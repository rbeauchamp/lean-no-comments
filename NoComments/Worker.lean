import Lean
import Lake.DSL.Extensions
import Lake.Load.Lean.Elab
import Std.Sync.Mutex
import NoComments.Core
import NoComments.Runner
import NoComments.LakeEnv
import NoComments.RatchetCore

namespace NoComments.Worker

open NoComments

private def coreSource : String := include_str "Core.lean"
private def runnerSource : String := include_str "Runner.lean"

private def prepareLakeEnv (req : Runner.WorkerRequest) (mainModule : Lean.Name)
    (env : Lean.Environment) : Lean.Environment :=
  if mainModule == Lake.configModuleName then
    let pkgDir? := match req.lakePkgDir? with
      | some dir =>
        if dir.isEmpty then (System.FilePath.mk req.absFile).parent
        else some (System.FilePath.mk dir)
      | none => (System.FilePath.mk req.absFile).parent
    match pkgDir? with
    | some pkgDir => Lake.dirExt.setState env (some pkgDir)
    | none => env
  else
    env

def runWorkerMode : IO Unit :=
  Runner.runWorkerMode prepareLakeEnv

def runWorkerLoopMode : IO Unit :=
  Runner.runWorkerLoopMode prepareLakeEnv

private def needsSharedLeanWorker (target : LakeEnv.WorkerTargetSetup) : Bool :=
  !target.setup.dynlibs.isEmpty || target.setup.plugins.any (!Runner.isLakeSharedPlugin ·)

private def toRunnerRequest (target : LakeEnv.WorkerTargetSetup) (stripLakePlugin : Bool) :
    Runner.WorkerRequest := {
  relPath := target.relPath
  absFile := target.absFile
  leanPath := target.leanPath
  leanSysroot := target.leanSysroot
  setup := target.setup
  stripLakePlugin
  lakePkgDir? := target.lakePkgDir?
}

private def leanExeForSysroot (sysroot : String) : String :=
  if sysroot == "" then "lean"
  else (System.FilePath.mk sysroot / "bin" / "lean").toString

private def prepareSharedLeanRunner (stageDir : System.FilePath) (sysroot : String) : IO System.FilePath := do
  let modDir := stageDir / "NoComments"
  IO.FS.createDirAll modDir
  let coreLean := modDir / "Core.lean"
  let runnerLean := modDir / "Runner.lean"
  let entryLean := stageDir / "RunnerEntry.lean"
  IO.FS.writeFile coreLean coreSource
  IO.FS.writeFile runnerLean runnerSource
  IO.FS.writeFile entryLean "import NoComments.Runner\n\ndef main : IO Unit := NoComments.Runner.runWorkerLoopMode\n"
  let leanCmd := leanExeForSysroot sysroot
  let coreOut ← IO.Process.output {
    cmd := leanCmd
    args := #["-o", "NoComments/Core.olean", "NoComments/Core.lean"]
    cwd := some stageDir
  }
  if coreOut.exitCode != 0 then
    throw <| IO.userError s!"failed to stage NoComments.Core: {coreOut.stderr.trimAscii.toString}{coreOut.stdout}"
  let runnerOut ← IO.Process.output {
    cmd := leanCmd
    args := #["-o", "NoComments/Runner.olean", "NoComments/Runner.lean"]
    cwd := some stageDir
    env := #[("LEAN_PATH", some stageDir.toString)]
  }
  if runnerOut.exitCode != 0 then
    throw <| IO.userError s!"failed to stage NoComments.Runner: {runnerOut.stderr.trimAscii.toString}{runnerOut.stdout}"
  return entryLean

def parseWorkerStdout (file raw : String) : Except String (Array Core.Comment) := do
  let mut comments : Array Core.Comment := #[]
  for rawLine in raw.splitOn "\n" do
    let line := if rawLine.endsWith "\r" then (rawLine.dropEnd 1).toString else rawLine
    if line != "" then
      match line.splitOn " " with
      | [fp, kind, startStr, endStr] =>
        unless Core.isFingerprint fp do
          throw s!"malformed worker output for {file}: invalid fingerprint '{fp}'"
        unless Core.commentKinds.contains kind do
          throw s!"malformed worker output for {file}: invalid comment kind '{kind}'"
        let some startLine := startStr.toNat?
          | throw s!"malformed worker output for {file}: invalid startLine '{startStr}'"
        let some endLine := endStr.toNat?
          | throw s!"malformed worker output for {file}: invalid endLine '{endStr}'"
        if startLine == 0 || endLine < startLine then
          throw s!"malformed worker output for {file}: invalid line range {startLine}..{endLine}"
        comments := comments.push { kind, startLine, endLine, fingerprint := fp }
      | _ =>
        throw s!"malformed worker output line for {file}: '{line}'"
  return comments

private def validateWireComments (file : String) (raw : Array Runner.WireComment) :
    Except String (Array Core.Comment) := do
  let mut comments := Array.emptyWithCapacity raw.size
  for c in raw do
    unless Core.isFingerprint c.fingerprint do
      throw s!"malformed worker output for {file}: invalid fingerprint '{c.fingerprint}'"
    unless Core.commentKinds.contains c.kind do
      throw s!"malformed worker output for {file}: invalid comment kind '{c.kind}'"
    if c.startLine == 0 || c.endLine < c.startLine then
      throw s!"malformed worker output for {file}: invalid line range {c.startLine}..{c.endLine}"
    comments := comments.push {
      kind := c.kind
      startLine := c.startLine
      endLine := c.endLine
      fingerprint := c.fingerprint
    }
  return comments

private def prependSearchPath (front rest : String) : String :=
  if rest == "" then front
  else front ++ String.singleton System.SearchPath.separator ++ rest

private structure WorkerEnvKey where
  useSharedLean : Bool
  wsDir : String
  leanPath : String
  leanSrcPath : String
  leanSysroot : String
  sharedLibPath : String
  dynlibs : Array String
  plugins : Array (String × Option String)
  deriving BEq, Hashable, Inhabited

private def targetEnvKey (target : LakeEnv.WorkerTargetSetup) : WorkerEnvKey :=
  let useShared := needsSharedLeanWorker target
  let stripLake := !useShared
  let filteredPlugins :=
    if stripLake then target.setup.plugins.filter (!Runner.isLakeSharedPlugin ·)
    else target.setup.plugins
  {
    useSharedLean := useShared
    wsDir := target.wsDir
    leanPath := target.leanPath
    leanSrcPath := target.leanSrcPath
    leanSysroot := target.leanSysroot
    sharedLibPath := target.sharedLibPath
    dynlibs := target.setup.dynlibs.map (·.toString)
    plugins := filteredPlugins.map fun p => (p.path.toString, p.initFn?)
  }

private structure TargetGroup where
  envKey : WorkerEnvKey
  items : Array (Nat × LakeEnv.WorkerTargetSetup)
  hNonEmpty : 0 < items.size

private structure TargetBatch where
  envKey : WorkerEnvKey
  items : Array (Nat × LakeEnv.WorkerTargetSetup)
  hNonEmpty : 0 < items.size
  weight : Nat
  sortRelPath : String

private def targetBatchKey (envKey : WorkerEnvKey) (target : LakeEnv.WorkerTargetSetup) : String :=
  let effectiveImports? := target.setup.imports? <|> target.header?.map (·.imports)
  let effectiveIsModule? :=
    if target.setup.isModule then some true
    else target.header?.map (·.isModule)
  let keyJson := match effectiveImports?, effectiveIsModule? with
    | some imps, some isMod =>
      Lean.toJson #[
        Lean.toJson "batch",
        Lean.toJson envKey.useSharedLean,
        Lean.toJson envKey.wsDir,
        Lean.toJson envKey.leanPath,
        Lean.toJson envKey.leanSrcPath,
        Lean.toJson envKey.leanSysroot,
        Lean.toJson envKey.sharedLibPath,
        Lean.toJson envKey.dynlibs,
        Lean.toJson envKey.plugins,
        Lean.toJson isMod,
        Runner.leanOptionsToJson target.setup.options,
        Runner.nameMapToJson target.setup.importArts,
        Lean.Json.arr (imps.map Runner.importToJson)
      ]
    | _, _ =>
      Lean.toJson #[
        Lean.toJson "solo",
        Lean.toJson target.relPath
      ]
  keyJson.compress

private def targetWeight (target : LakeEnv.WorkerTargetSetup) : Nat :=
  let artWeight := target.setup.importArts.size
  let impWeight := match target.setup.imports? <|> target.header?.map (·.imports) with
    | some imps => imps.size
    | none => 0
  artWeight * 10 + impWeight

private def buildBatches (targets : Array LakeEnv.WorkerTargetSetup) (jobs : Nat) :
    Array TargetBatch := Id.run do
  let mut keyToGroup : Std.HashMap String Nat := {}
  let mut groups : Array TargetGroup := #[]
  for h : idx in [:targets.size] do
    let target := targets[idx]
    let envKey := targetEnvKey target
    let k := targetBatchKey envKey target
    if let some gIdx := keyToGroup[k]? then
      groups := groups.modify gIdx fun g => {
        g with
        items := g.items.push (idx, target)
        hNonEmpty := by
          rw [Array.size_push]
          exact Nat.succ_pos _
      }
    else
      keyToGroup := keyToGroup.insert k groups.size
      groups := groups.push {
        envKey
        items := #[(idx, target)]
        hNonEmpty := by simp
      }
  let workerCount := max 1 (min jobs targets.size)
  let maxBatchSize := max 4 ((targets.size + workerCount - 1) / workerCount)
  have hMaxPos : 0 < maxBatchSize := by
    change 0 < max 4 _
    omega
  let mut batches : Array TargetBatch := #[]
  for grp in groups do
    let baseWeight := targetWeight (grp.items[0]'grp.hNonEmpty).2
    let mut start := 0
    while hStart : start < grp.items.size do
      let stop := min (start + maxBatchSize) grp.items.size
      let slice := grp.items.extract start stop
      have hSlice : 0 < slice.size := by
        simp only [slice, Array.size_extract, stop]
        omega
      batches := batches.push {
        envKey := grp.envKey
        items := slice
        hNonEmpty := hSlice
        weight := baseWeight + slice.size
        sortRelPath := (slice[0]'hSlice).2.relPath
      }
      start := stop
  return batches.qsort fun a b =>
    if a.weight != b.weight then
      a.weight > b.weight
    else
      a.sortRelPath < b.sortRelPath

private structure PersistentWorker where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  stderrTask : Task (Except IO.Error String)
  nextReqId : Nat := 1

private def spawnPersistentWorker (selfExe stageDir : System.FilePath)
    (entryLean? : Option System.FilePath) (envKey : WorkerEnvKey) : IO PersistentWorker := do
  let (cmd, args, leanPath) :=
    match entryLean?, envKey.useSharedLean with
    | some entryLean, true =>
      ( leanExeForSysroot envKey.leanSysroot
      , #["--run", entryLean.toString]
      , prependSearchPath stageDir.toString envKey.leanPath )
    | _, _ =>
      ( selfExe.toString
      , #["--worker-loop"]
      , envKey.leanPath )
  let child ← IO.Process.spawn {
    cmd
    args
    cwd := some (System.FilePath.mk envKey.wsDir)
    env := #[
      ("LEAN_PATH", some leanPath),
      ("LEAN_SRC_PATH", some envKey.leanSrcPath),
      ("LEAN_SYSROOT", some envKey.leanSysroot),
      (LakeEnv.sharedLibEnvVar, some envKey.sharedLibPath)
    ]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  return { child, stderrTask }

private def shutdownPersistentWorker (w : PersistentWorker) : IO (UInt32 × String) := do
  let waitRes ← (do
    let (_, child) ← w.child.takeStdin
    child.wait).toBaseIO
  let stderrRes ← IO.wait w.stderrTask
  match waitRes, stderrRes with
  | .ok exitCode, .ok stderr => return (exitCode, stderr)
  | .error err, _ => throw err
  | .ok _, .error err => throw err

private def killAndShutdownPersistentWorker (w : PersistentWorker) : IO (UInt32 × String) := do
  let _ ← w.child.kill.toBaseIO
  let waitRes ← (do
    let (_, child) ← w.child.takeStdin
    child.wait).toBaseIO
  let stderrRes ← IO.wait w.stderrTask
  match waitRes with
  | .ok exitCode =>
    let stderr := match stderrRes with
      | .ok s => s
      | .error _ => ""
    return (exitCode, stderr)
  | .error err => throw err

private def formatStderrSuffix (stderr : String) : String :=
  let trimmed := stderr.trimAscii.toString
  if trimmed.isEmpty then "" else s!" (stderr: {trimmed})"

private inductive StepResult where
  | ok (analysis : RatchetCore.FileAnalysis) (worker : PersistentWorker)
  | failed (err : String)

private def runTargetOnWorker (w : PersistentWorker) (target : LakeEnv.WorkerTargetSetup)
    (stripLakePlugin : Bool) : BaseIO StepResult := do
  let reqId := w.nextReqId
  let lreq : Runner.LoopRequest := {
    reqId
    request := toRunnerRequest target stripLakePlugin
  }
  let rawLineRes ← (do
    w.child.stdin.putStr ((Lean.toJson lreq).compress ++ "\n")
    w.child.stdin.flush
    w.child.stdout.getLine).toBaseIO
  let rawLine ← match rawLineRes with
    | .ok line => pure line
    | .error e =>
      match ← (killAndShutdownPersistentWorker w).toBaseIO with
      | .ok (exitCode, stderr) =>
        return .failed s!"worker IPC failed on {target.relPath} (exit {exitCode}): {e}{formatStderrSuffix stderr}"
      | .error waitErr =>
        return .failed s!"worker IPC failed on {target.relPath}: {e} (wait failed: {waitErr})"
  if rawLine.isEmpty then
    match ← (shutdownPersistentWorker w).toBaseIO with
    | .ok (exitCode, stderr) =>
      return .failed s!"worker failed on {target.relPath} (exit {exitCode}): {stderr.trimAscii.toString}"
    | .error waitErr =>
      return .failed s!"worker failed on {target.relPath} (closed stdout; wait failed: {waitErr})"
  let line := rawLine.trimAscii.toString
  let resp : Runner.LoopResponse ← match Lean.Json.parse line >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e =>
      match ← (killAndShutdownPersistentWorker w).toBaseIO with
      | .ok (exitCode, stderr) =>
        return .failed s!"malformed worker response for {target.relPath} (exit {exitCode}): {e}{formatStderrSuffix stderr}"
      | .error waitErr =>
        return .failed s!"malformed worker response for {target.relPath}: {e} (wait failed: {waitErr})"
  if resp.reqId != reqId || resp.relPath != target.relPath then
    let _ ← (killAndShutdownPersistentWorker w).toBaseIO
    return .failed s!"mismatched worker response for {target.relPath}: got reqId={resp.reqId} relPath='{resp.relPath}'"
  unless resp.ok do
    let _ ← (shutdownPersistentWorker w).toBaseIO
    return .failed s!"worker failed on {target.relPath}: {resp.error?.getD "unknown worker error"}"
  match validateWireComments target.relPath resp.comments with
  | .ok comments =>
    return .ok (RatchetCore.analyzeComments target.relPath comments) { w with nextReqId := reqId + 1 }
  | .error e =>
    let _ ← (killAndShutdownPersistentWorker w).toBaseIO
    return .failed e

private structure PoolState where
  nextBatchIdx : Nat
  results : Array (Option RatchetCore.FileAnalysis)
  firstError? : Option String

private def recordFirstError (poolMutex : Std.Mutex PoolState) (errMsg : String) : BaseIO Unit :=
  poolMutex.atomically do
    modify fun (st : PoolState) =>
      if st.firstError?.isNone then { st with firstError? := some errMsg }
      else st

private def resolveEntryLean? (entryLeanTask? : Option (Task (Except IO.Error System.FilePath)))
    (useSharedLean : Bool) : IO (Option System.FilePath) := do
  if !useSharedLean then
    return none
  match entryLeanTask? with
  | some t => some <$> IO.ofExcept (← IO.wait t)
  | none => throw <| IO.userError "internal error: missing staged shared Lean runner"

private def runBatch (selfExe stageDir : System.FilePath)
    (entryLeanTask? : Option (Task (Except IO.Error System.FilePath))) (batch : TargetBatch)
    (poolMutex : Std.Mutex PoolState) : BaseIO Unit := do
  let abortedBeforeStart ← poolMutex.atomically do
    return (← get).firstError?.isSome
  if abortedBeforeStart then
    return
  let entryLean? ← match ← (resolveEntryLean? entryLeanTask? batch.envKey.useSharedLean).toBaseIO with
    | .ok e? => pure e?
    | .error err =>
      recordFirstError poolMutex (toString err)
      return
  let abortedBeforeSpawn ← poolMutex.atomically do
    return (← get).firstError?.isSome
  if abortedBeforeSpawn then
    return
  let initWorker ← match ← (spawnPersistentWorker selfExe stageDir entryLean? batch.envKey).toBaseIO with
    | .ok fresh => pure fresh
    | .error err =>
      recordFirstError poolMutex (toString err)
      return
  let stripLakePlugin := !batch.envKey.useSharedLean
  let rec loop (idx : Nat) (w : PersistentWorker)
      (acc : Array (Nat × RatchetCore.FileAnalysis)) : BaseIO Unit := do
    if h : idx < batch.items.size then
      let aborted ← poolMutex.atomically do
        return (← get).firstError?.isSome
      if aborted then
        let _ ← (shutdownPersistentWorker w).toBaseIO
        return
      let (origIdx, target) := batch.items[idx]
      match ← runTargetOnWorker w target stripLakePlugin with
      | .ok analysis w' =>
        loop (idx + 1) w' (acc.push (origIdx, analysis))
      | .failed err =>
        recordFirstError poolMutex err
    else
      match ← (shutdownPersistentWorker w).toBaseIO with
      | .ok (exitCode, stderr) =>
        if exitCode != 0 then
          recordFirstError poolMutex
            s!"worker exited with code {exitCode} after batch{formatStderrSuffix stderr}"
        else
          poolMutex.atomically do
            modify fun (st : PoolState) =>
              acc.foldl (init := st) fun s (origIdx, analysis) =>
                { s with results := s.results.set! origIdx (some analysis) }
      | .error err =>
        recordFirstError poolMutex s!"failed to shut down worker cleanly: {err}"
  termination_by batch.items.size - idx
  loop 0 initWorker (Array.emptyWithCapacity batch.items.size)

def runWorkerPool (selfExe stageDir : System.FilePath) (targets : Array LakeEnv.WorkerTargetSetup)
    (jobs : Nat) : IO (Array RatchetCore.FileAnalysis) := do
  if jobs == 0 then
    throw <| IO.userError "--jobs must be at least 1"
  if targets.isEmpty then
    return #[]
  let sharedTarget? := targets.find? needsSharedLeanWorker
  let entryLeanTask? ← match sharedTarget? with
    | some t => some <$> IO.asTask (prepareSharedLeanRunner stageDir t.leanSysroot) Task.Priority.dedicated
    | none => pure none
  let batches := buildBatches targets jobs
  let workerCount := min jobs batches.size
  let poolMutex ← Std.Mutex.new {
    nextBatchIdx := 0
    results := Array.replicate targets.size none
    firstError? := none
    : PoolState
  }
  let mut tasks := Array.emptyWithCapacity workerCount
  for _ in [:workerCount] do
    let t ← BaseIO.asTask (prio := .dedicated) (do
      let mut keepGoing := true
      while keepGoing do
        let picked? : Option (Fin batches.size) ← poolMutex.atomically do
          let st ← get
          if st.firstError?.isSome then
            return none
          else if h : st.nextBatchIdx < batches.size then
            let idx : Fin batches.size := ⟨st.nextBatchIdx, h⟩
            set { st with nextBatchIdx := st.nextBatchIdx + 1 }
            return some idx
          else
            return none
        match picked? with
        | none => keepGoing := false
        | some batchIdx =>
          runBatch selfExe stageDir entryLeanTask? batches[batchIdx] poolMutex)
    tasks := tasks.push t
  for t in tasks do
    IO.wait t
  if let some stask := entryLeanTask? then
    discard <| IO.wait stask
  let finalSt ← poolMutex.atomically get
  if let some errMsg := finalSt.firstError? then
    throw <| IO.userError errMsg
  let mut out := Array.emptyWithCapacity targets.size
  for idx in [:targets.size] do
    match finalSt.results[idx]! with
    | some a => out := out.push a
    | none => throw <| IO.userError s!"missing worker result for {targets[idx]!.relPath}"
  return out

end NoComments.Worker
