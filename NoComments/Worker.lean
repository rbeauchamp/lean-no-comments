import Lean
import Std.Sync.Mutex
import NoComments.Core
import NoComments.Runner
import NoComments.LakeEnv
import NoComments.RatchetCore

namespace NoComments.Worker

open NoComments

private def coreSource : String := include_str "Core.lean"
private def runnerSource : String := include_str "Runner.lean"

def runWorkerMode : IO Unit :=
  Runner.runWorkerMode

def runWorkerLoopMode : IO Unit :=
  Runner.runWorkerLoopMode

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

private structure TargetBatch where
  envKey : WorkerEnvKey
  items : Array (Nat × LakeEnv.WorkerTargetSetup)
  weight : Nat
  sortRelPath : String
  deriving Inhabited

private def targetBatchKey (envKey : WorkerEnvKey) (target : LakeEnv.WorkerTargetSetup) : String :=
  let impPart := match target.setup.imports? <|> target.directImports? with
    | some imps => (Lean.toJson imps).compress
    | none => s!"file:{target.relPath}"
  let envPart := (Lean.toJson #[
    Lean.toJson envKey.useSharedLean,
    Lean.toJson envKey.wsDir,
    Lean.toJson envKey.leanPath,
    Lean.toJson envKey.leanSrcPath,
    Lean.toJson envKey.leanSysroot,
    Lean.toJson envKey.sharedLibPath,
    Lean.toJson envKey.dynlibs,
    Lean.toJson (envKey.plugins.map fun (p, f?) => s!"{p}:{f?.getD ""}")
  ]).compress
  s!"{envPart}|{target.setup.isModule}|{(Lean.toJson target.setup.options).compress}|{(Lean.toJson target.setup.importArts).compress}|{impPart}"

private def targetWeight (target : LakeEnv.WorkerTargetSetup) : Nat :=
  let artWeight := target.setup.importArts.size
  let impWeight := match target.setup.imports? <|> target.directImports? with
    | some imps => imps.size
    | none => 0
  artWeight * 10 + impWeight

private def buildBatches (targets : Array LakeEnv.WorkerTargetSetup) (jobs : Nat) :
    Array TargetBatch := Id.run do
  let mut byKey : Std.HashMap String (WorkerEnvKey × Array (Nat × LakeEnv.WorkerTargetSetup)) := {}
  let mut keyOrder : Array String := #[]
  for h : idx in [:targets.size] do
    let target := targets[idx]
    let envKey := targetEnvKey target
    let k := targetBatchKey envKey target
    if let some (ek, existing) := byKey[k]? then
      byKey := byKey.insert k (ek, existing.push (idx, target))
    else
      keyOrder := keyOrder.push k
      byKey := byKey.insert k (envKey, #[(idx, target)])
  let workerCount := max 1 (min jobs targets.size)
  let maxBatchSize := max 4 ((targets.size + workerCount - 1) / workerCount)
  let mut batches : Array TargetBatch := #[]
  for k in keyOrder do
    let (envKey, grp) := byKey[k]!
    let baseWeight := targetWeight grp[0]!.2
    let mut start := 0
    while start < grp.size do
      let stop := min (start + maxBatchSize) grp.size
      let slice := grp.extract start stop
      batches := batches.push {
        envKey
        items := slice
        weight := baseWeight + slice.size
        sortRelPath := slice[0]!.2.relPath
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
  let stderrTask ← IO.asTask child.stderr.readToEnd
  return { child, stderrTask }

private def shutdownPersistentWorker (w : PersistentWorker) : IO (UInt32 × String) := do
  let (_, child) ← w.child.takeStdin
  let exitCode ← child.wait
  let stderr ← match w.stderrTask.get with
    | .ok s => pure s
    | .error _ => pure ""
  return (exitCode, stderr)

private def killAndShutdownPersistentWorker (w : PersistentWorker) : IO (UInt32 × String) := do
  let _ ← w.child.kill.toBaseIO
  let (_, child) ← w.child.takeStdin
  let exitCode ← child.wait
  let stderr ← match w.stderrTask.get with
    | .ok s => pure s
    | .error _ => pure ""
  return (exitCode, stderr)

private def shutdownWorkerQuietly (w? : Option PersistentWorker) : IO Unit := do
  if let some w := w? then
    let _ ← (shutdownPersistentWorker w).toBaseIO
    pure ()

private def runTargetOnWorker (w : PersistentWorker) (target : LakeEnv.WorkerTargetSetup)
    (stripLakePlugin : Bool) : IO (RatchetCore.FileAnalysis × PersistentWorker) := do
  let reqId := w.nextReqId
  let lreq : Runner.LoopRequest := {
    reqId
    request := toRunnerRequest target stripLakePlugin
  }
  w.child.stdin.putStr ((Lean.toJson lreq).compress ++ "\n")
  w.child.stdin.flush
  let rawLine ← w.child.stdout.getLine
  if rawLine.isEmpty then
    let (exitCode, stderr) ← shutdownPersistentWorker w
    throw <| IO.userError s!"worker failed on {target.relPath} (exit {exitCode}): {stderr.trimAscii.toString}"
  let line := rawLine.trimAscii.toString
  let resp : Runner.LoopResponse ← match Lean.Json.parse line >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e =>
      let (exitCode, stderr) ← killAndShutdownPersistentWorker w
      let errSuffix := if stderr.trimAscii.toString.isEmpty then "" else s!" (stderr: {stderr.trimAscii.toString})"
      throw <| IO.userError s!"malformed worker response for {target.relPath} (exit {exitCode}): {e}{errSuffix}"
  if resp.reqId != reqId || resp.relPath != target.relPath then
    let _ ← killAndShutdownPersistentWorker w
    throw <| IO.userError s!"mismatched worker response for {target.relPath}: got reqId={resp.reqId} relPath='{resp.relPath}'"
  unless resp.ok do
    let _ ← shutdownPersistentWorker w
    throw <| IO.userError s!"worker failed on {target.relPath}: {resp.error?.getD "unknown worker error"}"
  let comments ← match validateWireComments target.relPath resp.comments with
    | .ok cs => pure cs
    | .error e =>
      let _ ← killAndShutdownPersistentWorker w
      throw <| IO.userError e
  return (RatchetCore.analyzeComments target.relPath comments, { w with nextReqId := reqId + 1 })

private structure PoolState where
  nextBatchIdx : Nat
  results : Array (Option RatchetCore.FileAnalysis)
  firstError? : Option String

private def resolveEntryLean? (entryLeanTask? : Option (Task (Except IO.Error System.FilePath)))
    (useSharedLean : Bool) : IO (Option System.FilePath) := do
  if !useSharedLean then
    return none
  match entryLeanTask? with
  | some t => some <$> IO.ofExcept t.get
  | none => throw <| IO.userError "internal error: missing staged shared Lean runner"

private def runBatch (selfExe stageDir : System.FilePath)
    (entryLeanTask? : Option (Task (Except IO.Error System.FilePath))) (batch : TargetBatch)
    (poolMutex : Std.Mutex PoolState) : IO Unit := do
  let mut worker? : Option PersistentWorker := none
  let stripLakePlugin := !batch.envKey.useSharedLean
  try
    let entryLean? ← match ← (resolveEntryLean? entryLeanTask? batch.envKey.useSharedLean).toBaseIO with
      | .ok e? => pure e?
      | .error err =>
        poolMutex.atomically do
          modify fun (st : PoolState) =>
            if st.firstError?.isNone then { st with firstError? := some (toString err) }
            else st
        return
    for (origIdx, target) in batch.items do
      let aborted ← poolMutex.atomically do
        return (← get).firstError?.isSome
      if aborted then
        break
      let w ← match worker? with
        | some existing => pure existing
        | none =>
          let fresh ← spawnPersistentWorker selfExe stageDir entryLean? batch.envKey
          worker? := some fresh
          pure fresh
      match ← (runTargetOnWorker w target stripLakePlugin).toBaseIO with
      | .ok (analysis, w') =>
        worker? := some w'
        poolMutex.atomically do
          modify fun (st : PoolState) =>
            { st with results := st.results.set! origIdx (some analysis) }
      | .error err =>
        worker? := none
        poolMutex.atomically do
          modify fun (st : PoolState) =>
            if st.firstError?.isNone then { st with firstError? := some (toString err) }
            else st
        break
  finally
    shutdownWorkerQuietly worker?

def runWorkerPool (selfExe stageDir : System.FilePath) (targets : Array LakeEnv.WorkerTargetSetup)
    (jobs : Nat) : IO (Array RatchetCore.FileAnalysis) := do
  if jobs == 0 then
    throw <| IO.userError "--jobs must be at least 1"
  if targets.isEmpty then
    return #[]
  let sharedTarget? := targets.find? needsSharedLeanWorker
  let entryLeanTask? ← match sharedTarget? with
    | some t => some <$> IO.asTask (prepareSharedLeanRunner stageDir t.leanSysroot)
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
    let t ← IO.asTask (do
      let mut keepGoing := true
      while keepGoing do
        let picked? ← poolMutex.atomically do
          let st ← get
          if st.firstError?.isSome || st.nextBatchIdx >= batches.size then
            return none
          else
            let idx := st.nextBatchIdx
            set { st with nextBatchIdx := idx + 1 }
            return some idx
        match picked? with
        | none => keepGoing := false
        | some batchIdx =>
          runBatch selfExe stageDir entryLeanTask? batches[batchIdx]! poolMutex)
    tasks := tasks.push t
  for t in tasks do
    IO.ofExcept t.get
  if let some stask := entryLeanTask? then
    let _ := stask.get
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
