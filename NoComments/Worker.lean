import Lean
import Std.Sync.Mutex
import NoComments.Core
import NoComments.Runner
import NoComments.LakeEnv
import NoComments.Ratchet

namespace NoComments.Worker

open NoComments

private def coreSource : String := include_str "Core.lean"
private def runnerSource : String := include_str "Runner.lean"

def runWorkerMode : IO Unit :=
  Runner.runWorkerMode

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
  IO.FS.writeFile entryLean "import NoComments.Runner\n\ndef main : IO Unit := NoComments.Runner.runWorkerMode\n"
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

private def prependSearchPath (front rest : String) : String :=
  if rest == "" then front
  else front ++ String.singleton System.SearchPath.separator ++ rest

private def runSingleChildWorker (selfExe stageDir : System.FilePath) (entryLean? : Option System.FilePath)
    (target : LakeEnv.WorkerTargetSetup) : IO Ratchet.FileAnalysis := do
  let (cmd, args, leanPath, stdinPayload) :=
    match entryLean?, needsSharedLeanWorker target with
    | some entryLean, true =>
      ( leanExeForSysroot target.leanSysroot
      , #["--run", entryLean.toString]
      , prependSearchPath stageDir.toString target.leanPath
      , (Lean.toJson (toRunnerRequest target false)).compress )
    | _, _ =>
      ( selfExe.toString
      , #["--worker"]
      , target.leanPath
      , (Lean.toJson (toRunnerRequest target true)).compress )
  let child ← IO.Process.spawn {
    cmd
    args
    cwd := some (System.FilePath.mk target.wsDir)
    env := #[
      ("LEAN_PATH", some leanPath),
      ("LEAN_SRC_PATH", some target.leanSrcPath),
      ("LEAN_SYSROOT", some target.leanSysroot),
      (LakeEnv.sharedLibEnvVar, some target.sharedLibPath)
    ]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr stdinPayload
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let stdoutTask ← IO.asTask child.stdout.readToEnd
  let stderrTask ← IO.asTask child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdoutTask.get
  let stderr ← IO.ofExcept stderrTask.get
  if exitCode != 0 then
    throw <| IO.userError s!"worker failed on {target.relPath} (exit {exitCode}): {stderr.trimAscii.toString}"
  match parseWorkerStdout target.relPath stdout with
  | .ok comments => return Ratchet.analyzeComments target.relPath comments
  | .error e => throw <| IO.userError e

private structure PoolState where
  nextIdx : Nat
  results : Array (Option Ratchet.FileAnalysis)
  firstError? : Option String

def runWorkerPool (selfExe stageDir : System.FilePath) (targets : Array LakeEnv.WorkerTargetSetup)
    (jobs : Nat) : IO (Array Ratchet.FileAnalysis) := do
  if jobs == 0 then
    throw <| IO.userError "--jobs must be at least 1"
  if targets.isEmpty then
    return #[]
  let sharedTarget? := targets.find? needsSharedLeanWorker
  let entryLean? ← match sharedTarget? with
    | some t => some <$> prepareSharedLeanRunner stageDir t.leanSysroot
    | none => pure none
  let workerCount := min jobs targets.size
  let mutex ← Std.Mutex.new {
    nextIdx := 0
    results := Array.replicate targets.size none
    firstError? := none
    : PoolState
  }
  let mut tasks := Array.emptyWithCapacity workerCount
  for _ in [:workerCount] do
    let t ← IO.asTask (do
      let mut keepGoing := true
      while keepGoing do
        let picked? ← mutex.atomically do
          let st ← get
          if st.firstError?.isSome || st.nextIdx >= targets.size then
            return none
          else
            let idx := st.nextIdx
            set { st with nextIdx := idx + 1 }
            return some idx
        match picked? with
        | none => keepGoing := false
        | some idx =>
          let target := targets[idx]!
          match ← (runSingleChildWorker selfExe stageDir entryLean? target).toBaseIO with
          | .ok analysis =>
            mutex.atomically do
              let st ← get
              set { st with results := st.results.set! idx (some analysis) }
          | .error err =>
            mutex.atomically do
              let st ← get
              if st.firstError?.isNone then
                set { st with firstError? := some (toString err) }
            keepGoing := false)
    tasks := tasks.push t
  for t in tasks do
    IO.ofExcept t.get
  let finalSt ← mutex.atomically get
  if let some errMsg := finalSt.firstError? then
    throw <| IO.userError errMsg
  let mut out := Array.emptyWithCapacity targets.size
  for idx in [:targets.size] do
    match finalSt.results[idx]! with
    | some a => out := out.push a
    | none => throw <| IO.userError s!"missing worker result for {targets[idx]!.relPath}"
  return out

end NoComments.Worker
