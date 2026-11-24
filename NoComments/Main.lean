import NoComments.Core
import NoComments.Config
import NoComments.ConfigIO
import NoComments.LakeEnv
import NoComments.RatchetCore
import NoComments.Ratchet
import NoComments.Worker

open NoComments

private def toolVersion : String := "0.3.0"

private inductive CommandMode where
  | inventory (file? : Option String) (asJson : Bool)
  | check (file? : Option String) (baseRef? : Option String) (bootstrap : Bool)
  deriving Repr

private structure CliOptions where
  repo? : Option String := none
  config? : Option String := none
  jobs? : Option Nat := none
  mode? : Option CommandMode := none
  showHelp : Bool := false
  showVersion : Bool := false

private def usageText : String :=
  String.intercalate "\n" [
    "Usage:",
    "  no-comments inventory [<file>] [--file <file>] [--json] [--repo <dir>] [--config <path>] [--jobs <n>]",
    "  no-comments check [--file <file>] [--base-ref <ref>] [--bootstrap] [--repo <dir>] [--config <path>] [--jobs <n>]",
    "  no-comments [--version | --help]"
  ]

private def requireArgValue (flag val : String) : Except String String := do
  if val == "" || val.startsWith "-" then
    throw s!"invalid value '{val}' for {flag}"
  return val

private def parseArgs (args : List String) (st : CliOptions := {}) :
    Except String CliOptions := do
  match args with
  | [] =>
    if st.showHelp || st.showVersion then
      return st
    else if st.mode?.isNone then
      throw "missing subcommand (`inventory` or `check`); run with --help"
    else
      return st
  | "--help" :: rest | "-h" :: rest =>
    parseArgs rest { st with showHelp := true }
  | "--version" :: rest | "-V" :: rest =>
    parseArgs rest { st with showVersion := true }
  | "--repo" :: dir :: rest =>
    parseArgs rest { st with repo? := some (← requireArgValue "--repo" dir) }
  | ["--repo"] =>
    throw "missing directory after --repo"
  | "--config" :: path :: rest =>
    parseArgs rest { st with config? := some (← requireArgValue "--config" path) }
  | ["--config"] =>
    throw "missing path after --config"
  | "--jobs" :: nStr :: rest | "-j" :: nStr :: rest =>
    let some n := nStr.toNat?
      | throw s!"invalid integer '{nStr}' for --jobs"
    if n == 0 then throw "--jobs must be at least 1"
    parseArgs rest { st with jobs? := some n }
  | ["--jobs"] =>
    throw "missing integer after --jobs"
  | ["-j"] =>
    throw "missing integer after -j"
  | "--file" :: f :: rest =>
    match st.mode? with
    | some (.inventory none asJson) =>
      parseArgs rest { st with mode? := some (.inventory (some (← requireArgValue "--file" f)) asJson) }
    | some (.inventory (some _) _) =>
      throw s!"duplicate target file '{f}'"
    | some (.check none baseRef? bootstrap) =>
      parseArgs rest { st with mode? := some (.check (some (← requireArgValue "--file" f)) baseRef? bootstrap) }
    | some (.check (some _) _ _) =>
      throw s!"duplicate target file '{f}'"
    | none =>
      throw "--file must follow subcommand (`inventory` or `check`)"
  | ["--file"] =>
    match st.mode? with
    | none => throw "--file must follow subcommand (`inventory` or `check`)"
    | some _ => throw "missing path after --file"
  | "--json" :: rest =>
    match st.mode? with
    | some (.inventory file? _) =>
      parseArgs rest { st with mode? := some (.inventory file? true) }
    | some (.check ..) =>
      throw "--json is supported only with `inventory`"
    | none =>
      throw "--json must follow `inventory`"
  | "--base-ref" :: ref :: rest =>
    match st.mode? with
    | some (.check file? none bootstrap) =>
      parseArgs rest { st with mode? := some (.check file? (some (← requireArgValue "--base-ref" ref)) bootstrap) }
    | some (.check _ (some _) _) =>
      throw "duplicate --base-ref"
    | _ =>
      throw "--base-ref is supported only with `check` and requires a ref"
  | ["--base-ref"] =>
    throw "--base-ref is supported only with `check` and requires a ref"
  | "--bootstrap" :: rest =>
    match st.mode? with
    | some (.check file? baseRef? _) =>
      parseArgs rest { st with mode? := some (.check file? baseRef? true) }
    | _ =>
      throw "--bootstrap is supported only with `check`"
  | arg :: rest =>
    if arg.startsWith "--repo=" then
      parseArgs rest { st with repo? := some (← requireArgValue "--repo=" (arg.drop 7).toString) }
    else if arg.startsWith "--config=" then
      parseArgs rest { st with config? := some (← requireArgValue "--config=" (arg.drop 9).toString) }
    else if arg.startsWith "--jobs=" then
      let nStr := (arg.drop 7).toString
      let some n := nStr.toNat?
        | throw s!"invalid integer '{nStr}' for --jobs"
      if n == 0 then throw "--jobs must be at least 1"
      parseArgs rest { st with jobs? := some n }
    else if arg.startsWith "--file=" then
      let f ← requireArgValue "--file=" (arg.drop 7).toString
      match st.mode? with
      | some (.inventory none asJson) =>
        parseArgs rest { st with mode? := some (.inventory (some f) asJson) }
      | some (.inventory (some _) _) =>
        throw s!"duplicate target file '{f}'"
      | some (.check none baseRef? bootstrap) =>
        parseArgs rest { st with mode? := some (.check (some f) baseRef? bootstrap) }
      | some (.check (some _) _ _) =>
        throw s!"duplicate target file '{f}'"
      | none =>
        throw "--file must follow subcommand (`inventory` or `check`)"
    else if arg.startsWith "--base-ref=" then
      let ref ← requireArgValue "--base-ref=" (arg.drop 11).toString
      match st.mode? with
      | some (.check file? none bootstrap) =>
        parseArgs rest { st with mode? := some (.check file? (some ref) bootstrap) }
      | some (.check _ (some _) _) =>
        throw "duplicate --base-ref"
      | _ =>
        throw "--base-ref is supported only with `check`"
    else if arg == "inventory" && st.mode?.isNone then
      parseArgs rest { st with mode? := some (.inventory none false) }
    else if arg == "check" && st.mode?.isNone then
      parseArgs rest { st with mode? := some (.check none none false) }
    else if !arg.startsWith "-" then
      match st.mode? with
      | some (.inventory none asJson) =>
        parseArgs rest { st with mode? := some (.inventory (some arg) asJson) }
      | some (.inventory (some _) _) =>
        throw s!"unexpected extra positional argument '{arg}'"
      | _ =>
        throw s!"unexpected argument '{arg}'"
    else
      throw s!"unknown flag '{arg}'"

private def defaultJobs : Nat :=
  let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
  min (max 1 hw) 8

private def groupAndPrepareTargets (selfExe repoRoot : System.FilePath)
    (cfg : Config.RepoConfig) (classified : Array Config.ClassifiedFile)
    (targetFile? : Option String) (stageDir : System.FilePath) :
    IO (Array LakeEnv.WorkerTargetSetup × Array String × Array String) := do
  let mut checkedFiles : Array String := #[]
  let mut excludedFiles : Array String := #[]
  let mut perWs : Array (Array LakeEnv.SetupFileRequest) :=
    Array.replicate cfg.workspaces.size #[]
  let mut foundTarget := false
  for item in classified do
    match item with
    | .excluded rel rule =>
      excludedFiles := excludedFiles.push rel
      if targetFile? == some rel then
        throw <| IO.userError s!"file '{rel}' is excluded by config ({rule.reason})"
    | .checked rel wsIdx wsRel isTool =>
      checkedFiles := checkedFiles.push rel
      let includeIt := match targetFile? with
        | some t => t == rel
        | none => true
      if includeIt then
        if targetFile? == some rel then
          foundTarget := true
        perWs := perWs.modify wsIdx (·.push { relPath := rel, wsRelPath := wsRel, isTool })
  if let some t := targetFile? then
    unless foundTarget do
      throw <| IO.userError s!"target file '{t}' is not a tracked Lean file in {repoRoot}"
  let mut activeWorkspaces : Array (Nat × Config.WorkspaceConfig × Array LakeEnv.SetupFileRequest) := #[]
  for h : wsIdx in [:cfg.workspaces.size] do
    let reqs := perWs[wsIdx]!
    unless reqs.isEmpty do
      activeWorkspaces := activeWorkspaces.push (wsIdx, cfg.workspaces[wsIdx], reqs)
  let mut allTargets : Array LakeEnv.WorkerTargetSetup := #[]
  if activeWorkspaces.size <= 1 then
    for (wsIdx, wsCfg, reqs) in activeWorkspaces do
      let wsStageDir := stageDir / s!"ws-{wsIdx}"
      IO.FS.createDirAll wsStageDir
      let prepared ← LakeEnv.prepareWorkspaceTargets selfExe repoRoot wsCfg reqs wsStageDir
      allTargets := allTargets ++ prepared
  else
    let mut stagedWorkspaces := Array.emptyWithCapacity activeWorkspaces.size
    for (wsIdx, wsCfg, reqs) in activeWorkspaces do
      let wsStageDir := stageDir / s!"ws-{wsIdx}"
      IO.FS.createDirAll wsStageDir
      stagedWorkspaces := stagedWorkspaces.push (wsCfg, reqs, wsStageDir)
    let prepTasks ← stagedWorkspaces.mapM fun (wsCfg, reqs, wsStageDir) =>
      IO.asTask (LakeEnv.prepareWorkspaceTargets selfExe repoRoot wsCfg reqs wsStageDir)
        Task.Priority.dedicated
    let results ← (prepTasks.mapM IO.wait : BaseIO _)
    for res in results do
      let prepared ← IO.ofExcept res
      allTargets := allTargets ++ prepared
  return (allTargets, checkedFiles, excludedFiles)

private def formatRatchetJson (analyses : Array RatchetCore.FileAnalysis) : String :=
  let nonEmpty := (analyses.filter (!·.comments.isEmpty)).qsort (fun a b => a.file < b.file)
  if nonEmpty.isEmpty then
    "[]"
  else
    let entries := nonEmpty.map fun a =>
      let fps := a.fingerprints.values.map fun fp => s!"    {Lean.Json.compress (Lean.Json.str fp)}"
      let fpBlock := String.intercalate ",\n" fps.toList
      s!"  \{\"file\": {Lean.Json.compress (Lean.Json.str a.file)}, \"comments\": {a.comments.size}, \"lines\": {a.lines}, \"fingerprints\": [\n{fpBlock}\n  ]}"
    "[\n" ++ String.intercalate ",\n" entries.toList ++ "\n]"

private def printHumanInventory (analyses : Array RatchetCore.FileAnalysis)
    (checkedCount excludedCount : Nat) (singleFile? : Option String) : IO Unit := do
  let sorted := analyses.qsort (fun a b => a.file < b.file)
  let mut filesWithComments : Nat := 0
  let mut totalComments : Nat := 0
  let mut totalLines : Nat := 0
  for a in sorted do
    if !a.comments.isEmpty then
      filesWithComments := filesWithComments + 1
      totalComments := totalComments + a.comments.size
      totalLines := totalLines + a.lines
      IO.println s!"{a.file}: {a.comments.size} comment(s), {a.lines} line(s)"
      if singleFile?.isSome then
        for c in a.comments do
          IO.println s!"  {c.fingerprint} {c.kind} L{c.startLine}-L{c.endLine}"
    else if singleFile?.isSome then
      IO.println s!"{a.file}: 0 comment(s), 0 line(s)"
  if singleFile?.isNone then
    let exclNote := if excludedCount > 0 then s!" ({excludedCount} excluded)" else ""
    IO.println s!"{filesWithComments}/{checkedCount} files with comments, {totalComments} comment(s), {totalLines} line(s){exclNote}"

private def runUserCli (rawArgs : List String) : IO Unit := do
  let opts ← match parseArgs rawArgs with
    | .ok o => pure o
    | .error e => throw <| IO.userError s!"{e}\n\n{usageText}"
  if opts.showHelp then
    IO.println usageText
    return
  if opts.showVersion then
    IO.println s!"no-comments {toolVersion} (Lean {LakeEnv.compiledLeanVersion} {Lean.githash})"
    return
  let some mode := opts.mode?
    | throw <| IO.userError usageText
  let selfExe ← IO.appPath
  let repoArg := System.FilePath.mk (opts.repo?.getD ".")
  let repoRoot ← ConfigIO.verifyGitRoot repoArg
  let configPath := match opts.config? with
    | some p =>
      let fp := System.FilePath.mk p
      if fp.isAbsolute then fp else repoRoot / fp
    | none => repoRoot / ".no-comments.json"
  let cfg ← ConfigIO.loadConfig configPath
  let tracked ← ConfigIO.listTrackedLeanFiles repoRoot
  let classified ← match Config.classifyTrackedFiles cfg tracked with
    | .ok c => pure c
    | .error e => throw <| IO.userError s!"repository coverage check failed: {e}"
  let jobs := opts.jobs?.getD defaultJobs
  let stageDir ← IO.FS.createTempDir
  try
    match mode with
    | .inventory file? asJson =>
      let targetRel? ← file?.mapM (ConfigIO.resolveTargetFile repoRoot)
      let (targets, checkedFiles, excludedFiles) ←
        groupAndPrepareTargets selfExe repoRoot cfg classified targetRel? stageDir
      let analyses ← Worker.runWorkerPool selfExe stageDir targets jobs
      if asJson then
        IO.println (formatRatchetJson analyses)
      else
        printHumanInventory analyses checkedFiles.size excludedFiles.size targetRel?
    | .check file? baseRef? bootstrap =>
      let targetRel? ← file?.mapM (ConfigIO.resolveTargetFile repoRoot)
      let currentRatchet ← Ratchet.loadCurrentRatchet repoRoot cfg.ratchet
      let (baseSha, baseRatchet?) ←
        Ratchet.resolveBaseRatchet repoRoot cfg.ratchet baseRef? bootstrap
      let usedBootstrap := baseRatchet?.isNone
      let (targets, checkedFiles, excludedFiles) ←
        groupAndPrepareTargets selfExe repoRoot cfg classified targetRel? stageDir
      let analyses ← Worker.runWorkerPool selfExe stageDir targets jobs
      match RatchetCore.validateCheck analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetRel? with
      | .error e => throw <| IO.userError e
      | .ok () =>
        let totalComments := analyses.foldl (fun acc a => acc + a.comments.size) 0
        let totalLines := analyses.foldl (fun acc a => acc + a.lines) 0
        let shortSha := if baseSha.length > 12 then (baseSha.take 12).toString else baseSha
        let bootstrapNote := if usedBootstrap then s!" [bootstrap: no base ratchet at {shortSha}]" else ""
        let exclNote := if targetRel?.isNone && !excludedFiles.isEmpty then s!" ({excludedFiles.size} excluded)" else ""
        IO.println s!"ok: {analyses.size} file(s) checked{exclNote}, {totalComments} comment(s), {totalLines} line(s), merge-base {shortSha}{bootstrapNote}"
  finally
    if (← stageDir.pathExists) then
      IO.FS.removeDirAll stageDir

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--print-env"] =>
      LakeEnv.runPrintEnvMode
    | ["--workspace-setup"] =>
      LakeEnv.runWorkspaceSetupMode
    | ["--worker"] =>
      Worker.runWorkerMode
    | ["--worker-loop"] =>
      Worker.runWorkerLoopMode
    | _ =>
      runUserCli args
    return 0
  catch err =>
    IO.eprintln s!"error: {err}"
    return 1
