import Lean
import Lake
import Lake.Load.Config
import Lake.Load.Manifest
import Lake.Load.Workspace
import NoComments.Config

namespace NoComments.LakeEnv

open NoComments

structure WorkspaceRuntimeEnv where
  wsDir : String
  srcDir : String
  lakeArgs : Array String
  leanPath : String
  leanSrcPath : String
  leanSysroot : String
  sharedLibPath : String
  pathEnv : String
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

structure SetupFileRequest where
  relPath : String
  wsRelPath : String
  isTool : Bool
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

structure WorkspaceSetupRequest where
  wsDir : String
  lakeArgs : Array String
  files : Array SetupFileRequest
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

structure SetupFileResult where
  relPath : String
  setup? : Option Lean.ModuleSetup
  deriving Lean.ToJson, Lean.FromJson

structure WorkerTargetSetup where
  relPath : String
  wsDir : String
  absFile : String
  isTool : Bool
  leanPath : String
  leanSrcPath : String
  leanSysroot : String
  sharedLibPath : String
  setup : Lean.ModuleSetup
  deriving Inhabited, Lean.ToJson, Lean.FromJson

def sharedLibEnvVar : String :=
  if System.Platform.isOSX then "DYLD_LIBRARY_PATH" else "LD_LIBRARY_PATH"

def compiledLeanVersion : String :=
  if Lean.version.specialDesc != "" then
    s!"{Lean.versionStringCore}-{Lean.version.specialDesc}"
  else
    Lean.versionStringCore

private def parseVersionCommit (out : String) : Except String (String × String) := do
  let line := (out.splitOn "\n").headD "" |>.trimAscii.toString
  let verMarker := "(version "
  let partsVer := line.splitOn verMarker
  if partsVer.length < 2 then
    throw s!"unexpected `lean --version` output: {line}"
  let afterVer := partsVer[1]!
  let ver := (afterVer.splitOn ",").headD "" |>.trimAscii.toString
  let commitMarker := "commit "
  let partsCommit := line.splitOn commitMarker
  if partsCommit.length < 2 then
    throw s!"missing commit hash in `lean --version` output: {line}"
  let afterCommit := partsCommit[1]!
  let hash := ((afterCommit.splitOn ",").headD "" |>.splitOn ")").headD "" |>.trimAscii.toString
  if ver == "" || hash == "" then
    throw s!"failed to parse version/commit from `lean --version`: {line}"
  return (ver, hash)

def checkWorkspaceToolchain (wsDir : System.FilePath) : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["--version"]
    cwd := some wsDir
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"`lean --version` failed in {wsDir}: {out.stderr.trimAscii.toString}"
  match parseVersionCommit out.stdout with
  | .error e => throw <| IO.userError s!"toolchain check failed in {wsDir}: {e}"
  | .ok (ver, hash) =>
    if ver != compiledLeanVersion || hash != Lean.githash then
      throw <| IO.userError
        s!"toolchain mismatch in {wsDir}: workspace has Lean {ver} ({hash}), expected Lean {compiledLeanVersion} ({Lean.githash})"

def runPrintEnvMode : IO Unit := do
  let leanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let leanSrcPath := (← IO.getEnv "LEAN_SRC_PATH").getD ""
  let leanSysroot := (← IO.getEnv "LEAN_SYSROOT").getD ""
  let sharedLibPath := (← IO.getEnv sharedLibEnvVar).getD ""
  let pathEnv := (← IO.getEnv "PATH").getD ""
  let payload := Lean.Json.mkObj [
    ("leanPath", Lean.Json.str leanPath),
    ("leanSrcPath", Lean.Json.str leanSrcPath),
    ("leanSysroot", Lean.Json.str leanSysroot),
    ("sharedLibPath", Lean.Json.str sharedLibPath),
    ("pathEnv", Lean.Json.str pathEnv)
  ]
  IO.println payload.compress

private def joinSearchPath (entries : Array String) : String :=
  let sep := String.singleton System.SearchPath.separator
  let cleaned := entries.filter (· != "")
  String.intercalate sep cleaned.toList

private def buildSharedLibPath (leanSysroot existing : String) : String :=
  if leanSysroot == "" then existing
  else
    let sys := System.FilePath.mk leanSysroot
    let leanLib := (sys / "lib" / "lean").toString
    let baseLib := (sys / "lib").toString
    joinSearchPath #[leanLib, baseLib, existing]

def queryWorkspaceEnv (selfExe : System.FilePath) (wsDir : System.FilePath)
    (srcDirRel : String) (lakeArgs : Array String) : IO WorkspaceRuntimeEnv := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := lakeArgs ++ #["env", selfExe.toString, "--print-env"]
    cwd := some wsDir
  }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"`lake {String.intercalate " " lakeArgs.toList} env` failed in {wsDir}: {out.stderr.trimAscii.toString}"
  let json ← match Lean.Json.parse out.stdout with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"failed to parse environment JSON from {wsDir}: {e}"
  let getField (k : String) : IO String := do
    match json.getObjValAs? String k with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"missing env field '{k}': {e}"
  let leanPath ← getField "leanPath"
  let leanSrcPath ← getField "leanSrcPath"
  let leanSysroot ← getField "leanSysroot"
  let rawShared ← getField "sharedLibPath"
  let pathEnv ← getField "pathEnv"
  let srcDir := if srcDirRel == "." then wsDir else wsDir / srcDirRel
  return {
    wsDir := wsDir.toString
    srcDir := srcDir.toString
    lakeArgs
    leanPath
    leanSrcPath
    leanSysroot
    sharedLibPath := buildSharedLibPath leanSysroot rawShared
    pathEnv
  }

private structure ParsedLakeFlags where
  relConfigFile : System.FilePath := Lake.defaultConfigFile
  wsDir : System.FilePath
  relPkgDir : System.FilePath := "."
  packageOverrides : Array Lake.PackageEntry := #[]
  lakeOpts : Lean.NameMap String := ∅
  reconfigure : Bool := false
  updateToolchain : Bool := true
  updateDeps : Bool := false
  oldMode : Bool := false
  trustHash : Bool := true
  failLv : Lake.LogLevel := .error
  noCache? : Option Bool := none

private def parseLakeFlags (initWsDir : System.FilePath) (lakeArgs : Array String) :
    IO ParsedLakeFlags := do
  let mut st : ParsedLakeFlags := { wsDir := initWsDir }
  let mut i : Nat := 0
  while h : i < lakeArgs.size do
    let arg := lakeArgs[i]
    if arg == "-f" || arg == "--file" then
      let nextIdx := i + 1
      if hNext : nextIdx < lakeArgs.size then
        st := { st with relConfigFile := lakeArgs[nextIdx] }
        i := nextIdx + 1
      else
        throw <| IO.userError s!"missing value after '{arg}' in lakeArgs"
    else if arg.startsWith "--file=" then
      st := { st with relConfigFile := (arg.drop 7).toString }
      i := i + 1
    else if arg == "-d" || arg == "--dir" then
      let nextIdx := i + 1
      if hNext : nextIdx < lakeArgs.size then
        st := { st with wsDir := st.wsDir / lakeArgs[nextIdx] }
        i := nextIdx + 1
      else
        throw <| IO.userError s!"missing value after '{arg}' in lakeArgs"
    else if arg.startsWith "--dir=" then
      st := { st with wsDir := st.wsDir / (arg.drop 6).toString }
      i := i + 1
    else if arg == "--packages" then
      let nextIdx := i + 1
      if hNext : nextIdx < lakeArgs.size then
        let rawPkgFile := lakeArgs[nextIdx]
        let pkgPath :=
          if (System.FilePath.mk rawPkgFile).isAbsolute then System.FilePath.mk rawPkgFile
          else st.wsDir / rawPkgFile
        let entries ← Lake.Manifest.loadEntries pkgPath
        st := { st with packageOverrides := st.packageOverrides ++ entries }
        i := nextIdx + 1
      else
        throw <| IO.userError s!"missing value after '{arg}' in lakeArgs"
    else if arg.startsWith "--packages=" then
      let rawPkgFile := (arg.drop 11).toString
      let pkgPath :=
        if (System.FilePath.mk rawPkgFile).isAbsolute then System.FilePath.mk rawPkgFile
        else st.wsDir / rawPkgFile
      let entries ← Lake.Manifest.loadEntries pkgPath
      st := { st with packageOverrides := st.packageOverrides ++ entries }
      i := i + 1
    else if arg == "-R" || arg == "--reconfigure" then
      st := { st with reconfigure := true }
      i := i + 1
    else if arg == "--offline" then
      st := { st with updateDeps := false, updateToolchain := false }
      i := i + 1
    else if arg == "--no-cache" then
      st := { st with noCache? := some true }
      i := i + 1
    else if arg == "--try-cache" then
      st := { st with noCache? := some false }
      i := i + 1
    else if arg == "--old" then
      st := { st with oldMode := true }
      i := i + 1
    else if arg == "--rehash" then
      st := { st with trustHash := false }
      i := i + 1
    else if arg == "--wfail" then
      st := { st with failLv := .warning }
      i := i + 1
    else if arg == "--iofail" then
      st := { st with failLv := .info }
      i := i + 1
    else if arg == "-q" || arg == "--quiet" || arg == "-v" || arg == "--verbose" then
      i := i + 1
    else if arg == "-K" then
      let nextIdx := i + 1
      if hNext : nextIdx < lakeArgs.size then
        let kv := lakeArgs[nextIdx]
        match kv.splitOn "=" with
        | [k, v] =>
          st := { st with lakeOpts := st.lakeOpts.insert (Lean.Name.mkSimple k) v }
        | _ =>
          throw <| IO.userError s!"invalid -K option '{kv}' in lakeArgs"
        i := nextIdx + 1
      else
        throw <| IO.userError "missing key=value after '-K' in lakeArgs"
    else if arg.startsWith "-K" && arg.length > 2 then
      let kv := (arg.drop 2).toString
      match kv.splitOn "=" with
      | [k, v] =>
        st := { st with lakeOpts := st.lakeOpts.insert (Lean.Name.mkSimple k) v }
      | _ =>
        throw <| IO.userError s!"invalid {arg} option in lakeArgs"
      i := i + 1
    else
      throw <| IO.userError s!"unsupported Lake CLI argument '{arg}' in lakeArgs"
  return st

def runWorkspaceSetupMode : IO Unit := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  let req : WorkspaceSetupRequest ← match Lean.Json.parse raw >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid workspace setup request: {e}"
  let wsDir := System.FilePath.mk req.wsDir
  let flags ← parseLakeFlags wsDir req.lakeArgs
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean?
    | throw <| IO.userError "failed to locate Lean installation inside Lake environment"
  let lake := match lake? with
    | some l =>
      if l.home == lean.sysroot && l.libDir != lean.leanLibDir then
        Lake.LakeInstall.ofLean lean
      else
        l
    | none => Lake.LakeInstall.ofLean lean
  let lakeEnv ← match ← (Lake.Env.compute lake lean elan? flags.noCache?).toBaseIO with
    | .ok env => pure env
    | .error e => throw <| IO.userError s!"Lake.Env.compute failed: {e}"
  let pkgDir := flags.wsDir / flags.relPkgDir
  let loadCfg : Lake.LoadConfig := {
    lakeEnv
    lakeArgs? := some req.lakeArgs
    wsDir := flags.wsDir
    relPkgDir := flags.relPkgDir
    pkgDir
    relConfigFile := flags.relConfigFile
    configFile := pkgDir / flags.relConfigFile
    packageOverrides := flags.packageOverrides
    lakeOpts := flags.lakeOpts
    reconfigure := flags.reconfigure
    updateDeps := flags.updateDeps
    updateToolchain := flags.updateToolchain
  }
  let (ws?, log) ← (Lake.loadWorkspace loadCfg).captureLog
  let some ws := ws?
    | throw <| IO.userError s!"failed to load Lake workspace in {flags.wsDir}:\n{log.toString}"
  let mut modPairs : Array (Nat × Lake.Module) := #[]
  let mut results : Array (Option Lean.ModuleSetup) := Array.replicate req.files.size none
  for h : idx in [:req.files.size] do
    let f := req.files[idx]
    if !f.isTool then
      let absFile := flags.wsDir / f.wsRelPath
      if let some mod := ws.findModuleBySrc? absFile then
        modPairs := modPairs.push (idx, mod)
  unless modPairs.isEmpty do
    let buildCfg : Lake.BuildConfig := {
      oldMode := flags.oldMode
      trustHash := flags.trustHash
      noBuild := true
      verbosity := .quiet
      failLv := flags.failLv
    }
    let setups ← ws.runBuild (do
      let jobs ← modPairs.mapM fun (_, mod) => mod.setup.fetch
      return Lake.Job.collectArray jobs) buildCfg
    for h : j in [:modPairs.size] do
      let (origIdx, _) := modPairs[j]
      results := results.set! origIdx (some setups[j]!)
  let out : Array SetupFileResult := Array.ofFn fun (i : Fin req.files.size) =>
    { relPath := req.files[i].relPath, setup? := results[i]! }
  IO.println (Lean.toJson out).compress

private def runWorkspaceSetupBatch (selfExe : System.FilePath) (wsEnv : WorkspaceRuntimeEnv)
    (files : Array SetupFileRequest) : IO (Std.HashMap String Lean.ModuleSetup) := do
  let req : WorkspaceSetupRequest := {
    wsDir := wsEnv.wsDir
    lakeArgs := wsEnv.lakeArgs
    files
  }
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := wsEnv.lakeArgs ++ #["env", selfExe.toString, "--workspace-setup"]
    cwd := some (System.FilePath.mk wsEnv.wsDir)
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.putStr (Lean.toJson req).compress
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let stdoutTask ← IO.asTask child.stdout.readToEnd
  let stderrTask ← IO.asTask child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdoutTask.get
  let stderr ← IO.ofExcept stderrTask.get
  if exitCode != 0 then
    throw <| IO.userError s!"workspace setup failed in {wsEnv.wsDir}: {stderr.trimAscii.toString}"
  let parsed : Array SetupFileResult ← match Lean.Json.parse stdout >>= Lean.fromJson? with
    | .ok arr => pure arr
    | .error e => throw <| IO.userError s!"invalid workspace setup JSON from {wsEnv.wsDir}: {e}"
  let mut map : Std.HashMap String Lean.ModuleSetup := {}
  for item in parsed do
    if let some s := item.setup? then
      map := map.insert item.relPath s
  return map

private def runLakeSetupFile (wsEnv : WorkspaceRuntimeEnv) (wsRelPath : String)
    (noBuild : Bool) : IO (Except String Lean.ModuleSetup) := do
  let flagArgs := if noBuild then #["--no-build"] else #[]
  let out ← IO.Process.output {
    cmd := "lake"
    args := wsEnv.lakeArgs ++ #["setup-file"] ++ flagArgs ++ #[wsRelPath]
    cwd := some (System.FilePath.mk wsEnv.wsDir)
  }
  if out.exitCode != 0 then
    return .error (out.stderr.trimAscii.toString)
  match Lean.Json.parse out.stdout >>= Lean.fromJson? with
  | .ok s => return .ok s
  | .error e => return .error s!"invalid `lake setup-file` JSON for {wsRelPath}: {e}"

private def builtinImportRoots : Array Lean.Name :=
  #[`Init, `Lean, `Std, `Lake]

private def isBuiltinImport (mod : Lean.Name) : Bool :=
  let root := mod.getRoot
  builtinImportRoots.contains root

private def oleanExistsInSearchPath (searchPath : System.SearchPath) (mod : Lean.Name) : IO Bool := do
  let relOlean := System.FilePath.mk ((mod.toString (escape := false) |>.replace "." "/") ++ ".olean")
  searchPath.anyM fun dir => (dir / relOlean).pathExists

private def parseHeaderImports (absFile : System.FilePath) : IO (Array Lean.Import) := do
  let content ← IO.FS.readFile absFile
  let inputCtx := Lean.Parser.mkInputContext content absFile.toString
  let (headerStx, _, msgs) ← Lean.Parser.parseHeader inputCtx
  if msgs.hasErrors then
    let errText ← msgs.toList.mapM (·.toString)
    throw <| IO.userError s!"failed to parse header of {absFile}:\n{String.intercalate "\n" errText}"
  return Lean.Elab.HeaderSyntax.imports ⟨headerStx⟩ (includeInit := true)

private def missingNonBuiltinImports (imports : Array Lean.Import)
    (importArts : Lean.NameMap Lean.ImportArtifacts) (searchPath : System.SearchPath) :
    IO (Array Lean.Name) := do
  let mut missing : Array Lean.Name := #[]
  for imp in imports do
    unless isBuiltinImport imp.module || importArts.contains imp.module do
      unless (← oleanExistsInSearchPath searchPath imp.module) do
        unless missing.contains imp.module do
          missing := missing.push imp.module
  return missing

private def findLocalToolSource? (srcRoots : Array System.FilePath) (mod : Lean.Name) :
    IO (Option (System.FilePath × System.FilePath)) := do
  let relLean := System.FilePath.mk (mod.toString (escape := false) |>.replace "." "/") |>.addExtension "lean"
  for root in srcRoots do
    let candidate := root / relLean
    if (← candidate.pathExists) then
      return some (root, relLean)
  return none

private partial def compileLocalToolHelper (mod : Lean.Name)
    (srcRoots : Array System.FilePath) (stageDir : System.FilePath)
    (importArts : Lean.NameMap Lean.ImportArtifacts) (leanPathEnv : String)
    (visiting compiled : Std.HashSet Lean.Name) :
    IO (Std.HashSet Lean.Name × Bool) := do
  if isBuiltinImport mod || compiled.contains mod then
    return (compiled, false)
  if visiting.contains mod then
    throw <| IO.userError s!"cyclic import detected while preparing tool imports at module '{mod}'"
  let searchPath := System.SearchPath.parse leanPathEnv
  if importArts.contains mod || (← oleanExistsInSearchPath searchPath mod) then
    return (compiled.insert mod, false)
  let some (foundRoot, relLean) ← findLocalToolSource? srcRoots mod
    | throw <| IO.userError s!"cannot locate compiled .olean or source file for tool import '{mod}'"
  let srcPath := foundRoot / relLean
  let imports ← parseHeaderImports srcPath
  let visiting' := visiting.insert mod
  let mut curCompiled := compiled
  for imp in imports do
    let (nextCompiled, _) ←
      compileLocalToolHelper imp.module srcRoots stageDir importArts leanPathEnv visiting' curCompiled
    curCompiled := nextCompiled
  let relOlean := System.FilePath.mk (mod.toString (escape := false) |>.replace "." "/") |>.addExtension "olean"
  let outOlean := stageDir / relOlean
  if let some parent := outOlean.parent then
    IO.FS.createDirAll parent
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["-o", outOlean.toString, relLean.toString]
    cwd := some foundRoot
    env := #[("LEAN_PATH", some leanPathEnv)]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"failed to compile tool import {mod} ({srcPath}): {out.stderr.trimAscii.toString}{out.stdout}"
  return (curCompiled.insert mod, true)

def prepareToolImports (wsEnv : WorkspaceRuntimeEnv) (wsRelPath : String)
    (stageDir : System.FilePath) : IO (Lean.ModuleSetup × String) := do
  let wsDir := System.FilePath.mk wsEnv.wsDir
  let srcDir := System.FilePath.mk wsEnv.srcDir
  let absFile := wsDir / wsRelPath
  let directImports ← parseHeaderImports absFile
  let searchPath := System.SearchPath.parse wsEnv.leanPath
  match ← runLakeSetupFile wsEnv wsRelPath true with
  | .ok setup =>
    let setupMissing ← missingNonBuiltinImports (setup.imports?.getD #[] ++ directImports) setup.importArts searchPath
    if setupMissing.isEmpty then
      return (setup, wsEnv.leanPath)
  | .error _ => pure ()
  let (setup?, firstErr?) ← match ← runLakeSetupFile wsEnv wsRelPath false with
    | .ok setup => pure (some setup, none)
    | .error err => pure (none, some err)
  let effectiveLeanPath := joinSearchPath #[stageDir.toString, wsEnv.leanPath]
  let effSearchPath := System.SearchPath.parse effectiveLeanPath
  let existingArts := match setup? with
    | some s => s.importArts
    | none => {}
  let checkImports := match setup? with
    | some s => s.imports?.getD #[] ++ directImports
    | none => directImports
  let wsMissing ← missingNonBuiltinImports checkImports existingArts searchPath
  if setup?.isNone && wsMissing.isEmpty then
    let errDetail := firstErr?.getD "missing tool imports"
    throw <| IO.userError s!"failed to prepare tool imports for {wsRelPath} in {wsEnv.wsDir}: {errDetail}"
  let stillMissing ← missingNonBuiltinImports checkImports existingArts effSearchPath
  unless stillMissing.isEmpty do
    let srcRoots := if srcDir == wsDir then #[wsDir] else #[srcDir, wsDir]
    let mut compiled : Std.HashSet Lean.Name := {}
    for mod in stillMissing do
      let (nextCompiled, _) ←
        compileLocalToolHelper mod srcRoots stageDir existingArts effectiveLeanPath {} compiled
      compiled := nextCompiled
  let outPath := if wsMissing.isEmpty then wsEnv.leanPath else effectiveLeanPath
  if let some setup := setup? then
    return (setup, outPath)
  let headerSetup : Lean.ModuleSetup := {
    name := Lean.Name.mkSimple wsRelPath
    imports? := some directImports
  }
  return (headerSetup, outPath)

def prepareWorkspaceTargets (selfExe : System.FilePath) (repoRoot : System.FilePath)
    (w : Config.WorkspaceConfig) (files : Array SetupFileRequest)
    (stageDir : System.FilePath) : IO (Array WorkerTargetSetup) := do
  if files.isEmpty then
    return #[]
  let wsDir := if w.dir == "." then repoRoot else repoRoot / w.dir
  checkWorkspaceToolchain wsDir
  let wsEnv ← queryWorkspaceEnv selfExe wsDir w.srcDir w.lakeArgs
  let nonToolReqs := files.filter (!·.isTool)
  let moduleSetups ←
    if nonToolReqs.isEmpty then pure ({} : Std.HashMap String Lean.ModuleSetup)
    else runWorkspaceSetupBatch selfExe wsEnv nonToolReqs
  let mut targets := Array.emptyWithCapacity files.size
  for f in files do
    let absFile := (wsDir / f.wsRelPath).toString
    if f.isTool then
      let (setup, effLeanPath) ← prepareToolImports wsEnv f.wsRelPath stageDir
      targets := targets.push {
        relPath := f.relPath
        wsDir := wsEnv.wsDir
        absFile
        isTool := true
        leanPath := effLeanPath
        leanSrcPath := wsEnv.leanSrcPath
        leanSysroot := wsEnv.leanSysroot
        sharedLibPath := wsEnv.sharedLibPath
        setup
      }
    else
      match moduleSetups[f.relPath]? with
      | some setup =>
        targets := targets.push {
          relPath := f.relPath
          wsDir := wsEnv.wsDir
          absFile
          isTool := false
          leanPath := wsEnv.leanPath
          leanSrcPath := wsEnv.leanSrcPath
          leanSysroot := wsEnv.leanSysroot
          sharedLibPath := wsEnv.sharedLibPath
          setup
        }
      | none =>
        match ← runLakeSetupFile wsEnv f.wsRelPath true with
        | .ok setup =>
          targets := targets.push {
            relPath := f.relPath
            wsDir := wsEnv.wsDir
            absFile
            isTool := false
            leanPath := wsEnv.leanPath
            leanSrcPath := wsEnv.leanSrcPath
            leanSysroot := wsEnv.leanSysroot
            sharedLibPath := wsEnv.sharedLibPath
            setup
          }
        | .error err =>
          throw <| IO.userError s!"failed to resolve Lake setup for '{f.relPath}' in {wsEnv.wsDir}: {err}"
  return targets

end NoComments.LakeEnv
