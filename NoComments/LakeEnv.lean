import Lean
import Lake
import Lake.CLI.Serve
import Lake.Load.Config
import Lake.Load.Manifest
import Lake.Load.Toml
import Lake.Load.Workspace
import NoComments.Config
import NoComments.Runner

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
  activeConfigFile? : Option String := none
  activeLakePkgDir? : Option String := none
  deriving Repr, Inhabited

instance : Lean.ToJson WorkspaceRuntimeEnv where
  toJson e :=
    let base : List (String × Lean.Json) := [
      ("wsDir", Lean.toJson e.wsDir),
      ("srcDir", Lean.toJson e.srcDir),
      ("lakeArgs", Lean.toJson e.lakeArgs),
      ("leanPath", Lean.toJson e.leanPath),
      ("leanSrcPath", Lean.toJson e.leanSrcPath),
      ("leanSysroot", Lean.toJson e.leanSysroot),
      ("sharedLibPath", Lean.toJson e.sharedLibPath),
      ("pathEnv", Lean.toJson e.pathEnv)
    ]
    let withCfg := match e.activeConfigFile? with
      | some c => ("activeConfigFile", Lean.toJson c) :: base
      | none => base
    let withPkg := match e.activeLakePkgDir? with
      | some d => ("activeLakePkgDir", Lean.toJson d) :: withCfg
      | none => withCfg
    Lean.Json.mkObj withPkg

instance : Lean.FromJson WorkspaceRuntimeEnv where
  fromJson? j := do
    let wsDir ← j.getObjValAs? String "wsDir"
    let srcDir ← j.getObjValAs? String "srcDir"
    let lakeArgs ← j.getObjValAs? (Array String) "lakeArgs"
    let leanPath ← j.getObjValAs? String "leanPath"
    let leanSrcPath ← j.getObjValAs? String "leanSrcPath"
    let leanSysroot ← j.getObjValAs? String "leanSysroot"
    let sharedLibPath ← j.getObjValAs? String "sharedLibPath"
    let pathEnv ← j.getObjValAs? String "pathEnv"
    let activeConfigFile? ← match ← Runner.getOptionalField j "activeConfigFile" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    let activeLakePkgDir? ← match ← Runner.getOptionalField j "activeLakePkgDir" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    return {
      wsDir, srcDir, lakeArgs, leanPath, leanSrcPath, leanSysroot, sharedLibPath, pathEnv,
      activeConfigFile?, activeLakePkgDir?
    }

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
  header? : Option Lean.ModuleHeader := none
  lakePkgDir? : Option String := none

instance : Lean.ToJson SetupFileResult where
  toJson r :=
    let base : List (String × Lean.Json) := [("relPath", Lean.toJson r.relPath)]
    let withSetup := match r.setup? with
      | some s => ("setup", Runner.moduleSetupToJson s) :: base
      | none => base
    let withHeader := match r.header? with
      | some h => ("header", Runner.moduleHeaderToJson h) :: withSetup
      | none => withSetup
    let withPkgDir := match r.lakePkgDir? with
      | some d => ("lakePkgDir", Lean.toJson d) :: withHeader
      | none => withHeader
    Lean.Json.mkObj withPkgDir

instance : Lean.FromJson SetupFileResult where
  fromJson? j := do
    let relPath ← j.getObjValAs? String "relPath"
    let setup? ← match ← Runner.getOptionalField j "setup" with
      | none => pure none
      | some v => some <$> Runner.moduleSetupFromJson? v
    let header? ← match ← Runner.getOptionalField j "header" with
      | none => pure none
      | some v => some <$> Runner.moduleHeaderFromJson? v
    let lakePkgDir? ← match ← Runner.getOptionalField j "lakePkgDir" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    return { relPath, setup?, header?, lakePkgDir? }

structure WorkspaceSetupResponse where
  leanPath : String
  leanSrcPath : String
  leanSysroot : String
  sharedLibPath : String
  pathEnv : String
  files : Array SetupFileResult
  activeConfigFile? : Option String := none
  activeLakePkgDir? : Option String := none

instance : Lean.ToJson WorkspaceSetupResponse where
  toJson r :=
    let base : List (String × Lean.Json) := [
      ("leanPath", Lean.toJson r.leanPath),
      ("leanSrcPath", Lean.toJson r.leanSrcPath),
      ("leanSysroot", Lean.toJson r.leanSysroot),
      ("sharedLibPath", Lean.toJson r.sharedLibPath),
      ("pathEnv", Lean.toJson r.pathEnv),
      ("files", Lean.toJson r.files)
    ]
    let withCfg := match r.activeConfigFile? with
      | some c => ("activeConfigFile", Lean.toJson c) :: base
      | none => base
    let withPkg := match r.activeLakePkgDir? with
      | some d => ("activeLakePkgDir", Lean.toJson d) :: withCfg
      | none => withCfg
    Lean.Json.mkObj withPkg

instance : Lean.FromJson WorkspaceSetupResponse where
  fromJson? j := do
    let leanPath ← j.getObjValAs? String "leanPath"
    let leanSrcPath ← j.getObjValAs? String "leanSrcPath"
    let leanSysroot ← j.getObjValAs? String "leanSysroot"
    let sharedLibPath ← j.getObjValAs? String "sharedLibPath"
    let pathEnv ← j.getObjValAs? String "pathEnv"
    let files ← j.getObjValAs? (Array SetupFileResult) "files"
    let activeConfigFile? ← match ← Runner.getOptionalField j "activeConfigFile" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    let activeLakePkgDir? ← match ← Runner.getOptionalField j "activeLakePkgDir" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    return {
      leanPath, leanSrcPath, leanSysroot, sharedLibPath, pathEnv, files,
      activeConfigFile?, activeLakePkgDir?
    }

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
  header? : Option Lean.ModuleHeader := none
  lakePkgDir? : Option String := none
  deriving Inhabited

instance : Lean.ToJson WorkerTargetSetup where
  toJson t :=
    let base : List (String × Lean.Json) := [
      ("relPath", Lean.toJson t.relPath),
      ("wsDir", Lean.toJson t.wsDir),
      ("absFile", Lean.toJson t.absFile),
      ("isTool", Lean.toJson t.isTool),
      ("leanPath", Lean.toJson t.leanPath),
      ("leanSrcPath", Lean.toJson t.leanSrcPath),
      ("leanSysroot", Lean.toJson t.leanSysroot),
      ("sharedLibPath", Lean.toJson t.sharedLibPath),
      ("setup", Runner.moduleSetupToJson t.setup)
    ]
    let withHeader := match t.header? with
      | some h => ("header", Runner.moduleHeaderToJson h) :: base
      | none => base
    let withPkgDir := match t.lakePkgDir? with
      | some d => ("lakePkgDir", Lean.toJson d) :: withHeader
      | none => withHeader
    Lean.Json.mkObj withPkgDir

instance : Lean.FromJson WorkerTargetSetup where
  fromJson? j := do
    let relPath ← j.getObjValAs? String "relPath"
    let wsDir ← j.getObjValAs? String "wsDir"
    let absFile ← j.getObjValAs? String "absFile"
    let isTool ← j.getObjValAs? Bool "isTool"
    let leanPath ← j.getObjValAs? String "leanPath"
    let leanSrcPath ← j.getObjValAs? String "leanSrcPath"
    let leanSysroot ← j.getObjValAs? String "leanSysroot"
    let sharedLibPath ← j.getObjValAs? String "sharedLibPath"
    let setup ← j.getObjVal? "setup" >>= Runner.moduleSetupFromJson?
    let header? ← match ← Runner.getOptionalField j "header" with
      | none => pure none
      | some v => some <$> Runner.moduleHeaderFromJson? v
    let lakePkgDir? ← match ← Runner.getOptionalField j "lakePkgDir" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    return {
      relPath, wsDir, absFile, isTool, leanPath, leanSrcPath, leanSysroot, sharedLibPath,
      setup, header?, lakePkgDir?
    }

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

private structure ParsedLakeFlags where
  relConfigFile : System.FilePath := Lake.defaultConfigFile
  rootDir? : Option String := none
  relPkgDir : System.FilePath := "."
  packageOverrideFiles : Array System.FilePath := #[]
  lakeOpts : Lean.NameMap String := ∅
  reconfigure : Bool := false
  updateToolchain : Bool := true
  updateDeps : Bool := false
  oldMode : Bool := false
  trustHash : Bool := true
  failLv : Lake.LogLevel := .error
  noCache? : Option Bool := none

private def resolveFromInitDir (initWsDir : System.FilePath) (raw : String) : System.FilePath :=
  let p := System.FilePath.mk raw
  if p.isAbsolute then p else initWsDir / p

private def isCommonLakeArgLongOpt : String → Bool
  | "--package" | "--service" | "--scope" | "--repo"
  | "--platform" | "--toolchain" | "--rev" | "--max-revs" | "--log-level"
  | "--fail-level" | "--linters" | "--lint-only" | "--checks" | "--only"
  | "--add-downstream" | "--add-public-downstream" | "--config" | "--from-export"
  | "--challenge-from-export" | "--solution-from-export" => true
  | _ => false

private def isCommonLakeFlagLongOpt : String → Bool
  | "--quiet" | "--verbose" | "--keep-toolchain" | "--reconfigure"
  | "--old" | "--text" | "--json" | "--allow-empty" | "--no-build" | "--fail-fast"
  | "--no-cache" | "--try-cache" | "--rehash" | "--offline" | "--wfail" | "--iofail"
  | "--no-overwrite" | "--force-overwrite" | "--force-download" | "--download-arts"
  | "--mappings-only" | "--ansi" | "--no-ansi" | "--builtin-lint"
  | "--builtin-only" | "--record-exceptions" | "--code-quality" | "--raw"
  | "--no-serve" | "--force" | "--keep-implied" | "--keep-prefix" | "--keep-public"
  | "--add-public" | "--gh-style" | "--explain" | "--trace" | "--fix"
  | "--paranoid" | "--inadvisably-no-sandbox" => true
  | _ => false

private def stripLeadingElanToolchain (lakeArgs : Array String) : List String :=
  match lakeArgs.toList with
  | arg :: rest => if arg.startsWith "+" && arg.length > 1 then rest else arg :: rest
  | [] => []

private abbrev LakeFlagsM := Lake.ArgsT (StateT ParsedLakeFlags (Except String))

private def takeLakeFlagArg (flag : String) : LakeFlagsM String := do
  let some val ← Lake.takeArg?
    | throw s!"missing value after '{flag}' in lakeArgs"
  return val

private def parseConfigOpt (kvPair : String) : Lean.Name × String :=
  let pos := kvPair.find '='
  if h : pos.IsAtEnd then
    (kvPair.toName, "")
  else
    ((kvPair.extract kvPair.startPos pos).toName, kvPair.extract (pos.next h) kvPair.endPos)

private def parseLakeFlagShort : Char → LakeFlagsM Unit
  | 'd' => do
    let dir ← takeLakeFlagArg "-d"
    modifyThe ParsedLakeFlags fun s => { s with rootDir? := some dir }
  | 'f' => do
    let cfg ← takeLakeFlagArg "-f"
    modifyThe ParsedLakeFlags fun s => { s with relConfigFile := cfg }
  | 'o' => do
    let _ ← takeLakeFlagArg "-o"
    pure ()
  | 'K' => do
    let kv ← takeLakeFlagArg "-K"
    let (k, v) := parseConfigOpt kv
    modifyThe ParsedLakeFlags fun s => { s with lakeOpts := s.lakeOpts.insert k v }
  | 'U' => modifyThe ParsedLakeFlags fun s => { s with updateDeps := true }
  | 'R' => modifyThe ParsedLakeFlags fun s => { s with reconfigure := true }
  | 'H' => modifyThe ParsedLakeFlags fun s => { s with trustHash := false }
  | 'q' | 'v' | 'J' => pure ()
  | opt => throw s!"unsupported Lake CLI argument '-{opt}' in lakeArgs"

private def parseLakeFlagLong (initWsDir : System.FilePath) (opt : String) : LakeFlagsM Unit :=
  match opt with
  | "--dir" => do
    let dir ← takeLakeFlagArg "--dir"
    modifyThe ParsedLakeFlags fun s => { s with rootDir? := some dir }
  | "--file" => do
    let cfg ← takeLakeFlagArg "--file"
    modifyThe ParsedLakeFlags fun s => { s with relConfigFile := cfg }
  | "--packages" => do
    let path ← takeLakeFlagArg "--packages"
    modifyThe ParsedLakeFlags fun s =>
      { s with packageOverrideFiles := s.packageOverrideFiles.push (resolveFromInitDir initWsDir path) }
  | "--reconfigure" => modifyThe ParsedLakeFlags fun s => { s with reconfigure := true }
  | "--update" => modifyThe ParsedLakeFlags fun s => { s with updateDeps := true }
  | "--keep-toolchain" => modifyThe ParsedLakeFlags fun s => { s with updateToolchain := false }
  | "--offline" => modifyThe ParsedLakeFlags fun s => { s with updateDeps := false, updateToolchain := false }
  | "--no-cache" => modifyThe ParsedLakeFlags fun s => { s with noCache? := some true }
  | "--try-cache" => modifyThe ParsedLakeFlags fun s => { s with noCache? := some false }
  | "--old" => modifyThe ParsedLakeFlags fun s => { s with oldMode := true }
  | "--rehash" => modifyThe ParsedLakeFlags fun s => { s with trustHash := false }
  | "--wfail" => modifyThe ParsedLakeFlags fun s => { s with failLv := .warning }
  | "--iofail" => modifyThe ParsedLakeFlags fun s => { s with failLv := .info }
  | "--fail-level" => do
    let raw ← takeLakeFlagArg "--fail-level"
    let some lv := Lake.LogLevel.ofString? raw
      | throw s!"invalid log level '{raw}' for '--fail-level' in lakeArgs"
    modifyThe ParsedLakeFlags fun s => { s with failLv := lv }
  | _ =>
    if isCommonLakeArgLongOpt opt then do
      let _ ← takeLakeFlagArg opt
      pure ()
    else if isCommonLakeFlagLongOpt opt then
      pure ()
    else
      throw s!"unsupported Lake CLI argument '{opt}' in lakeArgs"

private def parseLakeFlagOption (initWsDir : System.FilePath) : String → LakeFlagsM Unit :=
  Lake.option {
    short := parseLakeFlagShort
    long := parseLakeFlagLong initWsDir
    longShort := Lake.shortOptionWithArg parseLakeFlagShort
  }

private def parseLakeFlags (initWsDir : System.FilePath) (lakeArgs : Array String) :
    Except String ParsedLakeFlags := do
  let effectiveArgs := stripLeadingElanToolchain lakeArgs
  let (((), rem), flags) ←
    ((Lake.processLeadingOptions (parseLakeFlagOption initWsDir)).run effectiveArgs).run {}
  match rem with
  | [] => return flags
  | arg :: _ => throw s!"unsupported Lake CLI argument '{arg}' in lakeArgs"

private structure ResolvedWorkspaceLayout where
  wsDir : System.FilePath
  pkgDir : System.FilePath
  configFile : System.FilePath
  realCfg : System.FilePath

private def ResolvedWorkspaceLayout.activeConfigInfo (layout : ResolvedWorkspaceLayout) :
    Option String × Option String :=
  if layout.realCfg.toString.isEmpty then
    (none, none)
  else
    (some layout.realCfg.toString, some layout.pkgDir.toString)

private def resolveWorkspaceLayout (initWsDir : System.FilePath) (flags : ParsedLakeFlags) :
    IO ResolvedWorkspaceLayout := do
  let rawWsDir ← match flags.rootDir? with
    | some d =>
      if d.isEmpty then
        throw <| IO.userError "workspace directory does not exist: "
      else
        pure (resolveFromInitDir initWsDir d)
    | none => pure initWsDir
  let wsDir ← match ← Lake.resolvePath? rawWsDir with
    | some p => pure p
    | none => throw <| IO.userError s!"workspace directory does not exist: {rawWsDir}"
  let pkgDir := Lake.joinRelative wsDir flags.relPkgDir
  let configFile := Lake.joinRelative pkgDir flags.relConfigFile
  let realCfg ← Lake.realConfigFile configFile
  return { wsDir, pkgDir, configFile, realCfg }

private def resolveSourceFile (rawAbs : System.FilePath) : IO System.FilePath := do
  match ← Lake.resolvePath? rawAbs with
  | some p => pure p
  | none => pure rawAbs.normalize

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
  let flags ← match parseLakeFlags wsDir lakeArgs with
    | .ok f => pure f
    | .error e => throw <| IO.userError e
  let layout ← resolveWorkspaceLayout wsDir flags
  let (activeConfigFile?, activeLakePkgDir?) := layout.activeConfigInfo
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
    activeConfigFile?
    activeLakePkgDir?
  }

private abbrev LakeRootOptM := Lake.ArgsT (StateT (Option String) Option)

private def skipOptArg : LakeRootOptM Unit := do
  let some _ ← Lake.takeArg? | failure
  pure ()

private def parseRootDirShort : Char → LakeRootOptM Unit
  | 'd' => do
    let some dir ← Lake.takeArg? | failure
    set (some dir)
  | 'o' | 'K' => skipOptArg
  | 'q' | 'v' | 'R' | 'H' | 'J' => pure ()
  | _ => failure

private def parseRootDirLong (opt : String) : LakeRootOptM Unit :=
  match opt with
  | "--dir" => do
    let some dir ← Lake.takeArg? | failure
    set (some dir)
  | _ =>
    if isCommonLakeArgLongOpt opt then skipOptArg
    else if isCommonLakeFlagLongOpt opt then pure ()
    else failure

private def parseRootDirOption : String → LakeRootOptM Unit :=
  Lake.option {
    short := parseRootDirShort
    long := parseRootDirLong
    longShort := Lake.shortOptionWithArg parseRootDirShort
  }

private def isAbsentPath (path : System.FilePath) : BaseIO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | _ => return false

private def isUniqueRegularFile (path : System.FilePath) : BaseIO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok m => return m.type == .file && m.numLinks == 1
  | .error _ => return false

private def isAbsentOrUniqueFile (path : System.FilePath) : BaseIO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | .error _ => return false
  | .ok m => return m.type == .file && m.numLinks == 1

private def isAbsentOrRealDir (path : System.FilePath) : BaseIO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | .error _ => return false
  | .ok m => return m.type == .dir

private def isIsolatedPackagesDir (path : System.FilePath) : BaseIO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | .error _ => return false
  | .ok m =>
    unless m.type == .dir do
      return false
    match ← path.readDir.toBaseIO with
    | .error _ => return false
    | .ok entries =>
      for ent in entries do
        match ← ent.path.symlinkMetadata.toBaseIO with
        | .ok em =>
          match em.type with
          | .dir =>
            match ← (ent.path / ".git").symlinkMetadata.toBaseIO with
            | .error (.noFileOrDirectory ..) => pure ()
            | .error _ => return false
            | .ok gm =>
              match gm.type with
              | .dir => pure ()
              | .file => unless gm.numLinks == 1 do return false
              | .symlink | .other => return false
          | .file =>
            unless em.numLinks == 1 do
              return false
          | .symlink | .other => return false
        | .error _ => return false
      return true

private def isIsolatedConfigSubtree (path : System.FilePath) (allowMissing : Bool)
    (requireDir : Bool) : Nat → BaseIO Bool
  | 0 => return false
  | depth + 1 => do
    match ← path.symlinkMetadata.toBaseIO with
    | .error (.noFileOrDirectory ..) => return allowMissing
    | .error _ => return false
    | .ok m =>
      match m.type with
      | .file => return !requireDir && m.numLinks == 1
      | .dir =>
        match ← path.readDir.toBaseIO with
        | .error _ => return false
        | .ok entries =>
          for ent in entries do
            unless ← isIsolatedConfigSubtree ent.path false false depth do
              return false
          return true
      | .symlink | .other => return false

private def isSafeDepDirName (dirName : String) : Bool :=
  !dirName.isEmpty &&
  dirName != "." &&
  dirName != ".." &&
  !(System.FilePath.mk dirName).isAbsolute &&
  !dirName.any fun c => c == '/' || c == '\\' || System.FilePath.pathSeparators.contains c

private def isSafeRelativePath (p : System.FilePath) : Bool :=
  !p.isAbsolute &&
  !p.components.any (· == "..")

private def isSafeRelativeSubDir (subDir? : Option System.FilePath) : Bool :=
  match subDir? with
  | none => true
  | some sub => isSafeRelativePath sub

private def isDefaultTomlConfigFile (configFile : System.FilePath) : Bool :=
  !configFile.isAbsolute &&
  (configFile.normalize == Lake.defaultConfigFile.normalize ||
   configFile.normalize == Lake.defaultTomlConfigFile.normalize)

private def isDefaultManifestFile? (manifestFile? : Option System.FilePath) : Bool :=
  match manifestFile? with
  | none => true
  | some p => !p.isAbsolute && p.normalize == Lake.defaultManifestFile.normalize

private def hasDefaultTomlPath (table : Lake.Toml.Table) (key : Lean.Name)
    (expected : System.FilePath) : Bool :=
  match table.find? key with
  | none => true
  | some (.string _ s) =>
    let p := System.FilePath.mk s
    !p.isAbsolute && p.normalize == expected.normalize
  | some _ => false

private def hasDefaultTomlStoragePaths (table : Lake.Toml.Table) : Bool :=
  hasDefaultTomlPath table `packagesDir Lake.defaultPackagesDir &&
  hasDefaultTomlPath table `buildDir Lake.defaultBuildDir &&
  hasDefaultTomlPath table `manifestFile Lake.defaultManifestFile &&
  hasDefaultTomlPath table `leanLibDir Lake.defaultLeanLibDir &&
  hasDefaultTomlPath table `nativeLibDir Lake.defaultNativeLibDir &&
  hasDefaultTomlPath table `binDir Lake.defaultBinDir &&
  hasDefaultTomlPath table `irDir Lake.defaultIrDir &&
  hasDefaultTomlPath table `lakeDir Lake.defaultLakeDir

private def loadTomlTable? (tomlPath : System.FilePath) : BaseIO (Option Lake.Toml.Table) := do
  match ← (IO.FS.readFile tomlPath).toBaseIO with
  | .error _ => return none
  | .ok input =>
    let ictx := Lean.Parser.mkInputContext input tomlPath.toString
    match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok table => return some table
    | .error _ => return none

private def parseTomlRequires (table : Lake.Toml.Table) : Option (Array Lake.Dependency) :=
  match table.find? `require with
  | none => some #[]
  | some reqVal =>
    match EStateM.run (Lake.decodeToml (α := Array Lake.Dependency) reqVal) #[] with
    | .ok deps errs => if errs.isEmpty then some deps else none
    | .error _ _ => none

private def isIsolatedPathDep (depDir : System.FilePath) : Nat → BaseIO Bool
  | 0 => return false
  | depth + 1 => do
    match ← depDir.symlinkMetadata.toBaseIO with
    | .ok m =>
      unless m.type == .dir do
        return false
    | .error _ => return false
    unless ← isAbsentPath (depDir / Lake.defaultLeanConfigFile) do
      return false
    let tomlPath := depDir / Lake.defaultTomlConfigFile
    unless ← isUniqueRegularFile tomlPath do
      return false
    let some table ← loadTomlTable? tomlPath
      | return false
    let some deps := parseTomlRequires table
      | return false
    for dep in deps do
      unless isSafeDepDirName dep.dirName do
        return false
      match dep.src? with
      | some (.path dir copy) =>
        if copy then
          return false
        let some nextDir ← Lake.resolvePath? (depDir / dir)
          | return false
        unless ← isIsolatedPathDep nextDir depth do
          return false
      | some (.git _ _ subDir?) =>
        unless isSafeRelativeSubDir subDir? do
          return false
      | none => pure ()
    let manifestPath := depDir / Lake.defaultManifestFile
    match ← manifestPath.symlinkMetadata.toBaseIO with
    | .error (.noFileOrDirectory ..) => return true
    | .error _ => return false
    | .ok m =>
      unless m.type == .file && m.numLinks == 1 do
        return false
      match ← (Lake.Manifest.load manifestPath).toBaseIO with
      | .error _ => return false
      | .ok manifest =>
        for entry in manifest.packages do
          unless isSafeDepDirName entry.dirName do
            return false
          match entry.src with
          | .path dir copy =>
            if copy then
              return false
            unless isDefaultTomlConfigFile entry.configFile &&
                isDefaultManifestFile? entry.manifestFile? do
              return false
            let some nextDir ← Lake.resolvePath? (depDir / dir)
              | return false
            unless ← isIsolatedPathDep nextDir depth do
              return false
          | .git _ _ _ subDir? =>
            unless isSafeRelativeSubDir subDir? && isSafeRelativePath entry.configFile do
              return false
        return true

private def hasIsolatedManifest (realWsDir : System.FilePath) : BaseIO Bool := do
  let manifestPath := realWsDir / Lake.defaultManifestFile
  match ← manifestPath.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | .error _ => return false
  | .ok m =>
    unless m.type == .file && m.numLinks == 1 do
      return false
    match ← (Lake.Manifest.load manifestPath).toBaseIO with
    | .error _ => return false
    | .ok manifest =>
      unless !manifest.lakeDir.isAbsolute &&
          manifest.lakeDir.normalize == Lake.defaultLakeDir.normalize do
        return false
      match manifest.packagesDir? with
      | none => pure ()
      | some pkgsDir =>
        unless !pkgsDir.isAbsolute &&
            pkgsDir.normalize == Lake.defaultPackagesDir.normalize do
          return false
      for entry in manifest.packages do
        unless isSafeDepDirName entry.dirName do
          return false
        match entry.src with
        | .path dir copy =>
          if copy then
            return false
          unless isDefaultTomlConfigFile entry.configFile &&
              isDefaultManifestFile? entry.manifestFile? do
            return false
          let some depDir ← Lake.resolvePath? (realWsDir / dir)
            | return false
          unless ← isIsolatedPathDep depDir 16 do
            return false
        | .git _ _ _ subDir? =>
          unless isSafeRelativeSubDir subDir? && isSafeRelativePath entry.configFile do
            return false
      return true

private def hasIsolatedLakeState (realWsDir : System.FilePath) : BaseIO Bool := do
  match ← realWsDir.symlinkMetadata.toBaseIO with
  | .ok m =>
    unless m.type == .dir do
      return false
  | .error _ => return false
  unless ← isAbsentPath (realWsDir / Lake.defaultLeanConfigFile) do
    return false
  let tomlPath := realWsDir / Lake.defaultTomlConfigFile
  unless ← isUniqueRegularFile tomlPath do
    return false
  let some table ← loadTomlTable? tomlPath
    | return false
  unless hasDefaultTomlStoragePaths table do
    return false
  let some deps := parseTomlRequires table
    | return false
  for dep in deps do
    unless isSafeDepDirName dep.dirName do
      return false
    match dep.src? with
    | some (.path dir copy) =>
      if copy then
        return false
      let some depDir ← Lake.resolvePath? (realWsDir / dir)
        | return false
      unless ← isIsolatedPathDep depDir 16 do
        return false
    | some (.git _ _ subDir?) =>
      unless isSafeRelativeSubDir subDir? do
        return false
    | none => pure ()
  unless ← hasIsolatedManifest realWsDir do
    return false
  unless ← isAbsentOrUniqueFile (realWsDir / "lean-toolchain") do
    return false
  let lakeDir := realWsDir / Lake.defaultLakeDir
  match ← lakeDir.symlinkMetadata.toBaseIO with
  | .error (.noFileOrDirectory ..) => return true
  | .error _ => return false
  | .ok m =>
    unless m.type == .dir do
      return false
    unless ← isAbsentPath (lakeDir / "package-overrides.json") do
      return false
    unless ← isIsolatedConfigSubtree (lakeDir / "config") true true 32 do
      return false
    unless ← isIsolatedPackagesDir (lakeDir / "packages") do
      return false
    unless ← isAbsentOrRealDir (lakeDir / "build") do
      return false
    return true

private def isSegmentPrefix (prefixPath targetPath : System.FilePath) : Bool :=
  let pre := prefixPath.components.filter (!·.isEmpty)
  let tgt := targetPath.components.filter (!·.isEmpty)
  pre.length <= tgt.length && pre == tgt.take pre.length

def lakeStorageDisjoint (wsDirA wsDirB : System.FilePath) : Bool :=
  let lakeA := wsDirA / Lake.defaultLakeDir
  let lakeB := wsDirB / Lake.defaultLakeDir
  !(isSegmentPrefix lakeA wsDirB) && !(isSegmentPrefix lakeB wsDirA)

def resolveLakeLockKey? (repoRoot : System.FilePath) (w : Config.WorkspaceConfig) :
    IO (Option System.FilePath) := do
  let initWsDir := if w.dir == "." then repoRoot else repoRoot / w.dir
  let parsed? :=
    ((Lake.processLeadingOptions parseRootDirOption).run w.lakeArgs.toList).run none
  match parsed? with
  | some (((), []), rootDir?) =>
    let effectiveDir? := match rootDir? with
      | some d => if d.isEmpty then none else some (resolveFromInitDir initWsDir d)
      | none => some initWsDir
    let some effectiveDir := effectiveDir?
      | return none
    let some realWsDir ← Lake.resolvePath? effectiveDir
      | return none
    unless ← hasIsolatedLakeState realWsDir do
      return none
    return some realWsDir
  | _ => return none

def runWorkspaceSetupMode : IO Unit := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  let req : WorkspaceSetupRequest ← match Lean.Json.parse raw >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid workspace setup request: {e}"
  let reqWsDir := System.FilePath.mk req.wsDir
  let flags ← match parseLakeFlags reqWsDir req.lakeArgs with
    | .ok f => pure f
    | .error e => throw <| IO.userError e
  let layout ← resolveWorkspaceLayout reqWsDir flags
  let wsDir := layout.wsDir
  let pkgDir := layout.pkgDir
  let configFile := layout.configFile
  let realCfg := layout.realCfg
  let origWsDir ← match ← Lake.resolvePath? reqWsDir with
    | some p => pure p
    | none => pure wsDir
  let mut packageOverrides : Array Lake.PackageEntry := #[]
  for pkgPath in flags.packageOverrideFiles do
    let entries ← Lake.Manifest.loadEntries pkgPath
    packageOverrides := packageOverrides ++ entries
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
  let loadCfg : Lake.LoadConfig := {
    lakeEnv
    lakeArgs? := some (stripLeadingElanToolchain req.lakeArgs).toArray
    wsDir
    relPkgDir := flags.relPkgDir
    pkgDir
    relConfigFile := flags.relConfigFile
    configFile
    packageOverrides
    lakeOpts := flags.lakeOpts
    reconfigure := flags.reconfigure
    updateDeps := flags.updateDeps
    updateToolchain := flags.updateToolchain
  }
  let mut nonConfigFiles : Array (Nat × String × System.FilePath) := #[]
  let mut results : Array (Option Lean.ModuleSetup) := Array.replicate req.files.size none
  let mut headersArr : Array (Option Lean.ModuleHeader) := Array.replicate req.files.size none
  let mut lakePkgDirsArr : Array (Option String) := Array.replicate req.files.size none
  let mut hasNonTool := false
  for h : idx in [:req.files.size] do
    let f := req.files[idx]
    if !f.isTool then
      hasNonTool := true
      let rawAbs := origWsDir / f.wsRelPath
      let resolvedFile ← resolveSourceFile rawAbs
      if !realCfg.toString.isEmpty && resolvedFile == realCfg then
        let cfgSetup : Lean.ModuleSetup := {
          name := Lake.configModuleName
          plugins := #[lakeEnv.lake.sharedLib]
        }
        results := results.set! idx (some cfgSetup)
        lakePkgDirsArr := lakePkgDirsArr.set! idx (some pkgDir.toString)
      else
        nonConfigFiles := nonConfigFiles.push (idx, f.wsRelPath, resolvedFile)
  if hasNonTool && realCfg.toString.isEmpty then
    throw <| IO.userError s!"no Lake configuration file found in {wsDir}"
  unless nonConfigFiles.isEmpty do
    if let some errLog := (← IO.getEnv Lake.invalidConfigEnvVar) then
      let prefixMsg :=
        if errLog.isEmpty then ""
        else if errLog.endsWith "\n" then errLog
        else errLog ++ "\n"
      throw <| IO.userError
        s!"{prefixMsg}Failed to configure the Lake workspace. Please restart the server after fixing the error above."
    let (ws?, log) ← (Lake.loadWorkspace loadCfg).captureLog
    let some ws := ws?
      | throw <| IO.userError s!"failed to load Lake workspace in {wsDir}:\n{log.toString}"
    let mut modPairs : Array (Nat × Lake.Module) := #[]
    let mut extPairs : Array (Nat × String × System.FilePath) := #[]
    for (idx, wsRel, resolvedFile) in nonConfigFiles do
      if let some mod := ws.findModuleBySrc? resolvedFile then
        modPairs := modPairs.push (idx, mod)
      else
        extPairs := extPairs.push (idx, wsRel, resolvedFile)
    let buildCfg : Lake.BuildConfig := {
      oldMode := flags.oldMode
      trustHash := flags.trustHash
      noBuild := true
      verbosity := .quiet
      failLv := flags.failLv
    }
    let (modSetups, extSetups) ← ws.runBuild (do
      let modJobs ← modPairs.mapM fun (_, mod) => do
        let setupJob ← mod.setup.fetch
        let hdrJob ← mod.header.fetch
        return setupJob.zipWith (fun s h => ({ s with options := mod.serverOptions }, h)) hdrJob
      let extJobs ← extPairs.mapM fun (_, wsRel, resolvedPath) => do
        let content ← IO.FS.readFile resolvedPath
        let hdr ← Lean.parseImports' content wsRel
        let setupJob ← Lake.setupServerModule wsRel resolvedPath (some hdr)
        return setupJob.map (sync := true) fun s => (s, hdr)
      let allMods := Lake.Job.collectArray modJobs
      let allExts := Lake.Job.collectArray extJobs
      return allMods.zipWith (fun ms es => (ms, es)) allExts) buildCfg
    for h : j in [:modPairs.size] do
      let (origIdx, _) := modPairs[j]
      let (setup, hdr) := modSetups[j]!
      results := results.set! origIdx (some setup)
      headersArr := headersArr.set! origIdx (some hdr)
    for h : j in [:extPairs.size] do
      let (origIdx, _, _) := extPairs[j]
      let (setup, hdr) := extSetups[j]!
      results := results.set! origIdx (some setup)
      headersArr := headersArr.set! origIdx (some hdr)
  let outFiles : Array SetupFileResult := Array.ofFn fun (i : Fin req.files.size) =>
    { relPath := req.files[i].relPath
      setup? := results[i]!
      header? := headersArr[i]!
      lakePkgDir? := lakePkgDirsArr[i]! }
  let (activeConfigFile?, activeLakePkgDir?) := layout.activeConfigInfo
  let resp : WorkspaceSetupResponse := {
    leanPath := (← IO.getEnv "LEAN_PATH").getD ""
    leanSrcPath := (← IO.getEnv "LEAN_SRC_PATH").getD ""
    leanSysroot := (← IO.getEnv "LEAN_SYSROOT").getD ""
    sharedLibPath := (← IO.getEnv sharedLibEnvVar).getD ""
    pathEnv := (← IO.getEnv "PATH").getD ""
    files := outFiles
    activeConfigFile?
    activeLakePkgDir?
  }
  IO.println (Lean.toJson resp).compress

private def runWorkspaceSetupBatch (selfExe : System.FilePath) (wsDir : System.FilePath)
    (srcDirRel : String) (lakeArgs : Array String)
    (files : Array SetupFileRequest) :
    IO (WorkspaceRuntimeEnv × Std.HashMap String (Lean.ModuleSetup × Option Lean.ModuleHeader × Option String)) := do
  let req : WorkspaceSetupRequest := {
    wsDir := wsDir.toString
    lakeArgs
    files
  }
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := lakeArgs ++ #["env", selfExe.toString, "--workspace-setup"]
    cwd := some wsDir
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let writeRes ← (do
    child.stdin.putStr (Lean.toJson req).compress
    child.stdin.flush).toBaseIO
  let waitRes ← (do
    let (_, child) ← child.takeStdin
    child.wait).toBaseIO
  let stdoutRes ← IO.wait stdoutTask
  let stderrRes ← IO.wait stderrTask
  let exitCode ← IO.ofExcept waitRes
  if exitCode != 0 then
    let stderrMsg := match stderrRes with
      | .ok s => s.trimAscii.toString
      | .error e => toString e
    throw <| IO.userError s!"workspace setup failed in {wsDir}: {stderrMsg}"
  if let .error err := writeRes then
    throw <| IO.userError s!"failed to write workspace setup request in {wsDir}: {err}"
  let _ ← IO.ofExcept stderrRes
  let stdout ← IO.ofExcept stdoutRes
  let parsed : WorkspaceSetupResponse ← match Lean.Json.parse stdout >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid workspace setup JSON from {wsDir}: {e}"
  let srcDir := if srcDirRel == "." then wsDir else wsDir / srcDirRel
  let wsEnv : WorkspaceRuntimeEnv := {
    wsDir := wsDir.toString
    srcDir := srcDir.toString
    lakeArgs
    leanPath := parsed.leanPath
    leanSrcPath := parsed.leanSrcPath
    leanSysroot := parsed.leanSysroot
    sharedLibPath := buildSharedLibPath parsed.leanSysroot parsed.sharedLibPath
    pathEnv := parsed.pathEnv
    activeConfigFile? := parsed.activeConfigFile?
    activeLakePkgDir? := parsed.activeLakePkgDir?
  }
  let mut map : Std.HashMap String (Lean.ModuleSetup × Option Lean.ModuleHeader × Option String) := {}
  for item in parsed.files do
    if let some s := item.setup? then
      map := map.insert item.relPath (s, item.header?, item.lakePkgDir?)
  return (wsEnv, map)

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

private def parseModuleHeader (absFile : System.FilePath) : IO Lean.ModuleHeader := do
  let content ← IO.FS.readFile absFile
  let inputCtx := Lean.Parser.mkInputContext content absFile.toString
  let (headerStx, _, msgs) ← Lean.Parser.parseHeader inputCtx
  if msgs.hasErrors then
    let errText ← msgs.toList.mapM (·.toString)
    throw <| IO.userError s!"failed to parse header of {absFile}:\n{String.intercalate "\n" errText}"
  return Lean.Elab.HeaderSyntax.toModuleHeader ⟨headerStx⟩

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
  let header ← parseModuleHeader srcPath
  let visiting' := visiting.insert mod
  let mut curCompiled := compiled
  for imp in header.imports do
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
    (stageDir : System.FilePath) :
    IO (Lean.ModuleSetup × String × Lean.ModuleHeader) := do
  let wsDir := System.FilePath.mk wsEnv.wsDir
  let srcDir := System.FilePath.mk wsEnv.srcDir
  let absFile := wsDir / wsRelPath
  let header ← parseModuleHeader absFile
  let directImports := header.imports
  let searchPath := System.SearchPath.parse wsEnv.leanPath
  match ← runLakeSetupFile wsEnv wsRelPath true with
  | .ok setup =>
    let setupMissing ← missingNonBuiltinImports (setup.imports?.getD #[] ++ directImports) setup.importArts searchPath
    if setupMissing.isEmpty then
      return (setup, wsEnv.leanPath, header)
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
    return (setup, outPath, header)
  let headerSetup : Lean.ModuleSetup := {
    name := Lean.Name.mkSimple wsRelPath
    isModule := header.isModule
    imports? := some directImports
  }
  return (headerSetup, outPath, header)

private def activeLakePkgDirForFile (wsEnv : WorkspaceRuntimeEnv)
    (resolvedFile : System.FilePath) (setup : Lean.ModuleSetup) : Option String :=
  if setup.name == Lake.configModuleName then
    match wsEnv.activeConfigFile?, wsEnv.activeLakePkgDir? with
    | some cfgFile, some pkgDir =>
      if !cfgFile.isEmpty && !pkgDir.isEmpty && resolvedFile.toString == cfgFile then
        some pkgDir
      else
        none
    | _, _ => none
  else
    none

def prepareWorkspaceTargets (selfExe : System.FilePath) (repoRoot : System.FilePath)
    (w : Config.WorkspaceConfig) (files : Array SetupFileRequest)
    (stageDir : System.FilePath) : IO (Array WorkerTargetSetup) := do
  if files.isEmpty then
    return #[]
  let wsDir := if w.dir == "." then repoRoot else repoRoot / w.dir
  checkWorkspaceToolchain wsDir
  let nonToolReqs := files.filter (!·.isTool)
  let (wsEnv, moduleSetups) ←
    if nonToolReqs.isEmpty then
      let env ← queryWorkspaceEnv selfExe wsDir w.srcDir w.lakeArgs
      pure (env, ({} : Std.HashMap String (Lean.ModuleSetup × Option Lean.ModuleHeader × Option String)))
    else
      runWorkspaceSetupBatch selfExe wsDir w.srcDir w.lakeArgs nonToolReqs
  let mut targets := Array.emptyWithCapacity files.size
  for f in files do
    let resolvedFile ← resolveSourceFile (wsDir / f.wsRelPath)
    let absFile := resolvedFile.toString
    let (setup, effLeanPath, header?, batchLakePkgDir?) ←
      if f.isTool then
        let (setup, effLeanPath, header) ← prepareToolImports wsEnv f.wsRelPath stageDir
        pure (setup, effLeanPath, some header, none)
      else
        match moduleSetups[f.relPath]? with
        | some (setup, header?, lakePkgDir?) =>
          pure (setup, wsEnv.leanPath, header?, lakePkgDir?)
        | none =>
          match ← runLakeSetupFile wsEnv f.wsRelPath true with
          | .ok setup =>
            pure (setup, wsEnv.leanPath, none, none)
          | .error err =>
            throw <| IO.userError s!"failed to resolve Lake setup for '{f.relPath}' in {wsEnv.wsDir}: {err}"
    let lakePkgDir? :=
      match batchLakePkgDir? with
      | some d => if !d.isEmpty then some d else activeLakePkgDirForFile wsEnv resolvedFile setup
      | none => activeLakePkgDirForFile wsEnv resolvedFile setup
    targets := targets.push {
      relPath := f.relPath
      wsDir := wsEnv.wsDir
      absFile
      isTool := f.isTool
      leanPath := effLeanPath
      leanSrcPath := wsEnv.leanSrcPath
      leanSysroot := wsEnv.leanSysroot
      sharedLibPath := wsEnv.sharedLibPath
      setup
      header?
      lakePkgDir?
    }
  return targets

end NoComments.LakeEnv
