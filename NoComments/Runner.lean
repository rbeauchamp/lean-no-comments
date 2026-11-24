import Lean
import NoComments.Core

namespace NoComments.Runner

open NoComments

def nameToJson (n : Lean.Name) : Lean.Json :=
  let rec go : Lean.Name → List Lean.Json → List Lean.Json
    | .anonymous, acc => acc
    | .str pre s, acc => go pre (Lean.Json.str s :: acc)
    | .num pre k, acc => go pre (Lean.Json.num (Lean.JsonNumber.fromNat k) :: acc)
  Lean.Json.arr (go n []).toArray

def nameFromJson? : Lean.Json → Except String Lean.Name
  | .arr elems =>
    elems.foldlM (init := Lean.Name.anonymous) fun acc elem =>
      match elem with
      | .str s => pure (Lean.Name.str acc s)
      | .num ⟨Int.ofNat k, 0⟩ => pure (Lean.Name.num acc k)
      | other => throw s!"expected string or natural number name component, got '{other}'"
  | j@(.str _) => Lean.Name.fromJson? j
  | other => throw s!"expected structured `Name` array or string, got '{other}'"

def getOptionalField (j : Lean.Json) (key : String) : Except String (Option Lean.Json) :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | none => pure none
    | some .null => pure none
    | some v => pure (some v)
  | _ => throw "object expected"

private def getObjOptField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) (default : α) :
    Except String α :=
  match j with
  | .obj kvs =>
    match kvs.get? key with
    | none => pure default
    | some v => Lean.fromJson? v
  | _ => throw "object expected"

def importToJson (imp : Lean.Import) : Lean.Json :=
  Lean.Json.mkObj [
    ("module", nameToJson imp.module),
    ("importAll", Lean.toJson imp.importAll),
    ("isExported", Lean.toJson imp.isExported),
    ("isMeta", Lean.toJson imp.isMeta)
  ]

def importFromJson? (j : Lean.Json) : Except String Lean.Import := do
  let moduleJson ← j.getObjVal? "module"
  let module ← nameFromJson? moduleJson
  let importAll ← getObjOptField j "importAll" false
  let isExported ← getObjOptField j "isExported" true
  let isMeta ← getObjOptField j "isMeta" false
  return { module, importAll, isExported, isMeta }

def moduleHeaderToJson (hdr : Lean.ModuleHeader) : Lean.Json :=
  Lean.Json.mkObj [
    ("imports", Lean.Json.arr (hdr.imports.map importToJson)),
    ("isModule", Lean.toJson hdr.isModule)
  ]

def moduleHeaderFromJson? (j : Lean.Json) : Except String Lean.ModuleHeader := do
  let importsJson ← j.getObjVal? "imports"
  let importsArr ← importsJson.getArr?
  let imports ← importsArr.mapM importFromJson?
  let isModule ← j.getObjValAs? Bool "isModule"
  return { imports, isModule }

def nameMapToJson {α : Type} [Lean.ToJson α] (m : Lean.NameMap α) : Lean.Json :=
  let entries := m.foldl (init := #[]) fun acc k v => acc.push (k, v)
  let sorted := entries.qsort fun a b => Lean.Name.lt a.1 b.1
  Lean.Json.arr <| sorted.map fun (k, v) => Lean.Json.arr #[nameToJson k, Lean.toJson v]

def nameMapFromJson? {α : Type} [Lean.FromJson α] : Lean.Json → Except String (Lean.NameMap α)
  | .arr entries =>
    entries.foldlM (init := {}) fun m entry => do
      let pair ← entry.getArr?
      if h : pair.size = 2 then
        let k ← nameFromJson? pair[0]
        let v ← Lean.fromJson? pair[1]
        return m.insert k v
      else
        throw s!"expected [name, value] pair in NameMap, got '{entry}'"
  | j@(.obj _) => Lean.NameMap.fromJson? j
  | other => throw s!"expected `NameMap` array or object, got '{other}'"

def leanOptionsToJson (opts : Lean.LeanOptions) : Lean.Json :=
  nameMapToJson opts.values

def leanOptionsFromJson? (j : Lean.Json) : Except String Lean.LeanOptions :=
  Lean.LeanOptions.mk <$> nameMapFromJson? j

def moduleSetupToJson (s : Lean.ModuleSetup) : Lean.Json :=
  let base : List (String × Lean.Json) := [
    ("name", nameToJson s.name),
    ("isModule", Lean.toJson s.isModule),
    ("importArts", nameMapToJson s.importArts),
    ("dynlibs", Lean.toJson s.dynlibs),
    ("plugins", Lean.toJson s.plugins),
    ("options", leanOptionsToJson s.options)
  ]
  let withPkg := match s.package? with
    | some pkg => ("package", Lean.toJson pkg) :: base
    | none => base
  let withImports := match s.imports? with
    | some imps => ("imports", Lean.Json.arr (imps.map importToJson)) :: withPkg
    | none => withPkg
  Lean.Json.mkObj withImports

def moduleSetupFromJson? (j : Lean.Json) : Except String Lean.ModuleSetup := do
  let name ← j.getObjVal? "name" >>= nameFromJson?
  let package? : Option Lean.PkgId ← match ← getOptionalField j "package" with
    | none => pure none
    | some v => some <$> Lean.fromJson? v
  let isModule ← j.getObjValAs? Bool "isModule"
  let imports? ← match ← getOptionalField j "imports" with
    | none => pure none
    | some v =>
      let arr ← v.getArr?
      some <$> arr.mapM importFromJson?
  let importArts : Lean.NameMap Lean.ImportArtifacts ← j.getObjVal? "importArts" >>= nameMapFromJson?
  let dynlibs ← j.getObjValAs? (Array System.FilePath) "dynlibs"
  let plugins ← j.getObjValAs? (Array Lean.Plugin) "plugins"
  let options ← j.getObjVal? "options" >>= leanOptionsFromJson?
  return { name, package?, isModule, imports?, importArts, dynlibs, plugins, options }

structure WorkerRequest where
  relPath : String
  absFile : String
  leanPath : String
  leanSysroot : String
  setup : Lean.ModuleSetup
  stripLakePlugin : Bool := true
  lakePkgDir? : Option String := none
  deriving Inhabited

instance : Lean.ToJson WorkerRequest where
  toJson req :=
    let base : List (String × Lean.Json) := [
      ("relPath", Lean.toJson req.relPath),
      ("absFile", Lean.toJson req.absFile),
      ("leanPath", Lean.toJson req.leanPath),
      ("leanSysroot", Lean.toJson req.leanSysroot),
      ("setup", moduleSetupToJson req.setup),
      ("stripLakePlugin", Lean.toJson req.stripLakePlugin)
    ]
    let withPkgDir := match req.lakePkgDir? with
      | some d => ("lakePkgDir", Lean.toJson d) :: base
      | none => base
    Lean.Json.mkObj withPkgDir

instance : Lean.FromJson WorkerRequest where
  fromJson? j := do
    let relPath ← j.getObjValAs? String "relPath"
    let absFile ← j.getObjValAs? String "absFile"
    let leanPath ← j.getObjValAs? String "leanPath"
    let leanSysroot ← j.getObjValAs? String "leanSysroot"
    let setup ← j.getObjVal? "setup" >>= moduleSetupFromJson?
    let stripLakePlugin ← getObjOptField j "stripLakePlugin" true
    let lakePkgDir? ← match ← getOptionalField j "lakePkgDir" with
      | none => pure none
      | some v => some <$> Lean.fromJson? v
    return { relPath, absFile, leanPath, leanSysroot, setup, stripLakePlugin, lakePkgDir? }

structure LoopRequest where
  reqId : Nat
  request : WorkerRequest
  deriving Inhabited, Lean.ToJson, Lean.FromJson

structure WireComment where
  kind : String
  startLine : Nat
  endLine : Nat
  fingerprint : String
  deriving Inhabited, Lean.ToJson, Lean.FromJson

structure LoopResponse where
  reqId : Nat
  relPath : String
  ok : Bool
  comments : Array WireComment := #[]
  error? : Option String := none
  deriving Inhabited, Lean.ToJson, Lean.FromJson

private def formatErrors (msgs : Lean.MessageLog) : IO String := do
  let errMsgs := msgs.reportedPlusUnreported.toList.filter (·.severity == .error)
  let lines ← errMsgs.mapM fun m => m.toString
  return String.intercalate "\n" lines

private def mkParserCtx (inputCtx : Lean.Parser.InputContext) (cmdState : Lean.Elab.Command.State) :
    Lean.Parser.ParserContextCore :=
  let scope := cmdState.scopes.head!
  { toInputContext := inputCtx
    toParserModuleContext :=
      { env := cmdState.env
        options := scope.opts
        currNamespace := scope.currNamespace
        openDecls := scope.openDecls }
    toCacheableParserContext := { prec := 0 }
    tokens := Lean.Parser.getTokenTable cmdState.env }

private def appendErrorMessages (acc msgs : Lean.MessageLog) : Lean.MessageLog :=
  if msgs.hasErrors then acc ++ msgs else acc

private def collectSnapshotErrors
    (tasks : Array (Lean.Language.SnapshotTask Lean.Language.SnapshotTree))
    (acc : Lean.MessageLog) : Lean.MessageLog :=
  if tasks.isEmpty then acc
  else
    let tree := Lean.Language.SnapshotTree.mk { diagnostics := .empty } tasks
    tree.getAll.foldl (init := acc) fun logs snap =>
      appendErrorMessages logs snap.diagnostics.msgLog

private partial def collectFrontendCommands (inputCtx : Lean.Parser.InputContext)
    (acc : Array Core.CommandRange) (errMsgs : Lean.MessageLog) :
    Lean.Elab.Frontend.FrontendM (Array Core.CommandRange × Lean.MessageLog) := do
  let stBefore ← get
  let prevPos := stBefore.parserState.pos
  let pmCtx := mkParserCtx inputCtx stBefore.commandState
  let (_, _, parseMsgs) :=
    Lean.Parser.parseCommand inputCtx pmCtx.toParserModuleContext stBefore.parserState .empty
  let done ← Lean.Elab.Frontend.processCommand
  let stAfter ← get
  let nextPos := stAfter.parserState.pos
  let cmd := stAfter.commands.back?.getD .missing
  let acc := acc.push { ctx := pmCtx, prevPos, nextPos, stx := cmd }
  let errMsgs := appendErrorMessages errMsgs parseMsgs
  let errMsgs := appendErrorMessages errMsgs stAfter.commandState.messages
  let errMsgs := collectSnapshotErrors stAfter.commandState.snapshotTasks errMsgs
  unless stAfter.commandState.snapshotTasks.isEmpty do
    modify fun s => { s with commandState := { s.commandState with snapshotTasks := #[] } }
  if done then
    return (acc, errMsgs)
  else
    collectFrontendCommands inputCtx acc errMsgs

private def applyWorkerOptionOverrides (base : Lean.Options) : Lean.Options :=
  let o1 := base.setBool `Elab.async false
  let o2 := o1.setBool `debug.byAsSorry true
  let o3 := o2.setBool `warningAsError false
  o3.setBool `linter.all false

def isLakeSharedPlugin (p : Lean.Plugin) : Bool :=
  (p.path.fileName.getD "").startsWith "libLake_shared"

private unsafe def enableInitializersImpl : IO Unit :=
  Lean.enableInitializersExecution

@[implemented_by enableInitializersImpl]
private def enableInitializers : IO Unit := pure ()

private structure HeaderCacheKey where
  leanSysroot : String
  leanPath : String
  dynlibs : Array String
  plugins : Array (String × Option String)
  isModule : Bool
  inServer : Bool
  imports : Array Lean.Import
  optionsJson : String
  importArtsJson : String
  deriving BEq

private inductive WorkerBinding where
  | oneShot
  | unbound
  | bound (key : HeaderCacheKey) (env : Lean.Environment)

private def loadBaseEnv (req : WorkerRequest) (inputCtx : Lean.Parser.InputContext)
    (headerPos : String.Pos.Raw) (headerMsgs : Lean.MessageLog)
    (imports : Array Lean.Import) (isModule : Bool) (opts : Lean.Options)
    (filteredPlugins : Array Lean.Plugin) (cacheKey : HeaderCacheKey)
    (binding : WorkerBinding) :
    IO (Lean.Environment × Lean.MessageLog × WorkerBinding) := do
  let persistEnv ← match binding with
    | .bound boundKey env =>
      if boundKey != cacheKey then
        throw <| IO.userError s!"worker process is bound to a different import header/environment; refusing to reuse worker for {req.relPath}"
      return (env, headerMsgs, binding)
    | .unbound => pure true
    | .oneShot => pure false
  let sysroot ←
    if req.leanSysroot != "" then pure (System.FilePath.mk req.leanSysroot)
    else Lean.findSysroot
  Lean.initSearchPath sysroot (System.SearchPath.parse req.leanPath)
  let mut loadedDynlibs : Std.HashSet String := {}
  for dynlib in req.setup.dynlibs do
    let key := dynlib.toString
    unless loadedDynlibs.contains key do
      Lean.loadDynlib dynlib
      loadedDynlibs := loadedDynlibs.insert key
  let level : Lean.OLeanLevel :=
    if isModule then
      if Lean.Elab.inServer.get opts then .server else .exported
    else
      .private
  enableInitializers
  try
    let env ← Lean.importModules (leakEnv := persistEnv) (loadExts := true) (level := level)
      imports opts 0 filteredPlugins req.setup.importArts
    let nextBinding := if persistEnv then .bound cacheKey env else .oneShot
    return (env, headerMsgs, nextBinding)
  catch e =>
    let env ← Lean.mkEmptyEnvironment
    let pos := inputCtx.fileMap.toPosition headerPos
    let msgs := headerMsgs.add { fileName := inputCtx.fileName, data := toString e, pos }
    return (env, msgs, binding)

private def analyzeTargetWithState
    (prepareEnv : WorkerRequest → Lean.Name → Lean.Environment → Lean.Environment)
    (req : WorkerRequest) (binding : WorkerBinding) :
    IO (Array Core.Comment × WorkerBinding) := do
  let content ← IO.FS.readFile (System.FilePath.mk req.absFile)
  let inputCtx := Lean.Parser.mkInputContext content req.absFile
  let (headerStx, headerParserState, headerMsgs) ← Lean.Parser.parseHeader inputCtx
  if headerMsgs.hasErrors then
    let errText ← formatErrors headerMsgs
    throw <| IO.userError s!"parse error in header of {req.relPath}:\n{errText}"
  let opts := applyWorkerOptionOverrides req.setup.options.toOptions
  let headerSyntax : Lean.Elab.HeaderSyntax := ⟨headerStx⟩
  let imports := req.setup.imports?.getD (headerSyntax.imports (includeInit := true))
  let isModule := headerSyntax.isModule || req.setup.isModule
  let mainModule :=
    if req.setup.name == .anonymous then Lean.Name.mkSimple req.relPath
    else req.setup.name
  let filteredPlugins :=
    if req.stripLakePlugin then req.setup.plugins.filter (!isLakeSharedPlugin ·)
    else req.setup.plugins
  let cacheKey : HeaderCacheKey := {
    leanSysroot := req.leanSysroot
    leanPath := req.leanPath
    dynlibs := req.setup.dynlibs.map (·.toString)
    plugins := filteredPlugins.map fun p => (p.path.toString, p.initFn?)
    isModule
    inServer := Lean.Elab.inServer.get opts
    imports
    optionsJson := (leanOptionsToJson req.setup.options).compress
    importArtsJson := (nameMapToJson req.setup.importArts).compress
  }
  let (baseEnv, hdrMsgs0, nextBinding) ←
    loadBaseEnv req inputCtx headerParserState.pos headerMsgs imports isModule opts
      filteredPlugins cacheKey binding
  let env := baseEnv.setMainModule mainModule |>.setModulePackage req.setup.package?
  let hdrMsgs := Lean.Elab.checkDeprecatedImports env imports opts inputCtx headerParserState.pos
    hdrMsgs0 (some headerSyntax) (some headerSyntax)
  let hdrMsgs := Lean.Elab.checkModuleNamePortability mainModule inputCtx headerParserState.pos hdrMsgs
  if hdrMsgs.hasErrors then
    let errText ← formatErrors hdrMsgs
    throw <| IO.userError s!"import/header elaboration error in {req.relPath}:\n{errText}"
  let env := prepareEnv req mainModule env
  let cmdState := Lean.Elab.Command.mkState env hdrMsgs opts
  let hdrCtx := mkParserCtx inputCtx cmdState
  let initialRange : Core.CommandRange := {
    ctx := hdrCtx
    prevPos := 0
    nextPos := headerParserState.pos
    stx := headerStx
  }
  let initFrontendState : Lean.Elab.Frontend.State := {
    commandState := cmdState
    parserState := headerParserState
    cmdPos := headerParserState.pos
  }
  let ((cmdRanges, cmdErrMsgs), finalState) ←
    ((collectFrontendCommands inputCtx #[initialRange] {}).run { inputCtx }).run initFrontendState
  if cmdErrMsgs.hasErrors then
    let errText ← formatErrors cmdErrMsgs
    throw <| IO.userError s!"elaboration error in {req.relPath}:\n{errText}"
  let finalPos := finalState.parserState.pos
  let allRanges :=
    if finalPos < inputCtx.endPos then
      cmdRanges.push {
        ctx := mkParserCtx inputCtx finalState.commandState
        prevPos := finalPos
        nextPos := inputCtx.endPos
        stx := .missing
      }
    else
      cmdRanges
  match Core.collectRanges allRanges.toList {} with
  | .error e => throw <| IO.userError s!"comment audit error in {req.relPath}: {e}"
  | .ok acc =>
    return (Core.sourceOrder acc, nextBinding)

def analyzeTarget (req : WorkerRequest)
    (prepareEnv : WorkerRequest → Lean.Name → Lean.Environment → Lean.Environment := fun _ _ env => env) :
    IO (Array Core.Comment) := do
  let (comments, _) ← analyzeTargetWithState prepareEnv req .oneShot
  return comments

def runWorkerMode
    (prepareEnv : WorkerRequest → Lean.Name → Lean.Environment → Lean.Environment := fun _ _ env => env) :
    IO Unit := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  let req : WorkerRequest ← match Lean.Json.parse raw >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid worker request JSON: {e}"
  let comments ← analyzeTarget req prepareEnv
  for c in comments do
    IO.println s!"{c.fingerprint} {c.kind} {c.startLine} {c.endLine}"

private def toWireComments (comments : Array Core.Comment) : Array WireComment :=
  comments.map fun c => {
    kind := c.kind
    startLine := c.startLine
    endLine := c.endLine
    fingerprint := c.fingerprint
  }

private def nullStream : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure ByteArray.empty
  write := fun _ => pure ()
  getLine := pure ""
  putStr := fun _ => pure ()
  isTty := pure false
}

private def mkCaptureStream (bufRef : IO.Ref ByteArray) : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure ByteArray.empty
  write := fun bytes => bufRef.modify (· ++ bytes)
  getLine := pure ""
  putStr := fun s => bufRef.modify (· ++ s.toUTF8)
  isTty := pure false
}

def runWorkerLoopMode
    (prepareEnv : WorkerRequest → Lean.Name → Lean.Environment → Lean.Environment := fun _ _ env => env) :
    IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let initCwd ← IO.Process.getCurrentDir
  let mut binding : WorkerBinding := .unbound
  let mut keepGoing := true
  while keepGoing do
    let rawLine ← stdin.getLine
    if rawLine.isEmpty then
      keepGoing := false
    else
      let line := rawLine.trimAscii.toString
      match Lean.Json.parse line >>= Lean.fromJson? (α := LoopRequest) with
      | .error e =>
        let resp : LoopResponse := {
          reqId := 0
          relPath := ""
          ok := false
          error? := some s!"invalid worker request JSON: {e}"
        }
        stdout.putStrLn (Lean.toJson resp).compress
        stdout.flush
        keepGoing := false
      | .ok lreq =>
        IO.setNumHeartbeats 0
        let capturedOutRef ← IO.mkRef ByteArray.empty
        let captureOut := mkCaptureStream capturedOutRef
        let runRes ← (try
          IO.withStdin nullStream <| IO.withStdout captureOut <|
            analyzeTargetWithState prepareEnv lreq.request binding
        finally
          IO.Process.setCurrentDir initCwd).toBaseIO
        match runRes with
        | .ok (comments, binding') =>
          let capturedOut ← capturedOutRef.get
          if !capturedOut.isEmpty then
            let preview := match String.fromUTF8? capturedOut with
              | some s =>
                let trimmed := s.trimAscii.toString
                if trimmed.isEmpty then s!"<{capturedOut.size} whitespace byte(s)>" else trimmed
              | none => s!"<{capturedOut.size} non-UTF-8 byte(s)>"
            let resp : LoopResponse := {
              reqId := lreq.reqId
              relPath := lreq.request.relPath
              ok := false
              error? := some s!"unexpected stdout output while analyzing {lreq.request.relPath}: {preview}"
            }
            stdout.putStrLn (Lean.toJson resp).compress
            stdout.flush
            keepGoing := false
          else
            binding := binding'
            let resp : LoopResponse := {
              reqId := lreq.reqId
              relPath := lreq.request.relPath
              ok := true
              comments := toWireComments comments
            }
            stdout.putStrLn (Lean.toJson resp).compress
            stdout.flush
        | .error err =>
          let resp : LoopResponse := {
            reqId := lreq.reqId
            relPath := lreq.request.relPath
            ok := false
            error? := some (toString err)
          }
          stdout.putStrLn (Lean.toJson resp).compress
          stdout.flush
          keepGoing := false

end NoComments.Runner
