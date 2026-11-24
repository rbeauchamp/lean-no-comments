import Lean
import NoComments.Core

namespace NoComments.Runner

open NoComments

structure WorkerRequest where
  relPath : String
  absFile : String
  leanPath : String
  leanSysroot : String
  setup : Lean.ModuleSetup
  stripLakePlugin : Bool := true
  deriving Inhabited, Lean.ToJson, Lean.FromJson

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
  let errMsgs := msgs.toList.filter (·.severity == .error)
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

private partial def collectFrontendCommands (inputCtx : Lean.Parser.InputContext)
    (acc : Array Core.CommandRange) : Lean.Elab.Frontend.FrontendM (Array Core.CommandRange) := do
  let stBefore ← get
  let prevPos := stBefore.parserState.pos
  let pmCtx := mkParserCtx inputCtx stBefore.commandState
  let done ← Lean.Elab.Frontend.processCommand
  let stAfter ← get
  let nextPos := stAfter.parserState.pos
  let cmd := stAfter.commands.back!
  let acc := acc.push { ctx := pmCtx, prevPos, nextPos, stx := cmd }
  if done then
    return acc
  else
    collectFrontendCommands inputCtx acc

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
  | unbound
  | bound (key : HeaderCacheKey) (env : Lean.Environment)

private def nullStream : IO.FS.Stream := {
  flush := pure ()
  read := fun _ => pure ByteArray.empty
  write := fun _ => pure ()
  getLine := pure ""
  putStr := fun _ => pure ()
  isTty := pure false
}

private def loadBaseEnv (req : WorkerRequest) (inputCtx : Lean.Parser.InputContext)
    (headerPos : String.Pos.Raw) (headerMsgs : Lean.MessageLog)
    (imports : Array Lean.Import) (isModule : Bool) (opts : Lean.Options)
    (filteredPlugins : Array Lean.Plugin) (cacheKey : HeaderCacheKey)
    (binding : WorkerBinding) :
    IO (Lean.Environment × Lean.MessageLog × WorkerBinding) := do
  match binding with
  | .bound boundKey env =>
    if boundKey != cacheKey then
      throw <| IO.userError s!"worker process is bound to a different import header/environment; refusing to reuse worker for {req.relPath}"
    return (env, headerMsgs, binding)
  | .unbound =>
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
      let env ← Lean.importModules (leakEnv := true) (loadExts := true) (level := level)
        imports opts 0 filteredPlugins req.setup.importArts
      return (env, headerMsgs, .bound cacheKey env)
    catch e =>
      let env ← Lean.mkEmptyEnvironment
      let pos := inputCtx.fileMap.toPosition headerPos
      let msgs := headerMsgs.add { fileName := inputCtx.fileName, data := toString e, pos }
      return (env, msgs, .unbound)

private def analyzeTargetWithState (req : WorkerRequest) (binding : WorkerBinding) :
    IO (Array Core.Comment × WorkerBinding) :=
  IO.withStdin nullStream <| IO.withStdout nullStream do
  let content ← IO.FS.readFile (System.FilePath.mk req.absFile)
  let inputCtx := Lean.Parser.mkInputContext content req.relPath
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
    optionsJson := (Lean.toJson req.setup.options).compress
    importArtsJson := (Lean.toJson req.setup.importArts).compress
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
  let (cmdRanges, finalState) ←
    ((collectFrontendCommands inputCtx #[initialRange]).run { inputCtx }).run initFrontendState
  if finalState.commandState.messages.hasErrors then
    let errText ← formatErrors finalState.commandState.messages
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

def analyzeTarget (req : WorkerRequest) : IO (Array Core.Comment) := do
  let (comments, _) ← analyzeTargetWithState req .unbound
  return comments

def runWorkerMode : IO Unit := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  let req : WorkerRequest ← match Lean.Json.parse raw >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid worker request JSON: {e}"
  let comments ← analyzeTarget req
  for c in comments do
    IO.println s!"{c.fingerprint} {c.kind} {c.startLine} {c.endLine}"

private def toWireComments (comments : Array Core.Comment) : Array WireComment :=
  comments.map fun c => {
    kind := c.kind
    startLine := c.startLine
    endLine := c.endLine
    fingerprint := c.fingerprint
  }

def runWorkerLoopMode : IO Unit := do
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
      unless line.isEmpty do
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
          let runRes ← (try
            analyzeTargetWithState lreq.request binding
          finally
            IO.Process.setCurrentDir initCwd).toBaseIO
          match runRes with
          | .ok (comments, binding') =>
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
