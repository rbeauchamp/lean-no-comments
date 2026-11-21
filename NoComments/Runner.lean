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

def analyzeTarget (req : WorkerRequest) : IO (Array Core.Comment) := do
  let sysroot ←
    if req.leanSysroot != "" then pure (System.FilePath.mk req.leanSysroot)
    else Lean.findSysroot
  Lean.initSearchPath sysroot (System.SearchPath.parse req.leanPath)
  let content ← IO.FS.readFile (System.FilePath.mk req.absFile)
  let inputCtx := Lean.Parser.mkInputContext content req.relPath
  let (headerStx, headerParserState, headerMsgs) ← Lean.Parser.parseHeader inputCtx
  if headerMsgs.hasErrors then
    let errText ← formatErrors headerMsgs
    throw <| IO.userError s!"parse error in header of {req.relPath}:\n{errText}"
  for dynlib in req.setup.dynlibs do
    Lean.loadDynlib dynlib
  enableInitializers
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
  let (env, hdrMsgs) ← Lean.Elab.processHeaderCore
    headerParserState.pos
    imports
    isModule
    opts
    headerMsgs
    inputCtx
    (plugins := filteredPlugins)
    (mainModule := mainModule)
    (package? := req.setup.package?)
    (arts := req.setup.importArts)
    (headerStx? := some headerSyntax)
    (origHeaderStx? := some headerSyntax)
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
  | .ok acc => return Core.sourceOrder acc

def runWorkerMode : IO Unit := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  let req : WorkerRequest ← match Lean.Json.parse raw >>= Lean.fromJson? with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"invalid worker request JSON: {e}"
  let comments ← analyzeTarget req
  for c in comments do
    IO.println s!"{c.fingerprint} {c.kind} {c.startLine} {c.endLine}"

end NoComments.Runner
