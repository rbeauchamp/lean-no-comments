module

public import Lean
import Lake.CLI.Error
import Lake.Load.Package
import Lake.Util.IO
meta import Lake.CLI.Error
meta import Lake.Load.Package
meta import Lake.Util.IO

open Lean

namespace NoComments.TestListing

private unsafe def enableInitializersImpl : IO Unit :=
  Lean.enableInitializersExecution

@[implemented_by enableInitializersImpl]
private def enableInitializers : IO Unit := pure ()

private def loadPackageConfig (elanInstall? : Option Lake.ElanInstall)
    (leanInstall? : Option Lake.LeanInstall) (lakeInstall? : Option Lake.LakeInstall) :
    EIO Lake.CliError Lake.LoadConfig := do
  let some wsDir ← Lake.resolvePath? "."
    | throw <| .missingRootDir "."
  let lake ← match lakeInstall? with
    | none => throw .unknownLakeInstall
    | some lake => pure lake
  let lean ← match leanInstall? with
    | none => throw .unknownLeanInstall
    | some lean => pure lean
  let lakeEnv ← Lake.Env.compute lake lean elanInstall? none |>.adapt fun msg => .invalidEnv msg
  return {
    lakeArgs? := some #[]
    lakeEnv
    wsDir
    relConfigFile := Lake.defaultConfigFile
    packageOverrides := #[]
    lakeOpts := {}
    leanOpts := Lean.Options.empty
    reconfigure := false
    updateDeps := false
    updateToolchain := true
  }

private def readLakeTestDriver : IO (Option String) := do
  let installs ← Lake.findInstall?
  let loaded ← (((loadPackageConfig installs.1 installs.2.1 installs.2.2).adapt toString >>= fun config =>
    liftM (m := EIO String) ((Lake.loadPackage config).toBaseIO : BaseIO _)) :
      EIO String (Option Lake.Package)).toBaseIO
  match loaded with
  | .error why => throw <| IO.userError why
  | .ok none => throw <| IO.userError "Lake failed to load package configuration"
  | .ok (some pkg) =>
    if pkg.testDriver == "" then return none
    else return some pkg.testDriver

public def forbiddenCommandKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.eval,
   ``Lean.Parser.Command.evalBang,
   ``Lean.Parser.Command.guardCmd,
   ``Lean.guardMsgsCmd,
   ``Lean.guardPanicCmd,
   ``Lean.Parser.Command.guardExprCmd,
   ``Lean.Parser.Command.check,
   ``Lean.Parser.Command.check_failure,
   ``Lean.Parser.checkSimp,
   ``Lean.Parser.checkSimpFailure,
   ``Lean.Parser.checkTactic,
   ``Lean.Parser.checkTacticFailure,
   ``Lean.Parser.Command.print,
   ``Lean.Parser.Command.printAxioms,
   ``Lean.Parser.Command.printSig,
   ``Lean.Parser.Command.printEqns,
   ``Lean.Parser.Command.printTacTags,
   ``Lean.Parser.Command.example]

public def forbiddenAttrs : List Name :=
  [`test_driver, `Lake.test_driver]

private def lineOfPos (ictx : Parser.InputContext) (stx : Syntax) : Nat :=
  match stx.getPos? with
  | some pos => (ictx.fileMap.toPosition pos).line
  | none => 1

public partial def scanSyntax (ictx : Parser.InputContext) (file : String) (stx : Syntax)
    (acc : Array String) : Array String :=
  match stx with
  | .node _ k args =>
    let acc' :=
      if forbiddenCommandKinds.contains k then
        acc.push s!"{file}:{lineOfPos ictx stx}:cmd:{k}"
      else if k == ``Lean.Parser.Attr.simple then
        if h : 0 < args.size then
          match args[0] with
          | .ident _ _ n _ =>
            if forbiddenAttrs.contains n then
              acc.push s!"{file}:{lineOfPos ictx args[0]}:attr:{n}"
            else
              acc
          | _ => acc
        else
          acc
      else
        acc
    args.foldl (fun a c => scanSyntax ictx file c a) acc'
  | _ => acc

public def hasTestDirectory (file : String) : Bool :=
  let dirs := (file.splitOn "/").dropLast
  dirs.contains "test" || dirs.contains "tests"

private def listTrackedLeanFiles : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["ls-files", "--full-name", "-z", "--", "*.lean"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"git ls-files failed: {out.stderr.trimAscii.toString}"
  let files := ((out.stdout.splitOn "\x00").filter (· != "")).toArray.qsort (· < ·)
  if files.isEmpty then
    throw <| IO.userError "git ls-files returned no Lean files"
  return files

private def parseLeanEnv : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializers
  let ictx := Parser.mkInputContext "import Lean\nimport Lake\n" "<init>"
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let hstx : Elab.HeaderSyntax := ⟨hdr⟩
  let (env, hdrMsgs) ← Elab.processHeaderCore ps.pos (hstx.imports true) false {} msgs ictx
  if hdrMsgs.hasErrors then
    let shown ← hdrMsgs.toList.mapM (·.toString)
    throw <| IO.userError s!"failed to initialize Lean parser environment:\n{String.join shown}"
  return env

private partial def scanCommands (ictx : Parser.InputContext) (pmctx : Parser.ParserModuleContext)
    (file : String) (ps : Parser.ModuleParserState) (msgs : MessageLog)
    (acc : Array String) : Except String (Array String) :=
  let (cmd, ps', msgs') := Parser.parseCommand ictx pmctx ps msgs
  let acc' := scanSyntax ictx file cmd acc
  if Parser.isTerminalCommand cmd || ictx.atEnd ps'.pos then
    if msgs'.hasErrors then
      .error s!"{file}: Lean parser reported errors while scanning for tests"
    else
      .ok acc'
  else
    scanCommands ictx pmctx file ps' msgs' acc'

public def collectTestFindings : IO (Array String) := do
  let mut findings : Array String := #[]
  if let some driver ← readLakeTestDriver then
    findings := findings.push s!"lake-test-driver:{driver}"
  let env ← parseLeanEnv
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let files ← listTrackedLeanFiles
  for file in files do
    if hasTestDirectory file then
      findings := findings.push s!"file:{file}"
    let text ← IO.FS.readFile file
    let ictx := Parser.mkInputContext text file
    let (_, ps, msgs) ← Parser.parseHeader ictx
    if msgs.hasErrors then
      throw <| IO.userError s!"{file}: parse error in header while scanning for tests"
    match scanCommands ictx pmctx file ps msgs #[] with
    | .ok fileFindings => findings := findings ++ fileFindings
    | .error err => throw <| IO.userError err
  return findings

end NoComments.TestListing

public def main (args : List String) : IO UInt32 := do
  let checkMode ← match args with
    | [] => pure false
    | ["--check"] => pure true
    | _ =>
      IO.eprintln "usage: test-listing [--check]"
      return 1
  let findings ← NoComments.TestListing.collectTestFindings
  for f in findings do
    IO.println f
  if checkMode && !findings.isEmpty then
    IO.eprintln s!"error: found {findings.size} forbidden test item(s)"
    return 1
  return 0
