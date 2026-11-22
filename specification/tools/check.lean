module

public import Lean
public import Lake
public import Lake.Load.Package
public import LeanIntent.Cone
public import LeanIntent.CodeAudit
public import LeanIntent.Confirmation.Read
public import LeanIntent.Implementation.Read
public import LeanIntent.Required.Read
public import LeanIntent.Execution.Lake
public import LeanIntent.Execution.Read
public import NoCommentsSpecification

open Lean
open LeanIntent

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def recordNames : List Name :=
  [ `NoCommentsSpecification.CoreRecords.isFingerprintRecord
  , `NoCommentsSpecification.CoreRecords.fingerprintRecord
  , `NoCommentsSpecification.CoreRecords.checkTokenRecord
  , `NoCommentsSpecification.CoreRecords.collectRangesRecord
  , `NoCommentsSpecification.CoreRecords.sourceOrderRecord
  , `NoCommentsSpecification.CoreRecords.distinctCommentLinesRecord
  , `NoCommentsSpecification.CoreRecords.firstOutOfOrderRecord
  , `NoCommentsSpecification.CoreRecords.sortFingerprintsRecord
  , `NoCommentsSpecification.CoreRecords.missingFromRecord
  , `NoCommentsSpecification.ConfigRecords.parseConfigRecord
  , `NoCommentsSpecification.ConfigRecords.classifyFileRecord
  , `NoCommentsSpecification.ConfigRecords.classifyTrackedRecord
  , `NoCommentsSpecification.RatchetRecords.analyzeCommentsRecord
  , `NoCommentsSpecification.RatchetRecords.parseRatchetRecord
  , `NoCommentsSpecification.RatchetRecords.checkExactSyncRecord
  , `NoCommentsSpecification.RatchetRecords.checkMonotonicFileRecord
  , `NoCommentsSpecification.RatchetRecords.validateCheckRecord ]

private def implDecls (env : Environment) : List Name :=
  env.constants.fold (init := []) fun acc n ci =>
    let s := n.toString
    if s.startsWith "NoComments.Core." ||
       s.startsWith "NoComments.Config." ||
       s.startsWith "NoComments.RatchetCore." then
      match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        if n.isInternal || env.isProjectionFn n then acc
        else
          let last := (s.splitOn ".").getLast!
          if last == "mk" || last == "inj" || last == "injEq" ||
             last == "rec" || last == "recOn" || last == "casesOn" ||
             last == "noConfusion" || last == "noConfusionType" ||
             last == "sizeOf_spec" || last == "elim" ||
             last.startsWith "match_" then acc
          else n :: acc
      | _ => acc
    else acc

private def specCheckTargets (env : Environment) : List Name :=
  env.constants.fold (init := []) fun acc n ci =>
    let s := n.toString
    if s.startsWith "NoCommentsSpecification." && !n.isInternal then
      match ci with
      | .defnInfo _ | .thmInfo _ => n :: acc
      | _ => acc
    else acc

private def checkAxioms : CoreM Nat := do
  let env ← getEnv
  let targets := specCheckTargets env
  for n in targets do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless allowedAxioms.contains ax do
        throwError "disallowed axiom {ax} used by {n}"
  pure targets.length

private def hasCodeAuditTarget (ci : ConstantInfo) : Bool :=
  let consts := ci.type.getUsedConstants
  consts.contains ``LeanIntent.Verdicts ||
    consts.contains ``LeanIntent.WitnessVerdicts ||
    consts.contains ``LeanIntent.HasCode ||
    consts.contains ``LeanIntent.ExactCode

private def loadBuiltModules : IO (Array Name) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["query", "--json", "@/NoCommentsSpecification:modules"]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"lake query failed:\n{out.stderr}"
  match Required.Read.queryModules out.stdout with
  | .ok ms => return ms
  | .error err => throw <| IO.userError s!"invalid lake module list: {err}"

private def loadAllExecutables : IO (Array (Name × Name)) := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean? | throw <| IO.userError "Lake found no Lean installation"
  let some lake := lake? | throw <| IO.userError "Lake found no Lake installation"
  let lakeEnv ← match ← (Lake.Env.compute lake lean elan?).toBaseIO with
    | .ok e => pure e
    | .error err => throw <| IO.userError err
  let cwd ← IO.currentDir
  let loadPkg (dir : System.FilePath) : IO Lake.Package := do
    let some pkg ← (Lake.loadPackage {
      lakeEnv, wsDir := dir, relConfigFile := "lakefile.toml", configLang? := some .toml
    }).toBaseIO
      | throw <| IO.userError s!"Lake could not load {dir / "lakefile.toml"}"
    return pkg
  let specPkg ← loadPkg cwd
  let parentPkg ← loadPkg (cwd / "..")
  return Execution.lakeExecutables parentPkg ++ Execution.lakeExecutables specPkg

public unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let built ← loadBuiltModules
  let exes ← loadAllExecutables
  let mods : Array Import :=
    #[ { module := `NoComments.Core, importAll := true }
     , { module := `NoComments.Config, importAll := true }
     , { module := `NoComments.RatchetCore, importAll := true }
     , { module := `NoCommentsSpecification, importAll := true } ]
  let env ← importModules mods {} (loadExts := true)
  let impl := implDecls env
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let ((auditCount, axCount, confCount, implCount, reqCount, execCount), _) ← (Meta.MetaM.run' (do
    for recName in recordNames do
      Cone.requireIndependent recName impl
    let auditTargets := env.constants.fold (init := []) fun acc n ci =>
      if n.toString.startsWith "NoCommentsSpecification." && !n.isInternal &&
          hasCodeAuditTarget ci then
        n :: acc
      else acc
    for tgt in auditTargets do
      CodeAudit.requireCodes tgt
    let confirmed ← Confirmation.Read.check built
    unless confirmed.findings.isEmpty do
      throwError "confirmation findings: {confirmed.findings.length}"
    let implemented ← Implementation.Read.check built
    unless implemented.findings.isEmpty do
      throwError "implementation findings: {repr implemented.findings}"
    unless implemented.awaiting.isEmpty do
      throwError "deliverables still awaiting implementation: {repr implemented.awaiting}"
    let required ← Required.Read.check built
    unless required.findings.isEmpty do
      throwError "required-theorems findings:\n{"\n".intercalate (required.findings.map (·.message))}"
    let executed ← Execution.Read.check built exes
    unless executed.findings.isEmpty do
      throwError "execution findings: {repr executed.findings}"
    unless executed.notRun.isEmpty do
      throwError "deliverables not claimed by any executable: {repr executed.notRun}"
    let axCount ← checkAxioms
    pure (auditTargets.length, axCount, confirmed.counted.length,
      implemented.implementations.length, required.theorems.length, executed.reached.length)
    : Meta.MetaM (Nat × Nat × Nat × Nat × Nat × Nat))).toIO ctx { env := env }
  IO.println s!"check ok: records={recordNames.length} impl_excluded={impl.length} code_audited={auditCount} confirmed_answers={confCount} implemented={implCount} required_theorems={reqCount} executed={execCount} axiom_checked={axCount}"
