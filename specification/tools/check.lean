module

public import LeanIntent.Cone
public import LeanIntent.CodeAudit
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

public def main : IO Unit := do
  initSearchPath (← findSysroot)
  let mods : Array Import :=
    #[ { module := `NoComments.Core, importAll := true }
     , { module := `NoComments.Config, importAll := true }
     , { module := `NoComments.RatchetCore, importAll := true }
     , { module := `NoCommentsSpecification, importAll := true } ]
  let env ← importModules mods {}
  let impl := implDecls env
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let ((auditCount, axCount), _) ← (do
    for recName in recordNames do
      Cone.requireIndependent recName impl
    let auditTargets := env.constants.fold (init := []) fun acc n ci =>
      if n.toString.startsWith "NoCommentsSpecification." && !n.isInternal &&
          hasCodeAuditTarget ci then
        n :: acc
      else acc
    let audited ← Meta.MetaM.run' do
      for tgt in auditTargets do
        CodeAudit.requireCodes tgt
      pure auditTargets.length
    let axCount ← checkAxioms
    pure (audited, axCount)
    : CoreM (Nat × Nat)).toIO ctx { env := env }
  IO.println s!"check ok: records={recordNames.length} impl_excluded={impl.length} code_audited={auditCount} axiom_checked={axCount}"