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

private def implModules : List Name :=
  [ `NoComments.Core
  , `NoComments.Config
  , `NoComments.RatchetCore ]

private def hasMatchComponent : Name → Bool
  | .anonymous => false
  | .str parent s => s.startsWith "match_" || hasMatchComponent parent
  | .num parent _ => hasMatchComponent parent

private def isExcludedImplName (userName : Name) : Bool :=
  hasMatchComponent userName ||
  match userName with
  | .str _ last =>
      last == "mk" || last == "inj" || last == "injEq" ||
      last == "rec" || last == "recOn" || last == "casesOn" ||
      last == "noConfusion" || last == "noConfusionType" ||
      last == "sizeOf_spec" || last == "elim" ||
      last == "below" || last == "ibelow" ||
      last == "brecOn" || last == "binductionOn"
  | _ => false

private def implDecls (env : Environment) : CoreM (List Name) := do
  let mut acc : List Name := []
  for modName in implModules do
    let some modIdx := env.getModuleIdx? modName
      | throwError "implementation module {modName} is not imported in environment"
    let modData := env.header.moduleData[modIdx.toNat]!
    let mut modCount := 0
    for ci in modData.constants do
      match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .axiomInfo _ =>
        let userName := privateToUserName ci.name
        if env.isProjectionFn ci.name || userName.isInternalDetail ||
            isExcludedImplName userName then
          pure ()
        else
          unless (env.find? ci.name).isSome do
            throwError "implementation constant {ci.name} from {modName} is missing from environment"
          acc := ci.name :: acc
          modCount := modCount + 1
      | _ => pure ()
    if modCount == 0 then
      throwError "no implementation declarations found in {modName}"
  unless acc.any (fun n => isPrivateName n &&
      privateToUserName n == `NoComments.Config.stripLeadingDotSlashChars) do
    throwError "expected private helper NoComments.Config.stripLeadingDotSlashChars in implDecls"
  return acc.reverse

private def expectedAuditTargets : List Name :=
  [ ``NoCommentsSpecification.AdequacyCore.isFingerprint_verdicts
  , ``NoCommentsSpecification.AdequacyCore.isFingerprint_witnesses_whole
  , ``NoCommentsSpecification.AdequacyCore.isFingerprint_perInput_witnesses
  , ``NoCommentsSpecification.AdequacyCore.fingerprint_verdicts
  , ``NoCommentsSpecification.AdequacyCore.fingerprint_witnesses_whole_valid
  , ``NoCommentsSpecification.AdequacyCore.fingerprint_witnesses_whole_nonconst
  , ``NoCommentsSpecification.AdequacyCore.fpValid_perInput_witnesses
  , ``NoCommentsSpecification.AdequacyCore.distinctCommentLines_verdicts
  , ``NoCommentsSpecification.AdequacyCore.distinctCommentLines_witnesses_whole
  , ``NoCommentsSpecification.AdequacyCore.firstOutOfOrder_verdicts
  , ``NoCommentsSpecification.AdequacyCore.firstOutOfOrder_witnesses_whole ]

section ExpectedRequired

open NoCommentsSpecification.AdequacyCore
open NoCommentsSpecification.AdequacyCollect
open NoCommentsSpecification.AdequacyConfig
open NoCommentsSpecification.AdequacyRatchet
open NoCommentsSpecification.Comparison
open NoCommentsSpecification.Explanations
open NoCommentsSpecification.Refinement.Core
open NoCommentsSpecification.Refinement.Config
open NoCommentsSpecification.Refinement.Ratchet

private def expectedRequired : List (Name × List Name) :=
  [ (``NoCommentsSpecification.Required.isFingerprintRequired,
      [ ``isFingerprint_o2, ``isFingerprint_o2Run, ``isFingerprint_o3
      , ``isFingerprint_o4, ``isFingerprint_o5, ``isFingerprint_oPair_whole
      , ``isFingerprint_perInput_pairOf, ``isFingerprint_perInput_oPair_table
      , ``isFingerprint_verdicts, ``isFingerprint_witnesses_whole
      , ``isFingerprint_perInput_witnesses, ``isFingerprint_meets_iff
      , ``isFingerprint_refuses_empty, ``isFingerprint_accepts_zero
      , ``isFingerprint_meets, ``isFingerprint_fulfilled ])
  , (``NoCommentsSpecification.Required.fingerprintRequired,
      [ ``fingerprint_o2, ``fingerprint_o2Run, ``fingerprint_o3
      , ``fingerprint_o4, ``fingerprint_o5, ``fingerprint_not_o5_eq
      , ``fingerprint_oPair_whole, ``fpValid_perInput_pairOf
      , ``fpValid_perInput_witnesses, ``fingerprint_verdicts
      , ``fingerprint_witnesses_whole_valid, ``fingerprint_witnesses_whole_nonconst
      , ``fingerprint_meets_iff, ``NoCommentsSpecification.Explanations.fingerprint_nonconstant
      , ``NoCommentsSpecification.Refinement.Core.fingerprint_nonconstant, ``fingerprint_allows_zero_empty
      , ``fingerprint_meets, ``fingerprint_fulfilled ])
  , (``NoCommentsSpecification.Required.checkTokenRequired,
      [ ``checkToken_o2, ``checkToken_o2Run, ``checkToken_o3
      , ``checkToken_o4, ``checkToken_o5, ``checkToken_not_o5_eq
      , ``checkToken_interim_const_fails, ``checkToken_healthy_owed
      , ``token_healthy_nonempty, ``token_healthy_and_refusal_disjoint
      , ``checkToken_negative_external_model, ``checkToken_oPair_whole
      , ``checkToken_perInput_pairOf, ``checkToken_perInput_table_attack
      , ``diff_checkToken_identMismatch, ``checkToken_healthy_entailment
      , ``checkToken_refuses_raw_opener, ``checkToken_allows_custom_error
      , ``checkToken_meets, ``checkToken_fulfilled ])
  , (``NoCommentsSpecification.Required.collectRangesRequired,
      [ ``collectRanges_o2, ``collectRanges_o2Run, ``collectRanges_o3
      , ``collectRanges_o4, ``collectRanges_o5, ``collectRanges_not_o5_eq
      , ``collectRanges_healthy_owed, ``collectRanges_healthy_nonempty
      , ``collectRefusal_contradicts_healthy, ``collectRanges_negative_external_model
      , ``collect_reason_classified, ``collectRanges_oPair_whole
      , ``collectRanges_perInput_pairOf, ``collectRanges_perInput_table_attack
      , ``collectRanges_interim_const_fails, ``diff_collectRanges_plainDocComment
      , ``collectRanges_healthy_entailment, ``collectRanges_exact_scanner
      , ``collectRanges_allows_custom_error, ``collectRanges_rangesStep
      , ``collectRanges_new_span_fingerprint, ``collectRanges_meets
      , ``collectRanges_fulfilled ])
  , (``NoCommentsSpecification.Required.sourceOrderRequired,
      [ ``sourceOrder_o2, ``sourceOrder_o2Run, ``sourceOrder_o3
      , ``sourceOrder_o4, ``sourceOrder_o5, ``sourceOrder_interim_const_fails
      , ``sourceOrder_oPair_whole, ``sourceOrder_meets_iff
      , ``sourceOrder_members_recorded, ``sourceOrder_meets
      , ``sourceOrder_fulfilled ])
  , (``NoCommentsSpecification.Required.distinctCommentLinesRequired,
      [ ``distinctCommentLines_o2, ``distinctCommentLines_o2Run, ``distinctCommentLines_o3
      , ``distinctCommentLines_o4, ``distinctCommentLines_o5
      , ``distinctCommentLines_oPair_whole, ``distinct_perInput_pairOf
      , ``distinct_perInput_oPair_table, ``distinctCommentLines_verdicts
      , ``distinctCommentLines_witnesses_whole, ``distinctLines_equiv_of_pos
      , ``diff_distinctLines_zero_line, ``distinctCommentLines_empty_zero
      , ``distinctCommentLines_meets, ``distinctCommentLines_fulfilled ])
  , (``NoCommentsSpecification.Required.firstOutOfOrderRequired,
      [ ``firstOutOfOrder_o2, ``firstOutOfOrder_o2Run, ``firstOutOfOrder_o3
      , ``firstOutOfOrder_o4, ``firstOutOfOrder_o5
      , ``firstOutOfOrder_oPair_whole, ``firstOutOfOrder_verdicts
      , ``firstOutOfOrder_witnesses_whole, ``firstOutOfOrder_meets_iff
      , ``firstOutOfOrder_nil_none, ``firstOutOfOrder_meets
      , ``firstOutOfOrder_fulfilled ])
  , (``NoCommentsSpecification.Required.sortFingerprintsRequired,
      [ ``sortFingerprints_o2, ``sortFingerprints_o2Run, ``sortFingerprints_o3
      , ``sortFingerprints_o4, ``sortFingerprints_o5
      , ``sortFingerprints_interim_const_fails, ``sortFingerprints_oPair_whole
      , ``sortFingerprints_meets_iff, ``sortFingerprints_sorted
      , ``sortFingerprints_meets, ``sortFingerprints_fulfilled ])
  , (``NoCommentsSpecification.Required.missingFromRequired,
      [ ``missingFrom_o2, ``missingFrom_o2Run, ``missingFrom_o3
      , ``missingFrom_o4, ``missingFrom_o5, ``missingFrom_not_o5_eq
      , ``missingFrom_interim_degenerate, ``missingFrom_oPair_whole
      , ``missingFrom_meets_iff, ``missingFrom_self_empty
      , ``missingFrom_allows_unsorted_output, ``missingFrom_meets
      , ``missingFrom_fulfilled ])
  , (``NoCommentsSpecification.Required.parseConfigRequired,
      [ ``parseConfig_o2_of_oracle, ``parseConfig_o2Run, ``parseConfig_o3_of_oracle
      , ``parseConfig_o4, ``parseConfig_o5, ``parseConfig_not_o5_eq_of_oracle
      , ``parseConfig_oPair_whole, ``parseConfig_perInput_pairOf
      , ``parseConfig_perInput_table_attack, ``parseConfig_interim_const_fails_of_oracle
      , ``parseConfig_healthy_nonempty_of_oracle, ``parseConfig_healthy_owed
      , ``validConfigJson_and_refusal_disjoint
      , ``parseConfig_negative_external_model_of_oracle, ``parseConfig_reason_classified
      , ``diff_parseConfig_cleanCtrl, ``parseConfig_healthy_entailment
      , ``parseConfig_allows_custom_error, ``parseConfigJson_meets
      , ``parseConfigJson_fulfilled ])
  , (``NoCommentsSpecification.Required.classifyFileRequired,
      [ ``classifyFile_o2, ``classifyFile_o2Run, ``classifyFile_o3
      , ``classifyFile_o4, ``classifyFile_o5, ``classifyFile_not_o5_eq
      , ``classifyFile_oPair_whole, ``classifyFile_perInput_pairOf
      , ``classifyFile_perInput_table_attack, ``classifyFile_interim_const_fails
      , ``classifyFile_healthy_nonempty, ``classifyFile_healthy_owed
      , ``classifyFile_negative_external_model, ``classifyFile_reason_classified
      , ``diff_classifyFile_segmentPrefix, ``classifyFile_healthy_entailment
      , ``classifyFile_allows_custom_error, ``classifyFile_meets
      , ``classifyFile_fulfilled ])
  , (``NoCommentsSpecification.Required.classifyTrackedRequired,
      [ ``classifyTracked_o2, ``classifyTracked_o2Run, ``classifyTracked_o3
      , ``classifyTracked_o4, ``classifyTracked_o5, ``classifyTracked_not_o5_eq
      , ``classifyTracked_oPair_whole, ``classifyTracked_perInput_pairOf
      , ``classifyTracked_perInput_table_attack, ``classifyTracked_interim_const_fails
      , ``classifyTracked_healthy_nonempty, ``classifyTracked_healthy_owed
      , ``classifyTracked_negative_external_model, ``classifyTracked_reason_classified
      , ``classifyTracked_healthy_entailment, ``classifyTracked_allows_custom_error
      , ``classifyTrackedFiles_meets, ``classifyTrackedFiles_fulfilled ])
  , (``NoCommentsSpecification.Required.analyzeCommentsRequired,
      [ ``analyzeComments_o2, ``analyzeComments_o2Run, ``analyzeComments_o3
      , ``analyzeComments_o4, ``analyzeComments_o5
      , ``analyzeComments_oPair_whole, ``analyzeComments_perInput_pairOf
      , ``analyzeComments_perInput_table_attack, ``analyzeComments_interim_const_fails
      , ``analyzeComments_equiv_of_pos, ``analyzeComments_preserves_file
      , ``analyzeComments_meets, ``analyzeComments_fulfilled ])
  , (``NoCommentsSpecification.Required.parseRatchetRequired,
      [ ``parseRatchet_o2_of_oracle, ``parseRatchet_o2Run, ``parseRatchet_o3_of_oracle
      , ``parseRatchet_o4, ``parseRatchet_o5, ``parseRatchet_not_o5_eq_of_oracle
      , ``parseRatchet_oPair_whole, ``parseRatchet_perInput_pairOf
      , ``parseRatchet_perInput_table_attack, ``parseRatchet_interim_const_fails_of_oracle
      , ``parseRatchet_healthy_nonempty_of_oracle, ``parseRatchet_healthy_owed
      , ``validRatchetJson_and_refusal_disjoint
      , ``parseRatchet_negative_external_model_of_oracle, ``parseRatchet_reason_classified
      , ``parseRatchet_healthy_entailment, ``parseRatchet_allows_custom_error
      , ``parseRatchetJson_meets, ``parseRatchetJson_fulfilled ])
  , (``NoCommentsSpecification.Required.checkExactSyncRequired,
      [ ``checkExactSync_o2, ``checkExactSync_o2Run, ``checkExactSync_o3
      , ``checkExactSync_o4, ``checkExactSync_o5, ``checkExactSync_not_o5_eq
      , ``checkExactSync_oPair_whole, ``checkExactSync_perInput_pairOf
      , ``checkExactSync_perInput_table_attack, ``checkExactSync_interim_const_fails
      , ``checkExactSync_healthy_nonempty, ``checkExactSync_healthy_owed
      , ``checkExactSync_negative_external_model, ``checkExactSync_meets_iff
      , ``checkExactSync_accepts_sync, ``checkExactSync_allows_custom_error
      , ``checkExactSync_meets, ``checkExactSync_fulfilled ])
  , (``NoCommentsSpecification.Required.checkMonotonicFileRequired,
      [ ``checkMonotonicFile_o2, ``checkMonotonicFile_o2Run, ``checkMonotonicFile_o3
      , ``checkMonotonicFile_o4, ``checkMonotonicFile_o5, ``checkMonotonicFile_not_o5_eq
      , ``checkMonotonicFile_oPair_whole, ``checkMonotonicFile_perInput_pairOf
      , ``checkMonotonicFile_perInput_table_attack, ``checkMonotonicFile_interim_const_fails
      , ``checkMonotonicFile_healthy_nonempty, ``checkMonotonicFile_healthy_owed
      , ``checkMonotonicFile_negative_external_model, ``checkMonotonicFile_meets_iff
      , ``checkMonotonicFile_accepts_monotonic, ``checkMonotonicFile_allows_custom_error
      , ``checkMonotonicFile_meets, ``checkMonotonicFile_fulfilled ])
  , (``NoCommentsSpecification.Required.validateCheckRequired,
      [ ``validateCheck_o2, ``validateCheck_o2Run, ``validateCheck_o3
      , ``validateCheck_o4, ``validateCheck_o5, ``validateCheck_not_o5_eq
      , ``validateCheck_oPair_whole, ``validateCheck_perInput_pairOf
      , ``validateCheck_perInput_table_attack, ``validateCheck_interim_const_fails
      , ``validateCheck_healthy_nonempty, ``validateCheck_healthy_owed
      , ``validateOk_and_refusal_disjoint
      , ``validateCheck_negative_external_model, ``validateCheck_reason_classified
      , ``validateCheck_equiv_of_nodup, ``diff_validateCheck_duplicate_file
      , ``validateCheck_healthy_entailment, ``validateCheck_allows_custom_error
      , ``validateCheck_meets, ``validateCheck_fulfilled ]) ]

end ExpectedRequired

private def checkAuditTargets (actual : List Name) : MetaM Unit := do
  for tgt in expectedAuditTargets do
    unless actual.contains tgt do
      throwError "missing expected CodeAudit target: {tgt}"
  for tgt in actual do
    unless expectedAuditTargets.contains tgt do
      throwError "unexpected CodeAudit target: {tgt}"
  unless actual.length == expectedAuditTargets.length do
    throwError "CodeAudit target count mismatch: expected {expectedAuditTargets.length}, got {actual.length}"

private def checkRequiredMembership (actual : List (Name × Implementation.Constant)) : MetaM Unit := do
  let expectedEntries := expectedRequired.map Prod.fst
  for (r, _) in actual do
    unless expectedEntries.contains r do
      throwError "unexpected Required entry in report: {r}"
  for (reqName, expectedThms) in expectedRequired do
    unless expectedThms.Nodup do
      throwError "duplicate theorem in expectedRequired for {reqName}"
    let foundThms := actual.filterMap fun (r, c) => if r == reqName then some c.name else none
    for thm in expectedThms do
      unless foundThms.contains thm do
        throwError "missing required theorem {thm} under {reqName}"
    for thm in foundThms do
      unless expectedThms.contains thm do
        throwError "unexpected required theorem {thm} under {reqName}"
    unless foundThms.length == expectedThms.length do
      throwError "required theorem count mismatch under {reqName}: expected {expectedThms.length}, got {foundThms.length}"

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
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let ((implCountDecls, auditCount, axCount, confCount, implCount, reqCount, execCount), _) ←
      (Meta.MetaM.run' (do
    let impl ← implDecls (← getEnv)
    for recName in recordNames do
      Cone.requireIndependent recName impl
    let auditTargets := env.constants.fold (init := []) fun acc n ci =>
      if n.toString.startsWith "NoCommentsSpecification." && !n.isInternal &&
          hasCodeAuditTarget ci then
        n :: acc
      else acc
    checkAuditTargets auditTargets
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
    unless implemented.implementations.length == recordNames.length do
      throwError "implementation count mismatch: expected {recordNames.length}, got {implemented.implementations.length}"
    let required ← Required.Read.check built
    unless required.findings.isEmpty do
      throwError "required-theorems findings:\n{"\n".intercalate (required.findings.map (·.message))}"
    checkRequiredMembership required.theorems
    let executed ← Execution.Read.check built exes
    unless executed.findings.isEmpty do
      throwError "execution findings: {repr executed.findings}"
    unless executed.notRun.isEmpty do
      throwError "deliverables not claimed by any executable: {repr executed.notRun}"
    unless executed.reached.length == recordNames.length do
      throwError "execution count mismatch: expected {recordNames.length}, got {executed.reached.length}"
    let axCount ← checkAxioms
    pure (impl.length, auditTargets.length, axCount, confirmed.counted.length,
      implemented.implementations.length, required.theorems.length, executed.reached.length)
    : Meta.MetaM (Nat × Nat × Nat × Nat × Nat × Nat × Nat))).toIO ctx { env := env }
  IO.println s!"check ok: records={recordNames.length} impl_excluded={implCountDecls} code_audited={auditCount} confirmed_answers={confCount} implemented={implCount} required_theorems={reqCount} executed={execCount} axiom_checked={axCount}"
