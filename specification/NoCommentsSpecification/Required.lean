module

public import LeanIntent.Required
public import NoCommentsSpecification.Deliverables
public import NoCommentsSpecification.Comparison
public import NoCommentsSpecification.Refinement.Core
public import NoCommentsSpecification.Refinement.Config
public import NoCommentsSpecification.Refinement.Ratchet

@[expose] public section

namespace NoCommentsSpecification.Required

open LeanIntent
open NoCommentsSpecification.AdequacyCore
open NoCommentsSpecification.AdequacyCollect
open NoCommentsSpecification.AdequacyConfig
open NoCommentsSpecification.AdequacyRatchet
open NoCommentsSpecification.Comparison
open NoCommentsSpecification.Explanations
open NoCommentsSpecification.Deliverables
open NoCommentsSpecification.Refinement.Core
open NoCommentsSpecification.Refinement.Config
open NoCommentsSpecification.Refinement.Ratchet

def isFingerprintRequired : Required isFingerprintDeliverable where
  theorems := [
    ⟨isFingerprint_o2⟩, ⟨isFingerprint_o2Run⟩, ⟨isFingerprint_o3⟩,
    ⟨isFingerprint_o4⟩, ⟨isFingerprint_o5⟩, ⟨isFingerprint_oPair_whole⟩,
    ⟨isFingerprint_perInput_pairOf⟩, ⟨isFingerprint_perInput_oPair_table⟩,
    ⟨isFingerprint_verdicts⟩, ⟨isFingerprint_witnesses_whole⟩,
    ⟨isFingerprint_perInput_witnesses⟩, ⟨isFingerprint_meets_iff⟩,
    ⟨isFingerprint_refuses_empty⟩, ⟨isFingerprint_accepts_zero⟩,
    ⟨isFingerprint_meets⟩, ⟨isFingerprint_fulfilled⟩
  ]

def fingerprintRequired : Required fingerprintDeliverable where
  theorems := [
    ⟨fingerprint_o2⟩, ⟨fingerprint_o2Run⟩, ⟨fingerprint_o3⟩,
    ⟨fingerprint_o4⟩, ⟨fingerprint_o5⟩, ⟨fingerprint_not_o5_eq⟩,
    ⟨fingerprint_oPair_whole⟩, ⟨fpValid_perInput_pairOf⟩,
    ⟨fpValid_perInput_witnesses⟩, ⟨fingerprint_verdicts⟩,
    ⟨fingerprint_witnesses_whole_valid⟩, ⟨fingerprint_witnesses_whole_nonconst⟩,
    ⟨fingerprint_meets_iff⟩, ⟨Explanations.fingerprint_nonconstant⟩,
    ⟨Refinement.Core.fingerprint_nonconstant⟩, ⟨fingerprint_allows_zero_empty⟩,
    ⟨fingerprint_meets⟩, ⟨fingerprint_fulfilled⟩
  ]

def checkTokenRequired : Required checkTokenDeliverable where
  theorems := [
    ⟨checkToken_o2⟩, ⟨checkToken_o2Run⟩, ⟨checkToken_o3⟩,
    ⟨checkToken_o4⟩, ⟨checkToken_o5⟩, ⟨checkToken_not_o5_eq⟩,
    ⟨checkToken_interim_const_fails⟩, ⟨checkToken_healthy_owed⟩,
    ⟨token_healthy_nonempty⟩, ⟨token_healthy_and_refusal_disjoint⟩,
    ⟨checkToken_negative_external_model⟩, ⟨checkToken_oPair_whole⟩,
    ⟨checkToken_perInput_pairOf⟩, ⟨checkToken_perInput_table_attack⟩,
    ⟨diff_checkToken_identMismatch⟩, ⟨checkToken_healthy_entailment⟩,
    ⟨checkToken_refuses_raw_opener⟩, ⟨checkToken_allows_custom_error⟩,
    ⟨checkToken_meets⟩, ⟨checkToken_fulfilled⟩
  ]

def collectRangesRequired : Required collectRangesDeliverable where
  theorems := [
    ⟨collectRanges_o2⟩, ⟨collectRanges_o2Run⟩, ⟨collectRanges_o3⟩,
    ⟨collectRanges_o4⟩, ⟨collectRanges_o5⟩, ⟨collectRanges_not_o5_eq⟩,
    ⟨collectRanges_healthy_owed⟩, ⟨collectRanges_healthy_nonempty⟩,
    ⟨@collectRefusal_contradicts_healthy⟩, ⟨collectRanges_negative_external_model⟩,
    ⟨collect_reason_classified⟩, ⟨collectRanges_oPair_whole⟩,
    ⟨collectRanges_perInput_pairOf⟩, ⟨collectRanges_perInput_table_attack⟩,
    ⟨collectRanges_interim_const_fails⟩, ⟨diff_collectRanges_plainDocComment⟩,
    ⟨collectRanges_healthy_entailment⟩, ⟨collectRanges_allows_custom_error⟩,
    ⟨collectRanges_meets⟩, ⟨collectRanges_fulfilled⟩
  ]

def sourceOrderRequired : Required sourceOrderDeliverable where
  theorems := [
    ⟨sourceOrder_o2⟩, ⟨sourceOrder_o2Run⟩, ⟨sourceOrder_o3⟩,
    ⟨sourceOrder_o4⟩, ⟨sourceOrder_o5⟩, ⟨sourceOrder_interim_const_fails⟩,
    ⟨sourceOrder_oPair_whole⟩, ⟨sourceOrder_meets_iff⟩,
    ⟨sourceOrder_members_recorded⟩, ⟨sourceOrder_meets⟩, ⟨sourceOrder_fulfilled⟩
  ]

def distinctCommentLinesRequired : Required distinctCommentLinesDeliverable where
  theorems := [
    ⟨distinctCommentLines_o2⟩, ⟨distinctCommentLines_o2Run⟩, ⟨distinctCommentLines_o3⟩,
    ⟨distinctCommentLines_o4⟩, ⟨distinctCommentLines_o5⟩,
    ⟨distinctCommentLines_oPair_whole⟩, ⟨distinct_perInput_pairOf⟩,
    ⟨distinct_perInput_oPair_table⟩, ⟨distinctCommentLines_verdicts⟩,
    ⟨distinctCommentLines_witnesses_whole⟩, ⟨distinctLines_equiv_of_pos⟩,
    ⟨diff_distinctLines_zero_line⟩, ⟨distinctCommentLines_empty_zero⟩,
    ⟨distinctCommentLines_meets⟩, ⟨distinctCommentLines_fulfilled⟩
  ]

def firstOutOfOrderRequired : Required firstOutOfOrderDeliverable where
  theorems := [
    ⟨firstOutOfOrder_o2⟩, ⟨firstOutOfOrder_o2Run⟩, ⟨firstOutOfOrder_o3⟩,
    ⟨firstOutOfOrder_o4⟩, ⟨firstOutOfOrder_o5⟩,
    ⟨firstOutOfOrder_oPair_whole⟩, ⟨firstOutOfOrder_verdicts⟩,
    ⟨firstOutOfOrder_witnesses_whole⟩, ⟨firstOutOfOrder_meets_iff⟩,
    ⟨firstOutOfOrder_nil_none⟩, ⟨firstOutOfOrder_meets⟩, ⟨firstOutOfOrder_fulfilled⟩
  ]

def sortFingerprintsRequired : Required sortFingerprintsDeliverable where
  theorems := [
    ⟨sortFingerprints_o2⟩, ⟨sortFingerprints_o2Run⟩, ⟨sortFingerprints_o3⟩,
    ⟨sortFingerprints_o4⟩, ⟨sortFingerprints_o5⟩,
    ⟨sortFingerprints_interim_const_fails⟩, ⟨sortFingerprints_oPair_whole⟩,
    ⟨sortFingerprints_meets_iff⟩, ⟨sortFingerprints_sorted⟩,
    ⟨sortFingerprints_meets⟩, ⟨sortFingerprints_fulfilled⟩
  ]

def missingFromRequired : Required missingFromDeliverable where
  theorems := [
    ⟨missingFrom_o2⟩, ⟨missingFrom_o2Run⟩, ⟨missingFrom_o3⟩,
    ⟨missingFrom_o4⟩, ⟨missingFrom_o5⟩, ⟨missingFrom_not_o5_eq⟩,
    ⟨missingFrom_interim_degenerate⟩, ⟨missingFrom_oPair_whole⟩,
    ⟨missingFrom_meets_iff⟩, ⟨missingFrom_self_empty⟩,
    ⟨missingFrom_allows_unsorted_output⟩, ⟨missingFrom_meets⟩, ⟨missingFrom_fulfilled⟩
  ]

def parseConfigRequired : Required parseConfigDeliverable where
  theorems := [
    ⟨parseConfig_o2_of_oracle⟩, ⟨parseConfig_o2Run⟩, ⟨parseConfig_o3_of_oracle⟩,
    ⟨parseConfig_o4⟩, ⟨parseConfig_o5⟩, ⟨parseConfig_not_o5_eq_of_oracle⟩,
    ⟨parseConfig_oPair_whole⟩, ⟨parseConfig_perInput_pairOf⟩,
    ⟨parseConfig_perInput_table_attack⟩, ⟨parseConfig_interim_const_fails_of_oracle⟩,
    ⟨parseConfig_healthy_nonempty_of_oracle⟩, ⟨parseConfig_healthy_owed⟩,
    ⟨@validConfigJson_and_refusal_disjoint⟩,
    ⟨parseConfig_negative_external_model_of_oracle⟩, ⟨parseConfig_reason_classified⟩,
    ⟨diff_parseConfig_cleanCtrl⟩, ⟨parseConfig_healthy_entailment⟩,
    ⟨parseConfig_allows_custom_error⟩, ⟨parseConfigJson_meets⟩, ⟨parseConfigJson_fulfilled⟩
  ]

def classifyFileRequired : Required classifyFileDeliverable where
  theorems := [
    ⟨classifyFile_o2⟩, ⟨classifyFile_o2Run⟩, ⟨classifyFile_o3⟩,
    ⟨classifyFile_o4⟩, ⟨classifyFile_o5⟩, ⟨classifyFile_not_o5_eq⟩,
    ⟨classifyFile_oPair_whole⟩, ⟨classifyFile_perInput_pairOf⟩,
    ⟨classifyFile_perInput_table_attack⟩, ⟨classifyFile_interim_const_fails⟩,
    ⟨classifyFile_healthy_nonempty⟩, ⟨classifyFile_healthy_owed⟩,
    ⟨classifyFile_negative_external_model⟩, ⟨classifyFile_reason_classified⟩,
    ⟨diff_classifyFile_segmentPrefix⟩, ⟨classifyFile_healthy_entailment⟩,
    ⟨classifyFile_allows_custom_error⟩, ⟨classifyFile_meets⟩, ⟨classifyFile_fulfilled⟩
  ]

def classifyTrackedRequired : Required classifyTrackedDeliverable where
  theorems := [
    ⟨classifyTracked_o2⟩, ⟨classifyTracked_o2Run⟩, ⟨classifyTracked_o3⟩,
    ⟨classifyTracked_o4⟩, ⟨classifyTracked_o5⟩, ⟨classifyTracked_not_o5_eq⟩,
    ⟨classifyTracked_oPair_whole⟩, ⟨classifyTracked_perInput_pairOf⟩,
    ⟨classifyTracked_perInput_table_attack⟩, ⟨classifyTracked_interim_const_fails⟩,
    ⟨classifyTracked_healthy_nonempty⟩, ⟨classifyTracked_healthy_owed⟩,
    ⟨classifyTracked_negative_external_model⟩, ⟨classifyTracked_reason_classified⟩,
    ⟨classifyTracked_healthy_entailment⟩, ⟨classifyTracked_allows_custom_error⟩,
    ⟨classifyTrackedFiles_meets⟩, ⟨classifyTrackedFiles_fulfilled⟩
  ]

def analyzeCommentsRequired : Required analyzeCommentsDeliverable where
  theorems := [
    ⟨analyzeComments_o2⟩, ⟨analyzeComments_o2Run⟩, ⟨analyzeComments_o3⟩,
    ⟨analyzeComments_o4⟩, ⟨analyzeComments_o5⟩,
    ⟨analyzeComments_oPair_whole⟩, ⟨analyzeComments_perInput_pairOf⟩,
    ⟨analyzeComments_perInput_table_attack⟩, ⟨analyzeComments_interim_const_fails⟩,
    ⟨analyzeComments_equiv_of_pos⟩, ⟨analyzeComments_preserves_file⟩,
    ⟨analyzeComments_meets⟩, ⟨analyzeComments_fulfilled⟩
  ]

def parseRatchetRequired : Required parseRatchetDeliverable where
  theorems := [
    ⟨parseRatchet_o2_of_oracle⟩, ⟨parseRatchet_o2Run⟩, ⟨parseRatchet_o3_of_oracle⟩,
    ⟨parseRatchet_o4⟩, ⟨parseRatchet_o5⟩, ⟨parseRatchet_not_o5_eq_of_oracle⟩,
    ⟨parseRatchet_oPair_whole⟩, ⟨parseRatchet_perInput_pairOf⟩,
    ⟨parseRatchet_perInput_table_attack⟩, ⟨parseRatchet_interim_const_fails_of_oracle⟩,
    ⟨parseRatchet_healthy_nonempty_of_oracle⟩, ⟨parseRatchet_healthy_owed⟩,
    ⟨@validRatchetJson_and_refusal_disjoint⟩,
    ⟨parseRatchet_negative_external_model_of_oracle⟩, ⟨parseRatchet_reason_classified⟩,
    ⟨parseRatchet_healthy_entailment⟩, ⟨parseRatchet_allows_custom_error⟩,
    ⟨parseRatchetJson_meets⟩, ⟨parseRatchetJson_fulfilled⟩
  ]

def checkExactSyncRequired : Required checkExactSyncDeliverable where
  theorems := [
    ⟨checkExactSync_o2⟩, ⟨checkExactSync_o2Run⟩, ⟨checkExactSync_o3⟩,
    ⟨checkExactSync_o4⟩, ⟨checkExactSync_o5⟩, ⟨checkExactSync_not_o5_eq⟩,
    ⟨checkExactSync_oPair_whole⟩, ⟨checkExactSync_perInput_pairOf⟩,
    ⟨checkExactSync_perInput_table_attack⟩, ⟨checkExactSync_interim_const_fails⟩,
    ⟨checkExactSync_healthy_nonempty⟩, ⟨checkExactSync_healthy_owed⟩,
    ⟨checkExactSync_negative_external_model⟩, ⟨checkExactSync_meets_iff⟩,
    ⟨checkExactSync_accepts_sync⟩, ⟨checkExactSync_allows_custom_error⟩,
    ⟨checkExactSync_meets⟩, ⟨checkExactSync_fulfilled⟩
  ]

def checkMonotonicFileRequired : Required checkMonotonicFileDeliverable where
  theorems := [
    ⟨checkMonotonicFile_o2⟩, ⟨checkMonotonicFile_o2Run⟩, ⟨checkMonotonicFile_o3⟩,
    ⟨checkMonotonicFile_o4⟩, ⟨checkMonotonicFile_o5⟩, ⟨checkMonotonicFile_not_o5_eq⟩,
    ⟨checkMonotonicFile_oPair_whole⟩, ⟨checkMonotonicFile_perInput_pairOf⟩,
    ⟨checkMonotonicFile_perInput_table_attack⟩, ⟨checkMonotonicFile_interim_const_fails⟩,
    ⟨checkMonotonicFile_healthy_nonempty⟩, ⟨checkMonotonicFile_healthy_owed⟩,
    ⟨checkMonotonicFile_negative_external_model⟩, ⟨checkMonotonicFile_meets_iff⟩,
    ⟨checkMonotonicFile_accepts_monotonic⟩, ⟨checkMonotonicFile_allows_custom_error⟩,
    ⟨checkMonotonicFile_meets⟩, ⟨checkMonotonicFile_fulfilled⟩
  ]

def validateCheckRequired : Required validateCheckDeliverable where
  theorems := [
    ⟨validateCheck_o2⟩, ⟨validateCheck_o2Run⟩, ⟨validateCheck_o3⟩,
    ⟨validateCheck_o4⟩, ⟨validateCheck_o5⟩, ⟨validateCheck_not_o5_eq⟩,
    ⟨validateCheck_oPair_whole⟩, ⟨validateCheck_perInput_pairOf⟩,
    ⟨validateCheck_perInput_table_attack⟩, ⟨validateCheck_interim_const_fails⟩,
    ⟨validateCheck_healthy_nonempty⟩, ⟨validateCheck_healthy_owed⟩,
    ⟨@validateOk_and_refusal_disjoint⟩,
    ⟨validateCheck_negative_external_model⟩, ⟨validateCheck_reason_classified⟩,
    ⟨validateCheck_equiv_of_nodup⟩, ⟨diff_validateCheck_duplicate_file⟩,
    ⟨validateCheck_healthy_entailment⟩, ⟨validateCheck_allows_custom_error⟩,
    ⟨validateCheck_meets⟩, ⟨validateCheck_fulfilled⟩
  ]

end NoCommentsSpecification.Required
