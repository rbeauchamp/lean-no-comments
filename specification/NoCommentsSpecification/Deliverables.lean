module

public import LeanIntent.Confirmation
public import NoCommentsSpecification.Explanations

@[expose] public section

namespace NoCommentsSpecification.Deliverables

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreRecords
open NoCommentsSpecification.ConfigRecords
open NoCommentsSpecification.RatchetRecords
open NoCommentsSpecification.Explanations

theorem emptyKeeps {W : Type} (r : IntentRecord W) : Keeps r [] :=
  (keeps_iff r []).mpr fun _ h => nomatch h

theorem singleKeeps {W : Type} {r : IntentRecord W} {a : Answer W} (hk : a.KeptBy r) :
    Keeps r [a] :=
  (keeps_iff r [a]).mpr fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hk
    · exact nomatch hx

def isFingerprintDeliverable : Deliverable IsFingerprintFn where
  record := isFingerprintRecord
  explanation := isFingerprintExplained
  answers := []
  keeps := emptyKeeps _

def fingerprintAnswers : List (Attributed FingerprintFn) :=
  [ ⟨⟨⟨"allows model mapping empty string to zeroFp", .possibility,
      fun f => f "" = AdequacyCore.zeroFp⟩, .confirmed⟩, agentAnswerer⟩ ]

def fingerprintDeliverable : Deliverable FingerprintFn where
  record := fingerprintRecord
  explanation := fingerprintExplained
  answers := fingerprintAnswers
  keeps := singleKeeps fingerprint_allows_zero_empty

def checkTokenAnswers : List (Attributed CheckTokenFn) :=
  [ ⟨⟨⟨"leaves refusal message string unconstrained", .possibility,
      fun f => ∀ ctx tok raw next start, ¬ CoreSpec.TokenSafe ctx tok raw next →
        f ctx tok raw next start = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def checkTokenDeliverable : Deliverable CheckTokenFn where
  record := checkTokenRecord
  explanation := checkTokenExplained
  answers := checkTokenAnswers
  keeps := singleKeeps checkToken_allows_custom_error

def collectRangesAnswers : List (Attributed CollectRangesFn) :=
  [ ⟨⟨⟨"leaves refusal diagnostic wording unconstrained", .possibility,
      fun f => ∀ ranges acc, (¬ ∃ acc', AdequacyCollect.RangesAcc ranges acc acc') →
        f ranges acc = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def collectRangesDeliverable : Deliverable CollectRangesFn where
  record := collectRangesRecord
  explanation := collectRangesExplained
  answers := collectRangesAnswers
  keeps := singleKeeps collectRanges_allows_custom_error

def sourceOrderDeliverable : Deliverable SourceOrderFn where
  record := sourceOrderRecord
  explanation := sourceOrderExplained
  answers := []
  keeps := emptyKeeps _

def distinctCommentLinesDeliverable : Deliverable DistinctLinesFn where
  record := distinctCommentLinesRecord
  explanation := distinctCommentLinesExplained
  answers := []
  keeps := emptyKeeps _

def firstOutOfOrderDeliverable : Deliverable FirstOutOfOrderFn where
  record := firstOutOfOrderRecord
  explanation := firstOutOfOrderExplained
  answers := []
  keeps := emptyKeeps _

def sortFingerprintsDeliverable : Deliverable SortFingerprintsFn where
  record := sortFingerprintsRecord
  explanation := sortFingerprintsExplained
  answers := []
  keeps := emptyKeeps _

def missingFromAnswers : List (Attributed MissingFromFn) :=
  [ ⟨⟨⟨"leaves output ordering unconstrained up to permutation", .possibility,
      fun f => ∃ xs ys, ¬ (f xs ys).toList.Pairwise (· ≤ ·)⟩, .confirmed⟩, agentAnswerer⟩ ]

def missingFromDeliverable : Deliverable MissingFromFn where
  record := missingFromRecord
  explanation := missingFromExplained
  answers := missingFromAnswers
  keeps := singleKeeps missingFrom_allows_unsorted_output

def parseConfigAnswers : List (Attributed ParseConfigFn) :=
  [ ⟨⟨⟨"leaves refusal error wording free on invalid config JSON", .possibility,
      fun f => f Json.null = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def parseConfigDeliverable : Deliverable ParseConfigFn where
  record := parseConfigRecord
  explanation := parseConfigExplained
  answers := parseConfigAnswers
  keeps := singleKeeps parseConfig_allows_custom_error

def classifyFileAnswers : List (Attributed ClassifyFileFn) :=
  [ ⟨⟨⟨"leaves refusal message string unconstrained on unmatched file", .possibility,
      fun f => f AdequacyConfig.emptyRepoCfg "Foo.lean" = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def classifyFileDeliverable : Deliverable ClassifyFileFn where
  record := classifyFileRecord
  explanation := classifyFileExplained
  answers := classifyFileAnswers
  keeps := singleKeeps classifyFile_allows_custom_error

def classifyTrackedAnswers : List (Attributed ClassifyTrackedFn) :=
  [ ⟨⟨⟨"leaves refusal message string free on unmatched file array", .possibility,
      fun f => f AdequacyConfig.emptyRepoCfg #["Foo.lean"] = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def classifyTrackedDeliverable : Deliverable ClassifyTrackedFn where
  record := classifyTrackedRecord
  explanation := classifyTrackedExplained
  answers := classifyTrackedAnswers
  keeps := singleKeeps classifyTracked_allows_custom_error

def analyzeCommentsDeliverable : Deliverable AnalyzeCommentsFn where
  record := analyzeCommentsRecord
  explanation := analyzeCommentsExplained
  answers := []
  keeps := emptyKeeps _

def parseRatchetAnswers : List (Attributed ParseRatchetFn) :=
  [ ⟨⟨⟨"leaves refusal message string free on invalid ratchet JSON", .possibility,
      fun f => f Json.null = .error "denied"⟩, .confirmed⟩, agentAnswerer⟩ ]

def parseRatchetDeliverable : Deliverable ParseRatchetFn where
  record := parseRatchetRecord
  explanation := parseRatchetExplained
  answers := parseRatchetAnswers
  keeps := singleKeeps parseRatchet_allows_custom_error

def checkExactSyncAnswers : List (Attributed CheckExactSyncFn) :=
  [ ⟨⟨⟨"leaves error array contents unconstrained on sync mismatch", .possibility,
      fun f => (f AdequacyRatchet.nonEmptyAnalysis none).toList = ["denied"]⟩, .confirmed⟩, agentAnswerer⟩ ]

def checkExactSyncDeliverable : Deliverable CheckExactSyncFn where
  record := checkExactSyncRecord
  explanation := checkExactSyncExplained
  answers := checkExactSyncAnswers
  keeps := singleKeeps checkExactSync_allows_custom_error

def checkMonotonicFileAnswers : List (Attributed CheckMonotonicFn) :=
  [ ⟨⟨⟨"leaves error array contents unconstrained on regression", .possibility,
      fun f => (f "Foo.lean" Core.SortedFingerprints.empty 0 1 none).toList = ["denied"]⟩, .confirmed⟩, agentAnswerer⟩ ]

def checkMonotonicFileDeliverable : Deliverable CheckMonotonicFn where
  record := checkMonotonicFileRecord
  explanation := checkMonotonicFileExplained
  answers := checkMonotonicFileAnswers
  keeps := singleKeeps checkMonotonicFile_allows_custom_error

def validateCheckAnswers : List (Attributed ValidateCheckFn) :=
  [ ⟨⟨⟨"leaves refusal error wording unconstrained on missing target", .possibility,
      fun f => f #[] #[] #[] AdequacyRatchet.emptyRatchetMap none (some "Foo.lean") = .error "denied"⟩,
      .confirmed⟩, agentAnswerer⟩ ]

def validateCheckDeliverable : Deliverable ValidateCheckFn where
  record := validateCheckRecord
  explanation := validateCheckExplained
  answers := validateCheckAnswers
  keeps := singleKeeps validateCheck_allows_custom_error

end NoCommentsSpecification.Deliverables
