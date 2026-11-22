module

public import LeanIntent.Explain
public import NoCommentsSpecification.CoreRecords
public import NoCommentsSpecification.ConfigRecords
public import NoCommentsSpecification.RatchetRecords
public import NoCommentsSpecification.AdequacyCore
public import NoCommentsSpecification.AdequacyCollect
public import NoCommentsSpecification.AdequacyConfig
public import NoCommentsSpecification.AdequacyRatchet

@[expose] public section

namespace NoCommentsSpecification.Explanations

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreSpec
open NoCommentsSpecification.CoreRecords
open NoCommentsSpecification.ConfigSpec
open NoCommentsSpecification.ConfigRecords
open NoCommentsSpecification.RatchetSpec
open NoCommentsSpecification.RatchetRecords
open NoCommentsSpecification.AdequacyCore
open NoCommentsSpecification.AdequacyCollect
open NoCommentsSpecification.AdequacyConfig
open NoCommentsSpecification.AdequacyRatchet

def ownerId : LeanIntent.Ident := .of "rbeauchamp"

def agentId : LeanIntent.Ident := .of "antigravity"

def agentDelegationId : LeanIntent.Ident := .of "agent-delegation"

def ownerStanding : Restatement := .confirmed ownerId

def agentReason : String :=
  "Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22."

def agentAnswerer : Answerer := .onBehalf agentId agentDelegationId agentReason

theorem isFingerprint_refuses_empty :
    ∀ f : IsFingerprintFn, isFingerprintRecord.Meets f → f "" = false := by
  intro f hf
  cases h : f "" with
  | false => rfl
  | true =>
    exfalso
    exact not_isFp_empty ((hf.2 _ List.mem_cons_self "").mp h)

theorem isFingerprint_accepts_zero :
    ∀ f : IsFingerprintFn, isFingerprintRecord.Meets f → f zeroFp = true := by
  intro f hf
  exact (hf.2 _ List.mem_cons_self zeroFp).mpr zeroFp_valid

def isFingerprintExplained : Explanation isFingerprintRecord where
  shape :=
    { requires := "isFingerprint is a total pure function from String to Bool."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type String -> Bool until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns true iff the string has length 16 and every character is lowercase hex ('0'-'9' or 'a'-'f')."
      rulesOut := "Empty strings, wrong lengths, uppercase hex letters, and non-hex characters."
      allows := "Only exact 16-character lowercase hex digests."
      freedom := "Fixes the Boolean output on every input string (O5 .eq)." } ]
  vocab := [
    { requires := "IsFingerprint holds iff s has UTF-8/list length 16 and all characters satisfy isHexLowerChar."
      rulesOut := "Strings of length other than 16 or containing uppercase or non-hex characters."
      allows := "Any 16-character lowercase hexadecimal string."
      freedom := "Predicate definition; fixes membership on all strings." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"refuses empty string", .entailment, fun f => f "" = false⟩
      holds := isFingerprint_refuses_empty
      gloss :=
        { requires := "Any subject meeting isFingerprintRecord returns false on empty string."
          rulesOut := "Vacuous acceptance of the empty string."
          allows := "Any valid recognizer."
          freedom := "Fixed to false on \"\"." }
      settled := .derived },
    { consequence := ⟨"accepts sixteen-zero fingerprint", .entailment, fun f => f zeroFp = true⟩
      holds := isFingerprint_accepts_zero
      gloss :=
        { requires := "Any subject meeting isFingerprintRecord returns true on zeroFp."
          rulesOut := "Constant-false recognizers."
          allows := "Any valid recognizer."
          freedom := "Fixed to true on zeroFp." }
      settled := .derived } ]

theorem fingerprint_nonconstant :
    ∀ f : FingerprintFn, fingerprintRecord.Meets f → ∃ a b : String, f a ≠ f b := by
  intro f hf
  exact hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem fingerprint_allows_zero_empty :
    ∃ f : FingerprintFn, fingerprintRecord.Meets f ∧ f "" = zeroFp :=
  ⟨fpModel, fpModel_meets, rfl⟩

def fingerprintExplained : Explanation fingerprintRecord where
  shape :=
    { requires := "fingerprint is a total pure function from String to String."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type String -> String until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Every output satisfies IsFingerprint (16 lowercase hex characters)."
      rulesOut := "Hashes of wrong length, uppercase hex, or non-hex characters."
      allows := "Any 16-char lowercase hex digest family."
      freedom := "Any valid hex digest value on each input." },
    { requires := "Exists at least one pair of inputs mapped to distinct outputs."
      rulesOut := "Constant hash functions collapsing all inputs to one digest."
      allows := "Non-trivial hash functions such as 64-bit FNV-1a."
      freedom := "Specific digest collisions or algorithm choice beyond non-constancy remain open." } ]
  vocab := [
    { requires := "IsFingerprint holds iff length is 16 and all characters are lowercase hex."
      rulesOut := "Malformed digest strings."
      allows := "16-char lowercase hex strings."
      freedom := "Fixes valid digest syntax." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"non-constant digest output", .entailment, fun f => ∃ a b : String, f a ≠ f b⟩
      holds := fingerprint_nonconstant
      gloss :=
        { requires := "Exists at least two strings whose digests differ."
          rulesOut := "Constant functions."
          allows := "Any non-constant 16-hex digest function."
          freedom := "Exact hash algorithm left open within valid digests." }
      settled := .derived },
    { consequence := ⟨"allows model mapping empty string to zeroFp", .possibility, fun f => f "" = zeroFp⟩
      holds := fingerprint_allows_zero_empty
      gloss :=
        { requires := "Some conforming digest function maps \"\" to zeroFp."
          rulesOut := "Nothing; documents hash-value freedom."
          allows := "Alternative 16-hex digest implementations besides FNV-1a."
          freedom := "Specific digest mapping is delegated below owner level (not O5 .eq)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem checkToken_healthy_entailment :
    ∀ f : CheckTokenFn, checkTokenRecord.Meets f →
      ∀ ctx tok raw next start, Healthy.Token ctx tok raw next → f ctx tok raw next start = .ok () := by
  intro f hf ctx tok raw next start hh
  obtain ⟨_, h⟩ := checkToken_healthy_owed f ctx tok raw next start hf hh
  exact h

theorem checkToken_refuses_raw_opener :
    ∀ f : CheckTokenFn, checkTokenRecord.Meets f →
      ∀ ctx tok next start,
        literalToken ctx.env tok "--" = false →
        registeredSymbol ctx tok = false →
        ∃ msg, f ctx tok "--" next start = .error msg := by
  intro f hf ctx tok next start hlit hsym
  cases h : f ctx tok "--" next start with
  | error msg => exact ⟨msg, rfl⟩
  | ok u =>
    exfalso
    rcases hf.2 _ List.mem_cons_self ctx tok "--" next start h with h1 | h1 | ⟨hno, _⟩
    · rw [hlit] at h1; contradiction
    · rw [hsym] at h1; contradiction
    · rw [containsOpener_dash] at hno; contradiction

noncomputable def checkTokenDeniedModel : CheckTokenFn :=
  open Classical in
  fun ctx tok raw next _ => if TokenSafe ctx tok raw next then .ok () else .error "denied"

theorem checkTokenDeniedModel_meets : checkTokenRecord.Meets checkTokenDeniedModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ctx tok raw next start hok
    dsimp [checkTokenDeniedModel] at hok
    split at hok
    · assumption
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ctx tok raw next start msg herr
    dsimp [checkTokenDeniedModel] at herr
    split at herr
    · contradiction
    · rename_i hns
      rcases tokenSafe_dichotomy ctx tok raw next with hs | hr
      · exact absurd hs hns
      · exact hr
  exact nomatch hp

theorem checkToken_allows_custom_error :
    ∃ f : CheckTokenFn, checkTokenRecord.Meets f ∧
      (∀ ctx tok raw next start, ¬ TokenSafe ctx tok raw next → f ctx tok raw next start = .error "denied") := by
  refine ⟨checkTokenDeniedModel, checkTokenDeniedModel_meets, fun ctx tok raw next start hns => ?_⟩
  dsimp [checkTokenDeniedModel]
  split
  · contradiction
  · rfl

def checkTokenExplained : Explanation checkTokenRecord where
  shape :=
    { requires := "checkToken is a total pure function from ParserContextCore, Syntax, String, Char, and Pos.Raw to Except String Unit."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns .ok () only when TokenSafe holds of the token, raw slice, and lookahead char."
      rulesOut := "Accepting unparsed atoms or forged identifiers containing '--' or '/-' or crossing '-' opener boundaries."
      allows := "Safe atoms/whitespace, registered symbols, and round-tripping string/char/ident/interpolation literals."
      freedom := "Start position does not restrict acceptance beyond literal checks." },
    { requires := "Returns .error only when TokenRefusal holds."
      rulesOut := "False refusal of healthy tokens."
      allows := "Refusal of unsafe comment-smuggling tokens with any diagnostic error message."
      freedom := "Error string wording is left free." } ]
  vocab := [
    { requires := "TokenSafe holds iff token is a round-tripping literal, registered symbol, or opener/boundary-free."
      rulesOut := "Raw slices containing or crossing comment openers unless legitimately parsed."
      allows := "Legitimate literals, registered symbols, and safe raw tokens."
      freedom := "Defines exact token safety." },
    { requires := "TokenRefusal holds iff neither literal nor registered symbol and opener or boundary-crossing occurs."
      rulesOut := "Safe literals and registered symbols."
      allows := "Genuine opener-smuggling non-literal tokens."
      freedom := "Disjoint complement of TokenSafe." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"accepts all healthy tokens", .entailment,
        fun f => ∀ ctx tok raw next start, Healthy.Token ctx tok raw next → f ctx tok raw next start = .ok ()⟩
      holds := checkToken_healthy_entailment
      gloss :=
        { requires := "Every healthy token returns .ok ()."
          rulesOut := "Spurious token refusals on valid Lean code."
          allows := "Any conforming token checker."
          freedom := "Success verdict fixed on healthy inputs." }
      settled := .derived },
    { consequence := ⟨"refuses non-literal non-symbol '--' opener", .entailment,
        fun f => ∀ (ctx : Parser.ParserContextCore) (tok : Syntax) (next : Char) (start : String.Pos.Raw),
          literalToken ctx.env tok "--" = false →
          registeredSymbol ctx tok = false → ∃ msg, f ctx tok "--" next start = .error msg⟩
      holds := checkToken_refuses_raw_opener
      gloss :=
        { requires := "Refuses raw '--' whenever it is neither a literal nor a registered symbol."
          rulesOut := "Silent pass on '--' comment smuggling."
          allows := "Any error diagnostic string."
          freedom := "Diagnostic text left open." }
      settled := .derived },
    { consequence := ⟨"leaves refusal message string unconstrained", .possibility,
        fun f => ∀ ctx tok raw next start, ¬ TokenSafe ctx tok raw next → f ctx tok raw next start = .error "denied"⟩
      holds := checkToken_allows_custom_error
      gloss :=
        { requires := "Some conforming checker reports \"denied\" on every unsafe token."
          rulesOut := "Nothing; establishes refusal-message freedom."
          allows := "Independent diagnostic message formatting."
          freedom := "Refusal string format decided below owner level (O5 CheckTokenFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem collectRanges_healthy_entailment :
    ∀ f : CollectRangesFn, collectRangesRecord.Meets f →
      ∀ ranges acc, Healthy.Collect ranges acc → ∃ acc', f ranges acc = .ok acc' :=
  fun f hf ranges acc hh => collectRanges_healthy_owed f ranges acc hf hh

theorem collectRanges_allows_custom_error :
    ∃ f : CollectRangesFn, collectRangesRecord.Meets f ∧
      (∀ ranges acc, (¬ ∃ acc', RangesAcc ranges acc acc') → f ranges acc = .error "denied") := by
  refine ⟨collectRangesModelWith "denied", collectRangesModelWith_meets "denied", fun ranges acc hna => ?_⟩
  simp only [collectRangesModelWith]
  split
  · contradiction
  · rfl

def collectRangesExplained : Explanation collectRangesRecord where
  shape :=
    { requires := "collectRanges is a total pure function from List CommandRange and CommentAcc to Except String CommentAcc."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Preserves every span previously recorded in acc.spans."
      rulesOut := "Dropping earlier command comment spans across ranges."
      allows := "Accumulating additional spans across ranges."
      freedom := "Accumulation order." },
    { requires := "Accounts for every byte in contiguous ranges from start to endPos."
      rulesOut := "Skipped byte gaps between parsed commands."
      allows := "Leaf tokens, comments, and whitespace covering every byte."
      freedom := "Choice of valid decomposition." },
    { requires := "Accounts for every byte inside each individual command range."
      rulesOut := "Unchecked slices inside command ranges."
      allows := "ByteAccounted partitions."
      freedom := "Valid span keys." },
    { requires := "Every newly added span comes from a genuine comment within some range."
      rulesOut := "Fabricated comment spans not present in parsed ranges/trivia."
      allows := "All authentic line, block, doc, module-doc, and plainDocComment spans."
      freedom := "Non-conflicting span fingerprints." },
    { requires := "Returns .error only when CollectRefusal holds."
      rulesOut := "False failures on healthy command ranges."
      allows := "Refusal on unsafe tokens, unclosed comments, bounds errors, or conflicts."
      freedom := "Exact error diagnostic text." } ]
  vocab := [
    { requires := "ByteAccounted partitions bytes across safe original leaves, comment spans, and whitespace."
      rulesOut := "Unaccounted non-whitespace gaps."
      allows := "Complete byte coverage."
      freedom := "Byte classification vocabulary." },
    { requires := "GenuineCommentSpan witnesses an actual syntax/trivia comment in the input."
      rulesOut := "Spurious spans."
      allows := "Authentic comment spans."
      freedom := "Valid fingerprint details." },
    { requires := "CollectRefusal witnesses malformed bounds, unclosed block comments, unsafe tokens, or conflicts."
      rulesOut := "Healthy range sequences."
      allows := "Sound refusal causes."
      freedom := "Disjoint from Healthy.Collect." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"succeeds on every healthy range list", .entailment,
        fun f => ∀ ranges acc, Healthy.Collect ranges acc → ∃ acc', f ranges acc = .ok acc'⟩
      holds := collectRanges_healthy_entailment
      gloss :=
        { requires := "Every healthy range sequence and initial accumulator succeeds."
          rulesOut := "Spurious errors on valid Lean files."
          allows := "Any valid byte-covering accumulator."
          freedom := "Success guaranteed on healthy input." }
      settled := .derived },
    { consequence := ⟨"leaves refusal diagnostic wording unconstrained", .possibility,
        fun f => ∀ ranges acc, (¬ ∃ acc', RangesAcc ranges acc acc') → f ranges acc = .error "denied"⟩
      holds := collectRanges_allows_custom_error
      gloss :=
        { requires := "Some conforming collector returns \"denied\" on every invalid range list."
          rulesOut := "Nothing; establishes error-message freedom."
          allows := "Diagnostic message customization."
          freedom := "Exact error string decided below owner level (O5 CollectRangesFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem sourceOrder_members_recorded :
    ∀ f : SourceOrderFn, sourceOrderRecord.Meets f →
      ∀ (acc : Core.CommentAcc) (c : Core.Comment),
        c ∈ (f acc).toList → ∃ (sb eb : Nat), acc.spans[sb]? = some (eb, c) := by
  intro f hf acc c hc
  obtain ⟨entries, _, hiff, hmap⟩ := hf.2 _ List.mem_cons_self acc
  rw [hmap, List.mem_map] at hc
  obtain ⟨⟨sb, eb, c'⟩, hm, rfl⟩ := hc
  exact ⟨sb, eb, (hiff sb eb c').mp hm⟩

def sourceOrderExplained : Explanation sourceOrderRecord where
  shape :=
    { requires := "sourceOrder is a total pure function from CommentAcc to Array Comment."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type CommentAcc -> Array Comment until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Produces strictly ascending byte-start ordering matching all spans in acc.spans."
      rulesOut := "Dropped spans, duplicated spans, or out-of-order outputs."
      allows := "Only the exact ascending list of accumulated comments."
      freedom := "None: uniquely determined (O5 .eq)." } ]
  vocab := [
    { requires := "SourceOrdered relates acc to the strictly sorted array of comments in acc.spans."
      rulesOut := "Unsorted or mismatched collections."
      allows := "Unique sorted array."
      freedom := "Fixes exact output." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"outputs only comments recorded in accumulator", .entailment,
        fun f => ∀ (acc : Core.CommentAcc) (c : Core.Comment),
          c ∈ (f acc).toList → ∃ (sb eb : Nat), acc.spans[sb]? = some (eb, c)⟩
      holds := sourceOrder_members_recorded
      gloss :=
        { requires := "Every emitted comment comes from an entry in acc.spans."
          rulesOut := "Synthesizing extra comments."
          allows := "Exact source-ordered projection."
          freedom := "Deterministically equal (O5 .eq)." }
      settled := .derived } ]

theorem distinctCommentLines_empty_zero :
    ∀ f : DistinctLinesFn, distinctCommentLinesRecord.Meets f → f #[] = 0 := by
  intro f hf
  obtain ⟨ls, _, hm, hlen⟩ := hf.2 _ List.mem_cons_self #[]
  cases ls with
  | nil => exact hlen
  | cons x rest =>
    exfalso
    obtain ⟨c, hc, _⟩ := (hm x).mp List.mem_cons_self
    simp at hc

def distinctCommentLinesExplained : Explanation distinctCommentLinesRecord where
  shape :=
    { requires := "distinctCommentLines is a total pure function from Array Comment to Nat."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type Array Comment -> Nat until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Equals the exact number of distinct lines covered by intervals [startLine, endLine]."
      rulesOut := "Double-counting overlapping spans or under-counting multi-line spans."
      allows := "Only the unique cardinality of the line union."
      freedom := "None: uniquely determined (O5 .eq)." } ]
  vocab := [
    { requires := "DistinctLines holds iff there exists a duplicate-free list of covered line numbers of length n."
      rulesOut := "Incorrect counts or unmerged intervals."
      allows := "Exact union cardinality."
      freedom := "Fixes unique integer output." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"counts zero lines for empty array", .entailment, fun f => f #[] = 0⟩
      holds := distinctCommentLines_empty_zero
      gloss :=
        { requires := "An empty comment array produces 0 covered lines."
          rulesOut := "Non-zero baseline counts."
          allows := "Any valid counter."
          freedom := "Deterministically equal (O5 .eq)." }
      settled := .derived } ]

theorem firstOutOfOrder_nil_none :
    ∀ f : FirstOutOfOrderFn, firstOutOfOrderRecord.Meets f → f [] = none := by
  intro f hf
  exact (hf.2 _ List.mem_cons_self []).1.mpr List.Pairwise.nil

def firstOutOfOrderExplained : Explanation firstOutOfOrderRecord where
  shape :=
    { requires := "firstOutOfOrder is a total pure function from List String to Option String."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type List String -> Option String until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns none iff pairwise sorted; returns some b at the first descending transition a > b."
      rulesOut := "Accepting unsorted ratchet lists or rejecting sorted lists."
      allows := "Only the exact first violating element when unsorted."
      freedom := "None: uniquely determined (O5 .eq)." } ]
  vocab := [
    { requires := "FirstOutOfOrderSpec characterizes none as sorted and some b as the first descent."
      rulesOut := "Non-minimal or misidentified witnesses."
      allows := "Exact witness location."
      freedom := "Fixes unique option result." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"accepts empty fingerprint list", .entailment, fun f => f [] = none⟩
      holds := firstOutOfOrder_nil_none
      gloss :=
        { requires := "Empty list returns none."
          rulesOut := "Spurious out-of-order rejection on empty files."
          allows := "Any valid validator."
          freedom := "Deterministically equal (O5 .eq)." }
      settled := .derived } ]

theorem sortFingerprints_sorted :
    ∀ f : SortFingerprintsFn, sortFingerprintsRecord.Meets f →
      ∀ xs, (f xs).values.toList.Pairwise (· ≤ ·) :=
  fun f _ xs => (f xs).sorted

def sortFingerprintsExplained : Explanation sortFingerprintsRecord where
  shape :=
    { requires := "sortFingerprints is a total pure function from Array String to SortedFingerprints."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type Array String -> SortedFingerprints until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Produces a SortedFingerprints array preserving exact element multiplicities."
      rulesOut := "Dropping duplicate comment fingerprints or altering element counts."
      allows := "Only the unique sorted array with identical multiset counts."
      freedom := "None: uniquely determined (O5 .eq)." } ]
  vocab := [
    { requires := "MultisetEq holds iff every string has identical count in both lists."
      rulesOut := "Deduplication or altered counts."
      allows := "Exact permutations."
      freedom := "Fixes unique sorted copy." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"emits pairwise sorted output", .entailment,
        fun f => ∀ xs, (f xs).values.toList.Pairwise (· ≤ ·)⟩
      holds := sortFingerprints_sorted
      gloss :=
        { requires := "Sorted output invariant always holds."
          rulesOut := "Unsorted fingerprint arrays."
          allows := "Unique sorted array."
          freedom := "Deterministically equal (O5 .eq)." }
      settled := .derived } ]

theorem missingFrom_self_empty :
    ∀ f : MissingFromFn, missingFromRecord.Meets f → ∀ xs, (f xs xs).toList = [] := by
  intro f hf xs
  have hd := hf.2 _ List.mem_cons_self xs xs
  cases hres : (f xs xs).toList with
  | nil => rfl
  | cons a rest =>
    exfalso
    have hcnt := hd a
    rw [hres, List.count_cons, Nat.sub_self] at hcnt
    simp at hcnt

def missingFromUnsortedModel : MissingFromFn :=
  fun xs ys => (ys.values.toList.foldl (fun acc y => acc.erase y) xs.values.toList).reverse.toArray

theorem missingFromUnsortedModel_meets : missingFromRecord.Meets missingFromUnsortedModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro xs ys a
    have h1 := missingFromModel_meets.2 _ List.mem_cons_self xs ys a
    simpa [missingFromUnsortedModel, missingFromModel, List.count_reverse] using h1
  exact nomatch hp

theorem missingFrom_allows_unsorted_output :
    ∃ f : MissingFromFn, missingFromRecord.Meets f ∧ ∃ xs ys, ¬ (f xs ys).toList.Pairwise (· ≤ ·) := by
  let xs : Core.SortedFingerprints :=
    ⟨#[zeroFp, oneFp], List.pairwise_cons.mpr ⟨by simp [zeroFp_le_oneFp], List.pairwise_singleton _ _⟩⟩
  refine ⟨missingFromUnsortedModel, missingFromUnsortedModel_meets, xs, Core.SortedFingerprints.empty, ?_⟩
  intro hpw
  have heq : (missingFromUnsortedModel xs Core.SortedFingerprints.empty).toList = [oneFp, zeroFp] := rfl
  rw [heq, List.pairwise_cons] at hpw
  have hle : oneFp ≤ zeroFp := hpw.1 zeroFp List.mem_cons_self
  have hlt : zeroFp < oneFp := String.toList_lt_toList_iff.mp (by decide)
  exact (Std.not_le.mpr hlt) hle

def missingFromExplained : Explanation missingFromRecord where
  shape :=
    { requires := "missingFrom is a total pure function from two SortedFingerprints to Array String."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Every string occurs exactly (count xs - count ys) times in the output."
      rulesOut := "Ignoring duplicate fingerprint counts or using set difference."
      allows := "Any list ordering preserving exact multiset difference counts."
      freedom := "Permutation equivalence (O5 MissingFromFreedom)." } ]
  vocab := [
    { requires := "MultisetDiff holds iff diff count of every string equals count xs - count ys."
      rulesOut := "Set-based subtraction."
      allows := "Exact multiset subtraction."
      freedom := "Fixes counts, leaves element order free." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"returns empty array when subtracting multiset from itself", .entailment,
        fun f => ∀ xs, (f xs xs).toList = []⟩
      holds := missingFrom_self_empty
      gloss :=
        { requires := "Identical sorted fingerprint multisets yield no missing items."
          rulesOut := "False positives on equal ratchets."
          allows := "Any valid multiset difference."
          freedom := "Always empty on identical arguments." }
      settled := .derived },
    { consequence := ⟨"leaves output ordering unconstrained up to permutation", .possibility,
        fun f => ∃ xs ys, ¬ (f xs ys).toList.Pairwise (· ≤ ·)⟩
      holds := missingFrom_allows_unsorted_output
      gloss :=
        { requires := "Some conforming implementation returns descending output order."
          rulesOut := "Nothing; shows only multiset counts matter."
          allows := "Sorted or reversed difference arrays."
          freedom := "Order freedom decided below owner level (O5 MissingFromFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem parseConfig_healthy_entailment :
    ∀ f : ParseConfigFn, parseConfigRecord.Meets f →
      ∀ text, Healthy.ConfigText text → ∃ cfg, f text = .ok cfg :=
  fun f hf text hh => parseConfig_healthy_owed f text hf hh

theorem parseConfig_allows_custom_error :
    ∃ f : ParseConfigFn, parseConfigRecord.Meets f ∧
      ((∀ j, Json.parse "" ≠ .ok j) → f "" = .error "denied") := by
  refine ⟨parseConfigModelWith "denied", parseConfigModelWith_meets "denied", fun hempty => ?_⟩
  have hna : ¬ ∃ cfg, ValidConfigJson "" cfg := by
    rintro ⟨cfg, hv⟩
    exact validConfigJson_and_refusal_disjoint hv (.badJson hempty)
  dsimp [parseConfigModelWith]
  simp [hna]

def parseConfigExplained : Explanation parseConfigRecord where
  shape :=
    { requires := "parseConfigJson is a total pure function from String to Except String RepoConfig."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of type String -> Except String RepoConfig until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns .ok cfg only when ValidConfigJson holds with normalized paths, allowed keys, and unique dirs."
      rulesOut := "Unknown keys, empty workspace list, duplicate workspace dirs, traversal/backslash/control paths, or blank reasons."
      allows := "Valid normalized RepoConfig values."
      freedom := "Valid normalized field order/hash specifics." },
    { requires := "Returns .error only when ConfigRefusal holds."
      rulesOut := "Rejecting healthy configurations."
      allows := "Refusing invalid config inputs with arbitrary error strings."
      freedom := "Error message wording is left free." } ]
  vocab := [
    { requires := "ValidConfigJson characterizes schema, allowed keys, normalized paths, and non-duplicate dirs."
      rulesOut := "Malformed or unsafe configs."
      allows := "Normalized valid configs."
      freedom := "Exact schema validation." },
    { requires := "ConfigRefusal enumerates every config error cause."
      rulesOut := "Healthy JSON configs."
      allows := "All malformed config inputs."
      freedom := "Disjoint complement of ValidConfigJson." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"succeeds on every healthy configuration string", .entailment,
        fun f => ∀ text, Healthy.ConfigText text → ∃ cfg, f text = .ok cfg⟩
      holds := parseConfig_healthy_entailment
      gloss :=
        { requires := "Any valid healthy config parses to .ok cfg."
          rulesOut := "False config rejections."
          allows := "Any schema-compliant parser."
          freedom := "Success guaranteed on healthy config text." }
      settled := .derived },
    { consequence := ⟨"leaves refusal error wording free on malformed JSON", .possibility,
        fun f => (∀ j, Json.parse "" ≠ .ok j) → f "" = .error "denied"⟩
      holds := parseConfig_allows_custom_error
      gloss :=
        { requires := "Some conforming config parser returns \"denied\" on unparseable empty input."
          rulesOut := "Nothing; establishes refusal-message freedom."
          allows := "Different human-readable error strings."
          freedom := "Error formatting decided below owner level (O5 ParseConfigFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem classifyFile_healthy_entailment :
    ∀ f : ClassifyFileFn, classifyFileRecord.Meets f →
      ∀ cfg p, Healthy.ClassifyInput cfg p → ∃ out, f cfg p = .ok out :=
  fun f hf cfg p hh => classifyFile_healthy_owed f cfg p hf hh

theorem classifyFile_allows_custom_error :
    ∃ f : ClassifyFileFn, classifyFileRecord.Meets f ∧
      f emptyRepoCfg "Foo.lean" = .error "denied" := by
  refine ⟨classifyFileModelWith "denied", classifyFileModelWith_meets "denied", ?_⟩
  have hna : ¬ ∃ out, ClassifyOutcome emptyRepoCfg "Foo.lean" out := by
    rintro ⟨out, h⟩
    exact classifyOutcome_and_refusal_disjoint h emptyRepoCfg_foo_refusal
  dsimp [classifyFileModelWith]
  simp [hna]

def classifyFileExplained : Explanation classifyFileRecord where
  shape :=
    { requires := "classifyFile is a total pure function from RepoConfig and String to Except String ClassifiedFile."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns .ok out only when at most 1 exclude rule and (if unexcluded) exactly 1 workspace matches on segment boundaries."
      rulesOut := "Unowned files, overlapping workspaces, overlapping excludes, or raw non-segment prefix matches."
      allows := "Unique excluded or checked classification with isTool status."
      freedom := "None on outcome value when valid." },
    { requires := "Returns .error only when ClassifyRefusal holds."
      rulesOut := "Rejecting unambiguously owned files."
      allows := "Refusing ambiguous or unmatched files with arbitrary error message."
      freedom := "Error message wording left free." } ]
  vocab := [
    { requires := "ClassifyOutcome specifies unique exclude vs unique workspace ownership using segment PrefixMatches."
      rulesOut := "Ambiguous or unowned paths."
      allows := "Unambiguous ownership."
      freedom := "Unique outcome per file." },
    { requires := "ClassifyRefusal captures ambiguousExclude, unmatched, and ambiguousWorkspace."
      rulesOut := "Unambiguously owned paths."
      allows := "Ownership failures."
      freedom := "Disjoint from ClassifyOutcome." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"classifies every unambiguous healthy file", .entailment,
        fun f => ∀ cfg p, Healthy.ClassifyInput cfg p → ∃ out, f cfg p = .ok out⟩
      holds := classifyFile_healthy_entailment
      gloss :=
        { requires := "Any unambiguously owned file succeeds."
          rulesOut := "False failures on valid file layouts."
          allows := "Any compliant classifier."
          freedom := "Success guaranteed on healthy classification inputs." }
      settled := .derived },
    { consequence := ⟨"leaves refusal message string unconstrained on unmatched file", .possibility,
        fun f => f emptyRepoCfg "Foo.lean" = .error "denied"⟩
      holds := classifyFile_allows_custom_error
      gloss :=
        { requires := "Some conforming classifier returns \"denied\" on an unmatched file."
          rulesOut := "Nothing; establishes error-text freedom."
          allows := "Custom error wording."
          freedom := "Error formatting decided below owner level (O5 ClassifyFileFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem classifyTracked_healthy_entailment :
    ∀ f : ClassifyTrackedFn, classifyTrackedRecord.Meets f →
      ∀ cfg ps, Healthy.ClassifyTrackedInput cfg ps → ∃ out, f cfg ps = .ok out :=
  fun f hf cfg ps hh => classifyTracked_healthy_owed f cfg ps hf hh

theorem classifyTracked_allows_custom_error :
    ∃ f : ClassifyTrackedFn, classifyTrackedRecord.Meets f ∧
      f emptyRepoCfg #["Foo.lean"] = .error "denied" := by
  refine ⟨classifyTrackedModelWith "denied", classifyTrackedModelWith_meets "denied", ?_⟩
  have hna : ¬ ∃ out, ClassifyTrackedOutcome emptyRepoCfg #["Foo.lean"] out := by
    rintro ⟨out, h⟩
    exact classifyTrackedOutcome_and_refusal_disjoint h emptyTracked_refusal
  dsimp [classifyTrackedModelWith]
  simp [hna]

def classifyTrackedExplained : Explanation classifyTrackedRecord where
  shape :=
    { requires := "classifyTrackedFiles is a total pure function from RepoConfig and Array String to Except String (Array ClassifiedFile)."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Maps classifyFile across every tracked file preserving order and array length."
      rulesOut := "Skipping tracked files or reordering classifications."
      allows := "Only the exact in-order array of file classifications."
      freedom := "Choice of which failing file error message is reported first." },
    { requires := "Returns .error only when some tracked file fails ClassifyRefusal."
      rulesOut := "Failing when all tracked files are cleanly owned."
      allows := "Refusal citing any unowned or ambiguous tracked file."
      freedom := "Error wording left free." } ]
  vocab := [
    { requires := "ClassifyTrackedOutcome specifies exact length preservation and per-index ClassifyOutcome."
      rulesOut := "Mismatched lengths or misclassified entries."
      allows := "Exact array correspondence."
      freedom := "Unique outcome array." },
    { requires := "ClassifyTrackedRefusal holds when at least one tracked file hits ClassifyRefusal."
      rulesOut := "Repositories with full clean coverage."
      allows := "Partial or ambiguous coverage inputs."
      freedom := "Disjoint from ClassifyTrackedOutcome." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"succeeds when all tracked files have unambiguous ownership", .entailment,
        fun f => ∀ cfg ps, Healthy.ClassifyTrackedInput cfg ps → ∃ out, f cfg ps = .ok out⟩
      holds := classifyTracked_healthy_entailment
      gloss :=
        { requires := "Healthy tracked file lists always succeed."
          rulesOut := "False failures on fully covered repositories."
          allows := "Any compliant batch classifier."
          freedom := "Success guaranteed on healthy file lists." }
      settled := .derived },
    { consequence := ⟨"leaves refusal message string free on unmatched file array", .possibility,
        fun f => f emptyRepoCfg #["Foo.lean"] = .error "denied"⟩
      holds := classifyTracked_allows_custom_error
      gloss :=
        { requires := "Some conforming batch classifier returns \"denied\"."
          rulesOut := "Nothing; establishes error-message freedom."
          allows := "Any refusal diagnostic."
          freedom := "Error wording decided below owner level (O5 ClassifyTrackedFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem analyzeComments_preserves_file :
    ∀ f : AnalyzeCommentsFn, analyzeCommentsRecord.Meets f →
      ∀ file cs, (f file cs).file = file := by
  intro f hf file cs
  exact (hf.2 _ List.mem_cons_self file cs).1

def analyzeCommentsExplained : Explanation analyzeCommentsRecord where
  shape :=
    { requires := "analyzeComments is a total pure function from String and Array Comment to FileAnalysis."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Preserves file and comments, sets lines to DistinctLines, and sorts fingerprints preserving counts."
      rulesOut := "Wrong file path, wrong distinct line count, or altered fingerprint multiset."
      allows := "Only the canonical sorted FileAnalysis record."
      freedom := "None: uniquely determined (O5 .eq)." } ]
  vocab := [
    { requires := "AnalyzeCommentsSpec requires exact file, comments, DistinctLines, and MultisetEq sorted fingerprints."
      rulesOut := "Misattributed file paths or inaccurate counts."
      allows := "Canonical FileAnalysis."
      freedom := "Unique result." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"preserves analyzed file path", .entailment,
        fun f => ∀ file cs, (f file cs).file = file⟩
      holds := analyzeComments_preserves_file
      gloss :=
        { requires := "Result carries the exact file path argument."
          rulesOut := "Dropping or mutating file names."
          allows := "Exact path preservation."
          freedom := "Deterministically equal (O5 .eq)." }
      settled := .derived } ]

theorem parseRatchet_healthy_entailment :
    ∀ f : ParseRatchetFn, parseRatchetRecord.Meets f →
      ∀ text, Healthy.RatchetText text → ∃ m, f text = .ok m :=
  fun f hf text hh => parseRatchet_healthy_owed f text hf hh

theorem parseRatchet_allows_custom_error :
    ∃ f : ParseRatchetFn, parseRatchetRecord.Meets f ∧
      ((∀ j, Json.parse "" ≠ .ok j) → f "" = .error "denied") := by
  refine ⟨parseRatchetModelWith "denied", parseRatchetModelWith_meets "denied", fun hempty => ?_⟩
  have hna : ¬ ∃ m, ValidRatchetJson "" m := by
    rintro ⟨m, hv⟩
    exact validRatchetJson_and_refusal_disjoint hv (.badJson hempty)
  dsimp [parseRatchetModelWith]
  simp [hna]

def parseRatchetExplained : Explanation parseRatchetRecord where
  shape :=
    { requires := "parseRatchetJson is a total pure function from String to Except String (HashMap String RatchetEntry)."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Accepts only JSON arrays of distinct normalized file entries with positive counts and sorted valid fingerprints."
      rulesOut := "Zero comment/line entries, unsorted fingerprints, duplicate files, unknown keys, or invalid paths/hashes."
      allows := "Canonical HashMap keyed by normalized file path."
      freedom := "HashMap bucket layout." },
    { requires := "Returns .error only when RatchetRefusal holds."
      rulesOut := "Rejecting valid canonical ratchet manifests."
      allows := "Refusing invalid manifests with arbitrary error strings."
      freedom := "Error wording left free." } ]
  vocab := [
    { requires := "ValidRatchetJson enforces schema, normalized paths, positive counts, sorted valid hex digests, and unique files."
      rulesOut := "Empty, unsorted, duplicate, or malformed ratchet entries."
      allows := "Valid ratchet maps."
      freedom := "Exact map lookup equivalence." },
    { requires := "RatchetRefusal enumerates every invalid ratchet input cause."
      rulesOut := "Healthy ratchet manifests."
      allows := "All malformed ratchet JSON inputs."
      freedom := "Disjoint from ValidRatchetJson." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"succeeds on every healthy ratchet manifest", .entailment,
        fun f => ∀ text, Healthy.RatchetText text → ∃ m, f text = .ok m⟩
      holds := parseRatchet_healthy_entailment
      gloss :=
        { requires := "Every healthy ratchet JSON text parses to .ok m."
          rulesOut := "Spurious rejections on valid ratchets."
          allows := "Any compliant ratchet parser."
          freedom := "Success guaranteed on healthy ratchet manifests." }
      settled := .derived },
    { consequence := ⟨"leaves refusal message string free on unparseable JSON", .possibility,
        fun f => (∀ j, Json.parse "" ≠ .ok j) → f "" = .error "denied"⟩
      holds := parseRatchet_allows_custom_error
      gloss :=
        { requires := "Some conforming ratchet parser returns \"denied\" on empty text."
          rulesOut := "Nothing; documents diagnostic message freedom."
          allows := "Custom error messages."
          freedom := "Error text decided below owner level (O5 ParseRatchetFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem checkExactSync_accepts_sync :
    ∀ f : CheckExactSyncFn, checkExactSyncRecord.Meets f →
      ∀ a e, ExactSyncOk a e → (f a e).isEmpty = true := by
  intro f hf a e hs
  exact (hf.2 _ List.mem_cons_self a e).mpr hs

theorem checkExactSync_allows_custom_error :
    ∃ f : CheckExactSyncFn, checkExactSyncRecord.Meets f ∧
      (f nonEmptyAnalysis none).toList = ["denied"] := by
  refine ⟨checkExactSyncModelWith "denied", checkExactSyncModelWith_meets "denied", ?_⟩
  have hnot : ¬ ExactSyncOk nonEmptyAnalysis none := by
    intro ⟨h, _⟩
    simp [nonEmptyAnalysis] at h
  dsimp [checkExactSyncModelWith]
  simp [hnot]

def checkExactSyncExplained : Explanation checkExactSyncRecord where
  shape :=
    { requires := "checkExactSync is a total pure function from FileAnalysis and Option RatchetEntry to Array String."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns an empty error array iff ExactSyncOk holds between live analysis and checked-in entry."
      rulesOut := "Unrecorded comments, stale entries, line-count mismatches, or multiset drift."
      allows := "Empty error array on exact sync; non-empty diagnostics otherwise."
      freedom := "Error string messages when out of sync (O5 CheckExactSyncFreedom)." } ]
  vocab := [
    { requires := "ExactSyncOk requires zero comments/lines when absent, and equal comment/line counts and fingerprint multiset when present."
      rulesOut := "Any comment count, line count, or multiset discrepancy."
      allows := "Exact match."
      freedom := "Fixes pass/fail verdict." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"emits no errors when live comments match ratchet entry", .entailment,
        fun f => ∀ a e, ExactSyncOk a e → (f a e).isEmpty = true⟩
      holds := checkExactSync_accepts_sync
      gloss :=
        { requires := "Exact sync guarantees empty error array."
          rulesOut := "False sync failures."
          allows := "Any compliant sync checker."
          freedom := "Verdict fixed on exact sync." }
      settled := .derived },
    { consequence := ⟨"leaves error array contents unconstrained on sync mismatch", .possibility,
        fun f => (f nonEmptyAnalysis none).toList = ["denied"]⟩
      holds := checkExactSync_allows_custom_error
      gloss :=
        { requires := "Some conforming sync checker returns [\"denied\"] on mismatch."
          rulesOut := "Nothing; establishes error-list freedom."
          allows := "Custom diagnostic arrays."
          freedom := "Diagnostic formatting decided below owner level (O5 CheckExactSyncFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem checkMonotonicFile_accepts_monotonic :
    ∀ f : CheckMonotonicFn, checkMonotonicFileRecord.Meets f →
      ∀ file fps cs ls b, MonotonicOk fps ls b → (f file fps cs ls b).isEmpty = true := by
  intro f hf file fps cs ls b hm
  exact (hf.2 _ List.mem_cons_self file fps cs ls b).mpr hm

theorem checkMonotonicFile_allows_custom_error :
    ∃ f : CheckMonotonicFn, checkMonotonicFileRecord.Meets f ∧
      (f "Foo.lean" Core.SortedFingerprints.empty 0 1 none).toList = ["denied"] := by
  refine ⟨checkMonotonicModelWith "denied", checkMonotonicModelWith_meets "denied", ?_⟩
  have hnot : ¬ MonotonicOk Core.SortedFingerprints.empty 1 none := by
    intro ⟨_, hl⟩
    simp at hl
  dsimp [checkMonotonicModelWith]
  simp [hnot]

def checkMonotonicFileExplained : Explanation checkMonotonicFileRecord where
  shape :=
    { requires := "checkMonotonicFile is a total pure function from path, live fingerprints, live counts, and optional base entry to Array String."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns empty error array iff live fingerprints are a sub-multiset of base and liveLines <= base lines."
      rulesOut := "New or modified comment fingerprints, comment line growth, or comments in files absent from base."
      allows := "Draining comments downward or keeping identical baseline."
      freedom := "Error string messages when regression occurs (O5 CheckMonotonicFreedom)." } ]
  vocab := [
    { requires := "MonotonicOk requires every live fingerprint count <= base count and liveLines <= baseLines."
      rulesOut := "Any added fingerprint or increased line count."
      allows := "Monotonic reduction toward zero."
      freedom := "Fixes exact monotonicity predicate." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"passes when fingerprints and line count do not regress", .entailment,
        fun f => ∀ file fps cs ls b, MonotonicOk fps ls b → (f file fps cs ls b).isEmpty = true⟩
      holds := checkMonotonicFile_accepts_monotonic
      gloss :=
        { requires := "Monotonic inputs always yield empty error array."
          rulesOut := "Blocking valid comment deletions."
          allows := "Any compliant monotonicity checker."
          freedom := "Pass verdict guaranteed when MonotonicOk holds." }
      settled := .derived },
    { consequence := ⟨"leaves error array contents unconstrained on regression", .possibility,
        fun f => (f "Foo.lean" Core.SortedFingerprints.empty 0 1 none).toList = ["denied"]⟩
      holds := checkMonotonicFile_allows_custom_error
      gloss :=
        { requires := "Some conforming checker returns [\"denied\"] when line count grows."
          rulesOut := "Nothing; establishes error-array freedom."
          allows := "Custom diagnostic messages."
          freedom := "Error array formatting decided below owner level (O5 CheckMonotonicFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

theorem validateCheck_healthy_entailment :
    ∀ f : ValidateCheckFn, validateCheckRecord.Meets f →
      ∀ a c e cur b t, Healthy.ValidateInput a c e cur b t → f a c e cur b t = .ok () := by
  intro f hf a c e cur b t hh
  obtain ⟨⟨⟩, h⟩ := validateCheck_healthy_owed f a c e cur b t hf hh
  exact h

theorem validateCheck_allows_custom_error :
    ∃ f : ValidateCheckFn, validateCheckRecord.Meets f ∧
      f #[] #[] #[] emptyRatchetMap none (some "Foo.lean") = .error "denied" := by
  refine ⟨validateCheckModelWith "denied", validateCheckModelWith_meets "denied", ?_⟩
  have hnot : ¬ ValidateOk #[] #[] #[] emptyRatchetMap none (some "Foo.lean") :=
    fun h => validateOk_and_refusal_disjoint h emptyRatchet_missingTarget
  dsimp [validateCheckModelWith]
  simp [hnot]

def validateCheckExplained : Explanation validateCheckRecord where
  shape :=
    { requires := "validateCheck is a total pure function from analyses, file lists, current/base ratchets, and optional target to Except String Unit."
      rulesOut := "Any subject with external side effects, partiality, or another signature."
      allows := "Every pure function of that signature until restricted by properties."
      freedom := "Only fixes the pure function signature." }
  dom := []
  props := [
    { requires := "Returns .ok () only when current/base ratchets contain no excluded/untracked files and target/all analyses satisfy ExactSyncOk and MonotonicOk."
      rulesOut := "Stale excluded entries, dropped file coverage, missing target analysis, out-of-sync manifests, or merge-base regressions."
      allows := "Full repository or single-file passing checks."
      freedom := "Error formatting." },
    { requires := "Returns .error only when ValidateRefusal holds."
      rulesOut := "Rejecting healthy valid checks."
      allows := "Refusing violations with arbitrary error messages."
      freedom := "Error wording left free (O5 ValidateCheckFreedom)." } ]
  vocab := [
    { requires := "ValidateOk enforces current/base coverage invariants and sync + monotonicity over target or all analyses."
      rulesOut := "Coverage holes, excluded ratchet entries, or ratchet regressions."
      allows := "Clean sync and downward-monotonic checks."
      freedom := "Exact overall validation predicate." },
    { requires := "ValidateRefusal enumerates missing targets, excluded/untracked ratchet entries, sync mismatches, and regressions."
      rulesOut := "Healthy passing check inputs."
      allows := "All check failures."
      freedom := "Disjoint from ValidateOk." } ]
  restatement := ownerStanding
  consequences := [
    { consequence := ⟨"passes every healthy check input", .entailment,
        fun f => ∀ a c e cur b t, Healthy.ValidateInput a c e cur b t → f a c e cur b t = .ok ()⟩
      holds := validateCheck_healthy_entailment
      gloss :=
        { requires := "Healthy validation inputs always return .ok ()."
          rulesOut := "False failures on compliant builds."
          allows := "Any conforming check validator."
          freedom := "Success guaranteed on healthy input." }
      settled := .derived },
    { consequence := ⟨"leaves refusal error wording unconstrained on missing target", .possibility,
        fun f => f #[] #[] #[] emptyRatchetMap none (some "Foo.lean") = .error "denied"⟩
      holds := validateCheck_allows_custom_error
      gloss :=
        { requires := "Some conforming validator returns \"denied\" when target analysis is missing."
          rulesOut := "Nothing; establishes error-message freedom."
          allows := "Custom failure diagnostic strings."
          freedom := "Error wording decided below owner level (O5 ValidateCheckFreedom)." }
      settled := .answered agentAnswerer .confirmed } ]

end NoCommentsSpecification.Explanations
