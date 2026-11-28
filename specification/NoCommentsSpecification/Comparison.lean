module

import all Init.Data.String.Search
import all Init.Data.String.Substring
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Lean.Data.Json.Basic
public import Std.Data.HashMap.Lemmas
public import NoCommentsSpecification.BlindSecondModel
public import NoCommentsSpecification.AdequacyCore
public import NoCommentsSpecification.AdequacyCollect
public import NoCommentsSpecification.AdequacyConfig
public import NoCommentsSpecification.AdequacyRatchet

@[expose] public section

namespace NoCommentsSpecification.Comparison

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification

theorem isFingerprint_meets_iff (f : IsFingerprintFn) :
    CoreRecords.isFingerprintRecord.Meets f ↔ BlindSecondModel.isFingerprintRecord.Meets f := by
  have hc : ∀ (c : Char), CoreSpec.isHexLowerChar c = true ↔
      (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')) := fun c => by
    simp [CoreSpec.isHexLowerChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro s
      refine (h.2 _ List.mem_cons_self s).trans ?_
      simp [CoreSpec.IsFingerprint, BlindSecondModel.FingerprintText, hc, String.length_toList]
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro s
      refine (h.2 _ List.mem_cons_self s).trans ?_
      simp [CoreSpec.IsFingerprint, BlindSecondModel.FingerprintText, hc, String.length_toList]
    exact nomatch hp

theorem fingerprint_meets_iff (f : FingerprintFn) :
    CoreRecords.fingerprintRecord.Meets f ↔ BlindSecondModel.fingerprintRecord.Meets f := by
  have hc : ∀ (c : Char), CoreSpec.isHexLowerChar c = true ↔
      (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')) := fun c => by
    simp [CoreSpec.isHexLowerChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro s
      obtain ⟨hl, hcs⟩ := h.2 _ List.mem_cons_self s
      exact ⟨by simpa [String.length_toList] using hl, fun c hm => (hc c).mp (hcs c hm)⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨a, b, hne⟩ := h.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨a, b, fun hab => hne (congrArg f hab), hne⟩
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro s
      obtain ⟨hl, hcs⟩ := h.2 _ List.mem_cons_self s
      exact ⟨by simpa [String.length_toList] using hl, fun c hm => (hc c).mpr (hcs c hm)⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨a, b, _, hne⟩ := h.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨a, b, hne⟩
    exact nomatch hp

theorem firstOutOfOrder_meets_iff (f : FirstOutOfOrderFn) :
    CoreRecords.firstOutOfOrderRecord.Meets f ↔
      BlindSecondModel.firstOutOfOrderRecord.Meets f := by
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs
      obtain ⟨hnone, hsome⟩ := h.2 _ List.mem_cons_self xs
      cases hfx : f xs with
      | none => exact hnone.mp hfx
      | some b =>
        obtain ⟨pre, a, rest, heq, hpw, hlt⟩ := hsome b hfx
        exact ⟨pre, a, rest, by simpa [List.append_assoc] using heq, hpw, hlt⟩
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs
      have hspec := h.2 _ List.mem_cons_self xs
      constructor
      · constructor
        · intro hfx; rw [hfx] at hspec; exact hspec
        · intro hpw
          cases hfx : f xs with
          | none => rfl
          | some b =>
            exfalso
            rw [hfx] at hspec
            obtain ⟨pre, a, rest, rfl, _, hlt⟩ := hspec
            have hpair : a ≤ b := by
              have := List.pairwise_append.mp hpw
              have hr := List.pairwise_cons.mp this.2.1
              exact hr.1 b List.mem_cons_self
            exact (Std.not_lt.mpr hpair) hlt
      · intro b hfx
        rw [hfx] at hspec
        obtain ⟨pre, a, rest, heq, hpw, hlt⟩ := hspec
        exact ⟨pre, a, rest, by simpa [List.append_assoc] using heq, hpw, hlt⟩
    exact nomatch hp

theorem sortFingerprints_meets_iff (f : SortFingerprintsFn) :
    CoreRecords.sortFingerprintsRecord.Meets f ↔
      BlindSecondModel.sortFingerprintsRecord.Meets f := by
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs
      exact ⟨(f xs).sorted, h.2 _ List.mem_cons_self xs⟩
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs
      exact (h.2 _ List.mem_cons_self xs).2
    exact nomatch hp

theorem missingFrom_meets_iff (f : MissingFromFn) :
    CoreRecords.missingFromRecord.Meets f ↔
      BlindSecondModel.missingFromRecord.Meets f := by
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs ys a
      exact h.2 _ List.mem_cons_self xs ys a
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro xs ys a
      exact h.2 _ List.mem_cons_self xs ys a
    exact nomatch hp

theorem pairwise_fst_nodup {α β : Type} [BEq α] [LawfulBEq α] (xs : List (α × β))
    (hp : xs.Pairwise (fun a b => (a.1 == b.1) = false)) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    rw [List.pairwise_cons] at hp
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, ih hp.2⟩
    have := hp.1 x hx
    simp at this

theorem pairwise_lt_fst_nodup {β : Type} (xs : List (Nat × β))
    (hp : xs.Pairwise (fun a b => a.1 < b.1)) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    rw [List.pairwise_cons] at hp
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, ih hp.2⟩
    exact Nat.lt_irrefl _ (hp.1 x hx)

theorem sourceOrder_meets_iff (f : SourceOrderFn) :
    CoreRecords.sourceOrderRecord.Meets f ↔
      BlindSecondModel.sourceOrderRecord.Meets f := by
  have hmemMap : ∀ (acc : Core.CommentAcc) (sb eb : Nat) (c : Core.Comment),
      (sb, (eb, c)) ∈ acc.spans.toList ↔ acc.spans[sb]? = some (eb, c) :=
    fun acc _ _ _ => Std.HashMap.mem_toList_iff_getElem?_eq_some
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro acc
      obtain ⟨entries, hpw, hiff, hmap⟩ := h.2 _ List.mem_cons_self acc
      refine ⟨entries, ?_, hpw, hmap⟩
      refine (List.perm_ext_iff_of_nodup (pairwise_lt_fst_nodup entries hpw)
        (pairwise_fst_nodup acc.spans.toList Std.HashMap.distinct_keys_toList)).mpr ?_
      rintro ⟨sb, eb, c⟩
      exact (hiff sb eb c).trans (hmemMap acc sb eb c).symm
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro acc
      obtain ⟨entries, hperm, hpw, hmap⟩ := h.2 _ List.mem_cons_self acc
      refine ⟨entries, hpw, fun sb eb c => ?_, hmap⟩
      exact (hperm.mem_iff).trans (hmemMap acc sb eb c)
    exact nomatch hp

theorem eraseDups_nodup_len (n : Nat) :
    ∀ (l : List Nat), l.length ≤ n → l.eraseDups.Nodup := by
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [List.eraseDups]
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp [List.eraseDups]
    | cons a as =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih _ ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter] at hm
        simp at hm
      · have hle := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at hl
        omega

theorem distinctLines_equiv_of_pos (comments : Array Core.Comment)
    (hpos : ∀ c ∈ comments.toList, 1 ≤ c.startLine) (n : Nat) :
    CoreSpec.DistinctLines comments n ↔ BlindSecondModel.LineCount comments n := by
  let rawLs := comments.toList.flatMap BlindSecondModel.coveredLines
  let ls := rawLs.eraseDups
  have hnd : ls.Nodup := eraseDups_nodup_len rawLs.length rawLs (Nat.le_refl _)
  have hmem : ∀ l, l ∈ ls ↔ ∃ c ∈ comments.toList, c.startLine ≤ l ∧ l ≤ c.endLine := by
    intro l
    have hcov : ∀ c ∈ comments.toList,
        l ∈ BlindSecondModel.coveredLines c ↔ c.startLine ≤ l ∧ l ≤ c.endLine := by
      intro c hc
      simp only [BlindSecondModel.coveredLines, List.mem_range'_1, Nat.max_eq_right (hpos c hc)]
      omega
    simp only [ls, rawLs, List.mem_eraseDups, List.mem_flatMap]
    constructor
    · rintro ⟨c, hc, hm⟩
      exact ⟨c, hc, (hcov c hc).mp hm⟩
    · rintro ⟨c, hc, hm⟩
      exact ⟨c, hc, (hcov c hc).mpr hm⟩
  constructor
  · rintro ⟨ls1, hnd1, hm1, rfl⟩
    have hperm : ls1.Perm ls :=
      (List.perm_ext_iff_of_nodup hnd1 hnd).mpr fun x => (hm1 x).trans (hmem x).symm
    exact hperm.length_eq
  · intro rfl
    exact ⟨ls, hnd, hmem, rfl⟩

theorem diff_distinctLines_zero_line :
    let cs : Array Core.Comment := #[{ kind := "line", startLine := 0, endLine := 1, fingerprint := AdequacyCore.zeroFp }]
    CoreSpec.DistinctLines cs 2 ∧ BlindSecondModel.LineCount cs 1 := by
  intro cs
  refine ⟨⟨[0, 1], by decide, fun l => ?_, rfl⟩, ?_⟩
  · simp [cs]
    omega
  · simp [BlindSecondModel.LineCount, BlindSecondModel.coveredLines, cs]
    rfl

theorem analyzeComments_equiv_of_pos (file : String) (comments : Array Core.Comment)
    (hpos : ∀ c ∈ comments.toList, 1 ≤ c.startLine) (a : RatchetCore.FileAnalysis) :
    RatchetSpec.AnalyzeCommentsSpec file comments a ↔ BlindSecondModel.AnalysisOf file comments a := by
  simp only [RatchetSpec.AnalyzeCommentsSpec, BlindSecondModel.AnalysisOf,
    BlindSecondModel.SortedCopy, BlindSecondModel.SameCounts, CoreSpec.MultisetEq]
  constructor
  · rintro ⟨hf, hc, hdl, hms⟩
    refine ⟨hf, hc, (distinctLines_equiv_of_pos comments hpos a.lines).mp hdl,
      a.fingerprints.sorted, fun s => by simpa using hms s⟩
  · rintro ⟨hf, hc, hlc, _, hsc⟩
    refine ⟨hf, hc, (distinctLines_equiv_of_pos comments hpos a.lines).mpr hlc,
      fun s => by simpa using hsc s⟩

theorem exactSync_equiv (a : RatchetCore.FileAnalysis)
    (e : Option RatchetCore.RatchetEntry) :
    RatchetSpec.ExactSyncOk a e ↔ BlindSecondModel.ExactSync a e := by
  cases e with
  | none => simp [RatchetSpec.ExactSyncOk, BlindSecondModel.ExactSync, Array.isEmpty]
  | some entry =>
    simp only [RatchetSpec.ExactSyncOk, BlindSecondModel.ExactSync,
      BlindSecondModel.SameCounts, CoreSpec.MultisetEq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩⟩

theorem monotonic_equiv (fps : Core.SortedFingerprints) (ls : Nat)
    (be : Option RatchetCore.RatchetEntry) :
    RatchetSpec.MonotonicOk fps ls be ↔ BlindSecondModel.Monotonic fps ls be := by
  cases be <;> simp [RatchetSpec.MonotonicOk, BlindSecondModel.Monotonic, and_comm]

theorem checkExactSync_meets_iff (f : CheckExactSyncFn) :
    RatchetRecords.checkExactSyncRecord.Meets f ↔
      BlindSecondModel.checkExactSyncRecord.Meets f := by
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro a e
      exact (h.2 _ List.mem_cons_self a e).trans (exactSync_equiv a e)
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro a e
      exact (h.2 _ List.mem_cons_self a e).trans (exactSync_equiv a e).symm
    exact nomatch hp

theorem checkMonotonicFile_meets_iff (f : CheckMonotonicFn) :
    RatchetRecords.checkMonotonicFileRecord.Meets f ↔
      BlindSecondModel.checkMonotonicFileRecord.Meets f := by
  constructor <;> intro h
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro file fps cs ls base
      exact (h.2 _ List.mem_cons_self file fps cs ls base).trans (monotonic_equiv fps ls base)
    exact nomatch hp
  · refine ⟨(fun _ hc => nomatch hc), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro file fps cs ls base
      exact (h.2 _ List.mem_cons_self file fps cs ls base).trans (monotonic_equiv fps ls base).symm
    exact nomatch hp

theorem validateCheck_equiv_of_nodup (analyses : Array RatchetCore.FileAnalysis)
    (checked excluded : Array String)
    (current : Std.HashMap String RatchetCore.RatchetEntry)
    (base? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (target? : Option String)
    (hnd : (analyses.toList.map (·.file)).Nodup) :
    RatchetSpec.ValidateOk analyses checked excluded current base? target? ↔
      BlindSecondModel.ValidCheck analyses checked excluded current base? target? := by
  dsimp [RatchetSpec.ValidateOk, BlindSecondModel.ValidCheck, BlindSecondModel.AnalysisPasses]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun b hb => by rw [hb] at h2; exact h2, ?_⟩
    cases ht : target? with
    | none =>
      rw [ht] at h3
      intro a ha
      obtain ⟨hs, hm⟩ := h3 a ha
      refine ⟨(exactSync_equiv _ _).mp hs, fun b hb => ?_⟩
      rw [hb] at hm
      exact (monotonic_equiv _ _ _).mp hm
    | some target =>
      rw [ht] at h3
      obtain ⟨live, hfind, hs, hm⟩ := h3
      have hmem : live ∈ analyses.toList :=
        Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
      have heq : live.file = target :=
        beq_iff_eq.mp (@Array.find?_some _ (fun (x : RatchetCore.FileAnalysis) => x.file == target) _ _ hfind)
      refine ⟨live, hmem, heq, ?_, fun b hb => ?_⟩
      · rw [heq]
        exact (exactSync_equiv _ _).mp hs
      · rw [hb] at hm
        rw [heq]
        exact (monotonic_equiv _ _ _).mp hm
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · cases hb : base? with
      | none => trivial
      | some b => exact h2 b hb
    · cases ht : target? with
      | none =>
        rw [ht] at h3
        intro a ha
        obtain ⟨hs, hm⟩ := h3 a ha
        refine ⟨(exactSync_equiv _ _).mpr hs, ?_⟩
        cases hb : base? with
        | none => trivial
        | some b => exact (monotonic_equiv _ _ _).mpr (hm b hb)
      | some target =>
        rw [ht] at h3
        obtain ⟨live, hmem, hfile, hs, hm⟩ := h3
        have ⟨live2, hfind2⟩ : ∃ l, analyses.find? (·.file == target) = some l := by
          cases hf : analyses.find? (·.file == target) with
          | some l => exact ⟨l, rfl⟩
          | none =>
            exfalso
            have hne : ∀ x ∈ analyses, ¬ (x.file == target) = true := Array.find?_eq_none.mp hf
            exact hne live (Array.mem_toList_iff.mp hmem) (beq_iff_eq.mpr hfile)
        have heq2 : live2.file = target :=
          beq_iff_eq.mp (@Array.find?_some _ (fun (x : RatchetCore.FileAnalysis) => x.file == target) _ _ hfind2)
        have hmem2 : live2 ∈ analyses.toList :=
          Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind2)
        have hsame : live2 = live := by
          obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp hmem
          obtain ⟨j, hj, hlj⟩ := List.mem_iff_getElem.mp hmem2
          have hij : i = j := by
            by_cases hne : i = j
            · exact hne
            · exfalso
              have hmap_i : (analyses.toList.map (·.file))[i]'(by simpa using hi) = target := by
                simp [hli, hfile]
              have hmap_j : (analyses.toList.map (·.file))[j]'(by simpa using hj) = target := by
                simp [hlj, heq2]
              exact ((AdequacyConfig.list_not_nodup_iff_dup_idx (analyses.toList.map (·.file))).mpr
                ⟨i, j, by simpa using hi, by simpa using hj, hne, hmap_i.trans hmap_j.symm⟩) hnd
          subst hij
          exact hlj.symm.trans hli
        subst hsame
        rw [heq2] at hs
        refine ⟨live2, hfind2, (exactSync_equiv _ _).mpr hs, ?_⟩
        cases hb : base? with
        | none => trivial
        | some b =>
          have hmb := hm b hb
          rw [heq2] at hmb
          exact (monotonic_equiv _ _ _).mpr hmb

theorem diff_validateCheck_duplicate_file :
    let bad : RatchetCore.FileAnalysis := { file := "A.lean", comments := #[AdequacyCore.sampleComment1], lines := 1, fingerprints := ⟨#[AdequacyCore.zeroFp], List.pairwise_singleton _ _⟩ }
    let good : RatchetCore.FileAnalysis := { file := "A.lean", comments := #[], lines := 0, fingerprints := Core.SortedFingerprints.empty }
    let analyses : Array RatchetCore.FileAnalysis := #[bad, good]
    ¬ RatchetSpec.ValidateOk analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean") ∧
      BlindSecondModel.ValidCheck analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean") := by
  intro bad good analyses
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, live, hfind, hs, _⟩
    have : analyses.find? (·.file == "A.lean") = some bad := rfl
    rw [this] at hfind
    cases hfind
    simp [RatchetSpec.ExactSyncOk, AdequacyRatchet.emptyRatchetMap, bad] at hs
  · refine ⟨(fun f e h => by simp [AdequacyRatchet.emptyRatchetMap] at h),
      (fun _ h => by cases h),
      ⟨good, (by dsimp [analyses]; simp), rfl, ?_, (fun _ h => by cases h)⟩⟩
    have hnone : AdequacyRatchet.emptyRatchetMap[good.file]? = none := by
      simp [AdequacyRatchet.emptyRatchetMap]
    rw [hnone]
    exact ⟨rfl, rfl⟩

theorem diff_collectRanges_plainDocComment :
    CoreSpec.docKind ``Parser.Command.plainDocComment = true ∧
      BlindSecondModel.docKind ``Parser.Command.plainDocComment = none := by
  simp [CoreSpec.docKind, BlindSecondModel.docKind]

theorem diff_classifyFile_segmentPrefix :
    let cfg : Config.RepoConfig :=
      { workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
        exclude := #[{ prefix_ := "Foo", reason := "excluded" }]
        ratchet := "comment-ratchet.json" }
    ConfigSpec.ClassifyOutcome cfg "FooBar.lean" (.checked "FooBar.lean" 0 "FooBar.lean" false) ∧
      BlindSecondModel.Classification cfg "FooBar.lean"
        (.excluded "FooBar.lean" { prefix_ := "Foo", reason := "excluded" }) := by
  intro cfg
  refine ⟨?_, ?_⟩
  · dsimp [ConfigSpec.ClassifyOutcome, cfg, ConfigSpec.MatchWorkspace, ConfigSpec.PrefixMatches]
    exact .inr ⟨by simp, cfg.workspaces[0], 0, "FooBar.lean", by simp [cfg], by simp [cfg]⟩
  · dsimp [BlindSecondModel.Classification, cfg]
    exact .inl ⟨{ prefix_ := "Foo", reason := "excluded" }, by simp, rfl⟩

theorem diff_parseConfig_cleanCtrl :
    ConfigSpec.cleanStr "\x01" = true ∧ ¬ BlindSecondModel.CleanText "\x01" := by
  refine ⟨by decide, ?_⟩
  rintro ⟨_, _, hc⟩
  have hmem : Char.ofNat 1 ∈ "\x01".toList := by decide
  have h1 := (hc (Char.ofNat 1) hmem).1
  have hval : (Char.ofNat 1).toNat = 1 := rfl
  omega

theorem diff_checkToken_identMismatch :
    let tok := Syntax.ident .none ⟨"", ⟨0⟩, ⟨0⟩⟩ `x []
    BlindSecondModel.LiteralAt AdequacyCore.emptyCtx tok "--" 0 ∧
      ¬ CoreSpec.TokenSafe AdequacyCore.emptyCtx tok "--" ' ' := by
  intro tok
  refine ⟨.inl trivial, ?_⟩
  rintro (h | h | ⟨hno, _⟩)
  · dsimp [CoreSpec.literalToken, tok] at h
    split at h
    · simp at h
      exact absurd h.1 (by decide)
    · contradiction
  · simp [CoreSpec.registeredSymbol, tok] at h
  · rw [AdequacyCore.containsOpener_dash] at hno
    contradiction

theorem isFingerprint_meets_blind (f : IsFingerprintFn)
    (h : CoreRecords.isFingerprintRecord.Meets f) :
    BlindSecondModel.isFingerprintRecord.Meets f :=
  (isFingerprint_meets_iff f).mp h

theorem isFingerprint_blind_meets (f : IsFingerprintFn)
    (h : BlindSecondModel.isFingerprintRecord.Meets f) :
    CoreRecords.isFingerprintRecord.Meets f :=
  (isFingerprint_meets_iff f).mpr h

theorem fingerprint_meets_blind (f : FingerprintFn)
    (h : CoreRecords.fingerprintRecord.Meets f) :
    BlindSecondModel.fingerprintRecord.Meets f :=
  (fingerprint_meets_iff f).mp h

theorem fingerprint_blind_meets (f : FingerprintFn)
    (h : BlindSecondModel.fingerprintRecord.Meets f) :
    CoreRecords.fingerprintRecord.Meets f :=
  (fingerprint_meets_iff f).mpr h

theorem firstOutOfOrder_meets_blind (f : FirstOutOfOrderFn)
    (h : CoreRecords.firstOutOfOrderRecord.Meets f) :
    BlindSecondModel.firstOutOfOrderRecord.Meets f :=
  (firstOutOfOrder_meets_iff f).mp h

theorem firstOutOfOrder_blind_meets (f : FirstOutOfOrderFn)
    (h : BlindSecondModel.firstOutOfOrderRecord.Meets f) :
    CoreRecords.firstOutOfOrderRecord.Meets f :=
  (firstOutOfOrder_meets_iff f).mpr h

theorem sortFingerprints_meets_blind (f : SortFingerprintsFn)
    (h : CoreRecords.sortFingerprintsRecord.Meets f) :
    BlindSecondModel.sortFingerprintsRecord.Meets f :=
  (sortFingerprints_meets_iff f).mp h

theorem sortFingerprints_blind_meets (f : SortFingerprintsFn)
    (h : BlindSecondModel.sortFingerprintsRecord.Meets f) :
    CoreRecords.sortFingerprintsRecord.Meets f :=
  (sortFingerprints_meets_iff f).mpr h

theorem missingFrom_meets_blind (f : MissingFromFn)
    (h : CoreRecords.missingFromRecord.Meets f) :
    BlindSecondModel.missingFromRecord.Meets f :=
  (missingFrom_meets_iff f).mp h

theorem missingFrom_blind_meets (f : MissingFromFn)
    (h : BlindSecondModel.missingFromRecord.Meets f) :
    CoreRecords.missingFromRecord.Meets f :=
  (missingFrom_meets_iff f).mpr h

theorem sourceOrder_meets_blind (f : SourceOrderFn)
    (h : CoreRecords.sourceOrderRecord.Meets f) :
    BlindSecondModel.sourceOrderRecord.Meets f :=
  (sourceOrder_meets_iff f).mp h

theorem sourceOrder_blind_meets (f : SourceOrderFn)
    (h : BlindSecondModel.sourceOrderRecord.Meets f) :
    CoreRecords.sourceOrderRecord.Meets f :=
  (sourceOrder_meets_iff f).mpr h

theorem checkExactSync_meets_blind (f : CheckExactSyncFn)
    (h : RatchetRecords.checkExactSyncRecord.Meets f) :
    BlindSecondModel.checkExactSyncRecord.Meets f :=
  (checkExactSync_meets_iff f).mp h

theorem checkExactSync_blind_meets (f : CheckExactSyncFn)
    (h : BlindSecondModel.checkExactSyncRecord.Meets f) :
    RatchetRecords.checkExactSyncRecord.Meets f :=
  (checkExactSync_meets_iff f).mpr h

theorem checkMonotonicFile_meets_blind (f : CheckMonotonicFn)
    (h : RatchetRecords.checkMonotonicFileRecord.Meets f) :
    BlindSecondModel.checkMonotonicFileRecord.Meets f :=
  (checkMonotonicFile_meets_iff f).mp h

theorem checkMonotonicFile_blind_meets (f : CheckMonotonicFn)
    (h : BlindSecondModel.checkMonotonicFileRecord.Meets f) :
    RatchetRecords.checkMonotonicFileRecord.Meets f :=
  (checkMonotonicFile_meets_iff f).mpr h

def blindDistinctLinesModel : DistinctLinesFn :=
  fun cs => (cs.toList.flatMap BlindSecondModel.coveredLines).eraseDups.length

theorem distinctCommentLines_separates_blind :
    CoreRecords.distinctCommentLinesRecord.Meets AdequacyCore.distinctLinesModel ∧
      ¬ BlindSecondModel.distinctCommentLinesRecord.Meets AdequacyCore.distinctLinesModel := by
  refine ⟨AdequacyCore.distinctLinesModel_meets, fun hb => ?_⟩
  let cs : Array Core.Comment :=
    #[{ kind := "line", startLine := 0, endLine := 1, fingerprint := AdequacyCore.zeroFp }]
  have hdl := AdequacyCore.distinctLinesModel_meets.2 _ List.mem_cons_self cs
  have hbl := hb.2 _ List.mem_cons_self cs
  have hd := diff_distinctLines_zero_line
  have h2 : AdequacyCore.distinctLinesModel cs = 2 :=
    AdequacyRatchet.distinctLines_unique_val hdl hd.1
  have h1 : AdequacyCore.distinctLinesModel cs = 1 := hbl.trans hd.2.symm
  omega

theorem distinctCommentLines_blind_separates :
    BlindSecondModel.distinctCommentLinesRecord.Meets blindDistinctLinesModel ∧
      ¬ CoreRecords.distinctCommentLinesRecord.Meets blindDistinctLinesModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro cs; rfl
    exact nomatch hp
  · let cs : Array Core.Comment :=
      #[{ kind := "line", startLine := 0, endLine := 1, fingerprint := AdequacyCore.zeroFp }]
    have hdl := hc.2 _ List.mem_cons_self cs
    have hd := diff_distinctLines_zero_line
    have h2 : blindDistinctLinesModel cs = 2 :=
      AdequacyRatchet.distinctLines_unique_val hdl hd.1
    have h1 : blindDistinctLinesModel cs = 1 := hd.2.symm
    omega

def blindAnalyzeCommentsModel : AnalyzeCommentsFn :=
  fun file cs =>
    { file := file
      comments := cs
      lines := blindDistinctLinesModel cs
      fingerprints := AdequacyCore.sortFpModel (cs.map (·.fingerprint)) }

theorem analyzeComments_separates_blind :
    RatchetRecords.analyzeCommentsRecord.Meets AdequacyRatchet.analyzeCommentsModel ∧
      ¬ BlindSecondModel.analyzeCommentsRecord.Meets AdequacyRatchet.analyzeCommentsModel := by
  refine ⟨AdequacyRatchet.analyzeCommentsModel_meets, fun hb => ?_⟩
  let cs : Array Core.Comment :=
    #[{ kind := "line", startLine := 0, endLine := 1, fingerprint := AdequacyCore.zeroFp }]
  have ha := AdequacyRatchet.analyzeCommentsModel_meets.2 _ List.mem_cons_self "A.lean" cs
  have hba := hb.2 _ List.mem_cons_self "A.lean" cs
  have hd := diff_distinctLines_zero_line
  have h2 : (AdequacyRatchet.analyzeCommentsModel "A.lean" cs).lines = 2 :=
    AdequacyRatchet.distinctLines_unique_val ha.2.2.1 hd.1
  have h1 : (AdequacyRatchet.analyzeCommentsModel "A.lean" cs).lines = 1 :=
    hba.2.2.1.trans hd.2.symm
  omega

theorem analyzeComments_blind_separates :
    BlindSecondModel.analyzeCommentsRecord.Meets blindAnalyzeCommentsModel ∧
      ¬ RatchetRecords.analyzeCommentsRecord.Meets blindAnalyzeCommentsModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro file cs
      refine ⟨rfl, rfl, rfl, (blindAnalyzeCommentsModel file cs).fingerprints.sorted, fun a => ?_⟩
      simpa [blindAnalyzeCommentsModel] using
        AdequacyCore.sortFpModel_meets.2 _ List.mem_cons_self (cs.map (·.fingerprint)) a
    exact nomatch hp
  · let cs : Array Core.Comment :=
      #[{ kind := "line", startLine := 0, endLine := 1, fingerprint := AdequacyCore.zeroFp }]
    have ha := hc.2 _ List.mem_cons_self "A.lean" cs
    have hd := diff_distinctLines_zero_line
    have h2 : blindDistinctLinesModel cs = 2 :=
      AdequacyRatchet.distinctLines_unique_val ha.2.2.1 hd.1
    have h1 : blindDistinctLinesModel cs = 1 := hd.2.symm
    omega

noncomputable def blindValidateCheckModel : ValidateCheckFn :=
  open Classical in
  fun analyses checked excluded cur base? target? =>
    if BlindSecondModel.ValidCheck analyses checked excluded cur base? target? then .ok ()
    else .error "blind"

theorem validateCheck_separates_blind :
    RatchetRecords.validateCheckRecord.Meets AdequacyRatchet.validateCheckModel ∧
      ¬ BlindSecondModel.validateCheckRecord.Meets AdequacyRatchet.validateCheckModel := by
  refine ⟨AdequacyRatchet.validateCheckModel_meets, fun hb => ?_⟩
  let bad : RatchetCore.FileAnalysis :=
    { file := "A.lean", comments := #[AdequacyCore.sampleComment1], lines := 1,
      fingerprints := ⟨#[AdequacyCore.zeroFp], List.pairwise_singleton _ _⟩ }
  let good : RatchetCore.FileAnalysis :=
    { file := "A.lean", comments := #[], lines := 0, fingerprints := Core.SortedFingerprints.empty }
  let analyses : Array RatchetCore.FileAnalysis := #[bad, good]
  have hd := diff_validateCheck_duplicate_file
  obtain ⟨u, hu⟩ := (hb.2 _ List.mem_cons_self analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean")).mpr hd.2
  cases u
  exact hd.1 (AdequacyRatchet.validateCheckModel_meets.2 _ List.mem_cons_self analyses #[] #[]
    AdequacyRatchet.emptyRatchetMap none (some "A.lean") hu)

theorem validateCheck_blind_separates :
    BlindSecondModel.validateCheckRecord.Meets blindValidateCheckModel ∧
      ¬ RatchetRecords.validateCheckRecord.Meets blindValidateCheckModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro analyses checked excluded cur base? target?
      dsimp [blindValidateCheckModel, BlindSecondModel.Succeeds]
      split <;> rename_i h
      · exact ⟨(fun _ => h), (fun _ => ⟨(), rfl⟩)⟩
      · exact ⟨(fun ⟨_, heq⟩ => nomatch heq), (fun hv => absurd hv h)⟩
    exact nomatch hp
  · let bad : RatchetCore.FileAnalysis :=
      { file := "A.lean", comments := #[AdequacyCore.sampleComment1], lines := 1,
        fingerprints := ⟨#[AdequacyCore.zeroFp], List.pairwise_singleton _ _⟩ }
    let good : RatchetCore.FileAnalysis :=
      { file := "A.lean", comments := #[], lines := 0, fingerprints := Core.SortedFingerprints.empty }
    let analyses : Array RatchetCore.FileAnalysis := #[bad, good]
    have hd := diff_validateCheck_duplicate_file
    have hv : BlindSecondModel.ValidCheck analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean") :=
      hd.2
    have hok : blindValidateCheckModel analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean") = .ok () := by
      dsimp [blindValidateCheckModel]
      simp [hv]
    exact hd.1 (hc.2 _ List.mem_cons_self analyses #[] #[] AdequacyRatchet.emptyRatchetMap none (some "A.lean") hok)

noncomputable def blindCheckTokenModel : CheckTokenFn :=
  open Classical in
  fun ctx tok raw next start =>
    if BlindSecondModel.SafeToken ctx tok raw next start then .ok () else .error "blind"

theorem checkToken_separates_blind :
    CoreRecords.checkTokenRecord.Meets AdequacyCore.checkTokenModel ∧
      ¬ BlindSecondModel.checkTokenRecord.Meets AdequacyCore.checkTokenModel := by
  refine ⟨AdequacyCore.checkTokenModel_meets, fun hb => ?_⟩
  let tok := Syntax.ident .none ⟨"", ⟨0⟩, ⟨0⟩⟩ `x []
  have hd := diff_checkToken_identMismatch
  have hsafe : BlindSecondModel.SafeToken AdequacyCore.emptyCtx tok "--" ' ' 0 := .inl hd.1
  obtain ⟨u, hu⟩ := (hb.2 _ List.mem_cons_self AdequacyCore.emptyCtx tok "--" ' ' 0).mpr hsafe
  cases u
  exact hd.2 (AdequacyCore.checkTokenModel_meets.2 _ List.mem_cons_self AdequacyCore.emptyCtx tok "--" ' ' 0 hu)

theorem checkToken_blind_separates :
    BlindSecondModel.checkTokenRecord.Meets blindCheckTokenModel ∧
      ¬ CoreRecords.checkTokenRecord.Meets blindCheckTokenModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro ctx tok raw next start
      dsimp [blindCheckTokenModel, BlindSecondModel.Succeeds]
      split <;> rename_i h
      · exact ⟨(fun _ => h), (fun _ => ⟨(), rfl⟩)⟩
      · exact ⟨(fun ⟨_, heq⟩ => nomatch heq), (fun hs => absurd hs h)⟩
    exact nomatch hp
  · let tok := Syntax.ident .none ⟨"", ⟨0⟩, ⟨0⟩⟩ `x []
    have hd := diff_checkToken_identMismatch
    have hsafe : BlindSecondModel.SafeToken AdequacyCore.emptyCtx tok "--" ' ' 0 := .inl hd.1
    have hok : blindCheckTokenModel AdequacyCore.emptyCtx tok "--" ' ' 0 = .ok () := by
      dsimp [blindCheckTokenModel]
      simp [hsafe]
    exact hd.2 (hc.2 _ List.mem_cons_self AdequacyCore.emptyCtx tok "--" ' ' 0 hok)

noncomputable def blindClassifyFileModel : ClassifyFileFn :=
  open Classical in
  fun cfg path =>
    if h : ∃ out, BlindSecondModel.Classification cfg path out then .ok (Classical.choose h)
    else .error "blind"

theorem classifyFile_separates_blind :
    ConfigRecords.classifyFileRecord.Meets AdequacyConfig.classifyFileModel ∧
      ¬ BlindSecondModel.classifyFileRecord.Meets AdequacyConfig.classifyFileModel := by
  refine ⟨AdequacyConfig.classifyFileModel_meets, fun hb => ?_⟩
  let cfg : Config.RepoConfig :=
    { workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
      exclude := #[{ prefix_ := "Foo", reason := "excluded" }]
      ratchet := "comment-ratchet.json" }
  have hd := diff_classifyFile_segmentPrefix
  have hbm := hb.2 _ List.mem_cons_self cfg "FooBar.lean"
  cases hf : AdequacyConfig.classifyFileModel cfg "FooBar.lean" with
  | error msg =>
    rw [hf] at hbm
    exact hbm ⟨_, hd.2⟩
  | ok out =>
    have hout := AdequacyConfig.classifyOutcome_unique
      (AdequacyConfig.classifyFileModel_meets.2 _ List.mem_cons_self cfg "FooBar.lean" out hf) hd.1
    subst hout
    rw [hf] at hbm
    rcases hbm with ⟨_, _, hne⟩ | ⟨hex, _⟩
    · cases hne
    · simp [cfg] at hex

theorem classifyFile_blind_separates :
    BlindSecondModel.classifyFileRecord.Meets blindClassifyFileModel ∧
      ¬ ConfigRecords.classifyFileRecord.Meets blindClassifyFileModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro cfg path
      dsimp [blindClassifyFileModel]
      split <;> rename_i h
      · exact Classical.choose_spec h
      · exact h
    exact nomatch hp
  · let cfg : Config.RepoConfig :=
      { workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
        exclude := #[{ prefix_ := "Foo", reason := "excluded" }]
        ratchet := "comment-ratchet.json" }
    have hd := diff_classifyFile_segmentPrefix
    have hex : ∃ out, BlindSecondModel.Classification cfg "FooBar.lean" out := ⟨_, hd.2⟩
    have hok : blindClassifyFileModel cfg "FooBar.lean" = .ok (Classical.choose hex) := by
      dsimp [blindClassifyFileModel]
      simp [hex]
    have hcl := Classical.choose_spec hex
    have hco := hc.2 _ List.mem_cons_self cfg "FooBar.lean" (Classical.choose hex) hok
    have heq := AdequacyConfig.classifyOutcome_unique hco hd.1
    rw [heq] at hcl
    rcases hcl with ⟨_, _, hne⟩ | ⟨hem, _⟩
    · cases hne
    · simp [cfg] at hem

noncomputable def blindClassifyTrackedModel : ClassifyTrackedFn :=
  open Classical in
  fun cfg paths =>
    if h : ∃ out, BlindSecondModel.TrackedClassification cfg paths out then .ok (Classical.choose h)
    else .error "blind"

theorem classifyTracked_separates_blind :
    ConfigRecords.classifyTrackedRecord.Meets AdequacyConfig.classifyTrackedModel ∧
      ¬ BlindSecondModel.classifyTrackedRecord.Meets AdequacyConfig.classifyTrackedModel := by
  refine ⟨AdequacyConfig.classifyTrackedModel_meets, fun hb => ?_⟩
  let cfg : Config.RepoConfig :=
    { workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
      exclude := #[{ prefix_ := "Foo", reason := "excluded" }]
      ratchet := "comment-ratchet.json" }
  have hd := diff_classifyFile_segmentPrefix
  have htc : ConfigSpec.ClassifyTrackedOutcome cfg #["FooBar.lean"]
      #[.checked "FooBar.lean" 0 "FooBar.lean" false] := by
    refine ⟨rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨by decide, hd.1⟩
  have hbt : BlindSecondModel.TrackedClassification cfg #["FooBar.lean"]
      #[.excluded "FooBar.lean" { prefix_ := "Foo", reason := "excluded" }] := by
    refine ⟨rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨by decide, hd.2⟩
  have hbm := hb.2 _ List.mem_cons_self cfg #["FooBar.lean"]
  cases hf : AdequacyConfig.classifyTrackedModel cfg #["FooBar.lean"] with
  | error msg =>
    rw [hf] at hbm
    exact hbm ⟨_, hbt⟩
  | ok out =>
    have hout := AdequacyConfig.classifyTrackedOutcome_unique
      (AdequacyConfig.classifyTrackedModel_meets.2 _ List.mem_cons_self cfg #["FooBar.lean"] out hf) htc
    subst hout
    rw [hf] at hbm
    obtain ⟨_, hcl⟩ := hbm.2 0 (by decide)
    rcases hcl with ⟨_, _, hne⟩ | ⟨hex, _⟩
    · cases hne
    · simp [cfg] at hex

theorem classifyTracked_blind_separates :
    BlindSecondModel.classifyTrackedRecord.Meets blindClassifyTrackedModel ∧
      ¬ ConfigRecords.classifyTrackedRecord.Meets blindClassifyTrackedModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro cfg paths
      dsimp [blindClassifyTrackedModel]
      split <;> rename_i h
      · exact Classical.choose_spec h
      · exact h
    exact nomatch hp
  · let cfg : Config.RepoConfig :=
      { workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
        exclude := #[{ prefix_ := "Foo", reason := "excluded" }]
        ratchet := "comment-ratchet.json" }
    have hd := diff_classifyFile_segmentPrefix
    have htc : ConfigSpec.ClassifyTrackedOutcome cfg #["FooBar.lean"]
        #[.checked "FooBar.lean" 0 "FooBar.lean" false] := by
      refine ⟨rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact ⟨by decide, hd.1⟩
    have hbt : BlindSecondModel.TrackedClassification cfg #["FooBar.lean"]
        #[.excluded "FooBar.lean" { prefix_ := "Foo", reason := "excluded" }] := by
      refine ⟨rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact ⟨by decide, hd.2⟩
    have hex : ∃ out, BlindSecondModel.TrackedClassification cfg #["FooBar.lean"] out := ⟨_, hbt⟩
    have hok : blindClassifyTrackedModel cfg #["FooBar.lean"] = .ok (Classical.choose hex) := by
      dsimp [blindClassifyTrackedModel]
      simp [hex]
    have hcl := Classical.choose_spec hex
    have hco := hc.2 _ List.mem_cons_self cfg #["FooBar.lean"] (Classical.choose hex) hok
    have heq := AdequacyConfig.classifyTrackedOutcome_unique hco htc
    rw [heq] at hcl
    obtain ⟨_, h0⟩ := hcl.2 0 (by decide)
    rcases h0 with ⟨_, _, hne⟩ | ⟨hem, _⟩
    · cases hne
    · simp [cfg] at hem

def ctrlConfigObj : Std.TreeMap.Raw String Json compare :=
  ((Std.TreeMap.Raw.empty : Std.TreeMap.Raw String Json compare).insert "workspaces"
    (Json.arr #[AdequacyConfig.sampleWorkspaceJson])).insert "ratchet" (Json.str "\x01")

def ctrlConfigJson : Json := Json.obj ctrlConfigObj

def ctrlRepoConfig : Config.RepoConfig where
  workspaces := #[AdequacyConfig.sampleParsedWorkspace]
  exclude := #[]
  ratchet := "\x01"

theorem ctrlConfigJson_valid :
    ConfigSpec.ValidConfigJson ctrlConfigJson ctrlRepoConfig := by
  refine ⟨ctrlConfigObj, #[AdequacyConfig.sampleWorkspaceJson], "\x01", rfl, ?_, rfl,
    by decide, rfl, ?_, by decide, rfl, rfl, ?_⟩
  · intro kv hmem
    have hkv : kv ∈ [("ratchet", Json.str "\x01"),
        ("workspaces", Json.arr #[AdequacyConfig.sampleWorkspaceJson])] := hmem
    rcases List.mem_cons.mp hkv with rfl | hkv
    · decide
    · rcases List.mem_singleton.mp hkv with rfl
      decide
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨by decide, AdequacyConfig.sampleWorkspaceJson_valid⟩
  · have h1 : ConfigSpec.stripDotSlash "\x01" = "\x01" :=
      AdequacyConfig.stripDotSlash_eq_self (by simp only [String.reduceToList]; decide)
    have hsp : "\x01".splitOn "/" = ["\x01"] :=
      AdequacyConfig.splitOn_slash_single_byte "\x01" (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨by decide, diff_parseConfig_cleanCtrl.1, by decide, by decide,
      ?_, ?_, ?_, h1⟩
    · rw [h1]; decide
    · rw [h1]; decide
    · rw [h1, ConfigSpec.validSegmentsBool, hsp]; decide

theorem ctrlConfigJson_not_blind (cfg : Config.RepoConfig) :
    ¬ BlindSecondModel.ConfigJson ctrlConfigJson cfg := by
  rintro ⟨_, _, _, _, _, _, _, hrat, hfp⟩
  have hget : ctrlConfigJson.getObjVal? "ratchet" = .ok (Json.str "\x01") := rfl
  rw [BlindSecondModel.Field] at hrat
  rw [hget] at hrat
  have hreq : cfg.ratchet = "\x01" := Json.str.inj (Except.ok.inj hrat).symm
  rw [hreq] at hfp
  have hsp : "\x01".splitOn "/" = ["\x01"] :=
    AdequacyConfig.splitOn_slash_single_byte "\x01" (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpart : "\x01" ∈ ("\x01".splitOn "/") := by rw [hsp]; simp
  exact diff_parseConfig_cleanCtrl.2 (hfp.1 "\x01" hpart).1

noncomputable def blindParseConfigModel : ParseConfigFn :=
  open Classical in
  fun j =>
    if h : ∃ cfg, BlindSecondModel.ConfigJson j cfg then .ok (Classical.choose h)
    else .error "blind"

theorem parseConfig_separates_blind :
    ConfigRecords.parseConfigRecord.Meets AdequacyConfig.parseConfigModel ∧
      ¬ BlindSecondModel.parseConfigRecord.Meets AdequacyConfig.parseConfigModel := by
  refine ⟨AdequacyConfig.parseConfigModel_meets, fun hb => ?_⟩
  have hbm := hb.2 _ List.mem_cons_self ctrlConfigJson
  cases hf : AdequacyConfig.parseConfigModel ctrlConfigJson with
  | error msg =>
    exact AdequacyConfig.validConfigJson_and_refusal_disjoint ctrlConfigJson_valid
      (AdequacyConfig.parseConfigModel_meets.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
        ctrlConfigJson msg hf)
  | ok cfg =>
    rw [hf] at hbm
    exact ctrlConfigJson_not_blind cfg hbm

theorem parseConfig_blind_separates :
    BlindSecondModel.parseConfigRecord.Meets blindParseConfigModel ∧
      ¬ ConfigRecords.parseConfigRecord.Meets blindParseConfigModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro j
      dsimp [blindParseConfigModel]
      split <;> rename_i h
      · exact Classical.choose_spec h
      · exact h
    exact nomatch hp
  · have hno : ¬ ∃ cfg, BlindSecondModel.ConfigJson ctrlConfigJson cfg :=
      fun ⟨cfg, h⟩ => ctrlConfigJson_not_blind cfg h
    have herr : blindParseConfigModel ctrlConfigJson = .error "blind" := by
      dsimp [blindParseConfigModel]
      simp [hno]
    exact AdequacyConfig.validConfigJson_and_refusal_disjoint ctrlConfigJson_valid
      (hc.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) ctrlConfigJson "blind" herr)

def ctrlRatchetEntryObj : Std.TreeMap.Raw String Json compare :=
  ((((Std.TreeMap.Raw.empty : Std.TreeMap.Raw String Json compare).insert "file" (Json.str "\x01")).insert
    "comments" (Json.num ⟨1, 0⟩)).insert "lines" (Json.num ⟨1, 0⟩)).insert
    "fingerprints" (Json.arr #[Json.str AdequacyCore.zeroFp])

def ctrlRatchetEntryJson : Json := Json.obj ctrlRatchetEntryObj

def ctrlRatchetJson : Json := Json.arr #[ctrlRatchetEntryJson]

def ctrlRatchetEntry : RatchetCore.RatchetEntry where
  file := "\x01"
  comments := 1
  lines := 1
  fingerprints := ⟨#[AdequacyCore.zeroFp], List.pairwise_singleton _ _⟩

theorem ctrlRatchetEntryJson_valid :
    RatchetSpec.ValidRatchetEntryJson ctrlRatchetEntryJson ctrlRatchetEntry := by
  refine ⟨ctrlRatchetEntryObj, "\x01", #[Json.str AdequacyCore.zeroFp], rfl, ?_, rfl, ?_,
    rfl, by decide, rfl, by decide, rfl, rfl, rfl, ?_⟩
  · intro kv hmem
    have hkv : kv ∈ [("comments", Json.num ⟨1, 0⟩), ("file", Json.str "\x01"),
        ("fingerprints", Json.arr #[Json.str AdequacyCore.zeroFp]), ("lines", Json.num ⟨1, 0⟩)] := hmem
    rcases List.mem_cons.mp hkv with rfl | hkv
    · decide
    · rcases List.mem_cons.mp hkv with rfl | hkv
      · decide
      · rcases List.mem_cons.mp hkv with rfl | hkv
        · decide
        · rcases List.mem_singleton.mp hkv with rfl
          decide
  · have h1 : ConfigSpec.stripDotSlash "\x01" = "\x01" :=
      AdequacyConfig.stripDotSlash_eq_self (by simp only [String.reduceToList]; decide)
    have hsp : "\x01".splitOn "/" = ["\x01"] :=
      AdequacyConfig.splitOn_slash_single_byte "\x01" (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨by decide, diff_parseConfig_cleanCtrl.1, by decide, by decide,
      ?_, ?_, ?_, h1⟩
    · rw [h1]; decide
    · rw [h1]; decide
    · rw [h1, ConfigSpec.validSegmentsBool, hsp]; decide
  · intro fp hfp
    have hmem : fp ∈ [AdequacyCore.zeroFp] := hfp
    rcases List.mem_singleton.mp hmem with rfl
    exact AdequacyCore.zeroFp_valid

theorem ctrlRatchetJson_valid :
    RatchetSpec.ValidRatchetJson ctrlRatchetJson
      (AdequacyRatchet.hashMapOfEntries [ctrlRatchetEntry]) := by
  refine ⟨#[ctrlRatchetEntryJson], [ctrlRatchetEntry], rfl, rfl, ?_, by decide,
    AdequacyRatchet.hashMapOfEntries_lookup (by decide)⟩
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  exact ⟨by decide, ctrlRatchetEntryJson_valid⟩

theorem ctrlRatchetJson_not_blind (m : BlindSecondModel.RatchetMap) :
    ¬ BlindSecondModel.RatchetJson ctrlRatchetJson m := by
  rintro ⟨entries, ⟨items, hgetArr, hsz, helts⟩, _, _⟩
  have ha : items = #[ctrlRatchetEntryJson] := by
    change Except.ok #[ctrlRatchetEntryJson] = Except.ok items at hgetArr
    exact (Except.ok.inj hgetArr).symm
  subst ha
  obtain ⟨ho, _, hfile, hfp, _⟩ := helts 0 (by decide)
  have hfget : ctrlRatchetEntryJson.getObjVal? "file" = .ok (Json.str "\x01") := rfl
  change ctrlRatchetEntryJson.getObjVal? "file" = .ok (Json.str entries[0].file) at hfile
  rw [hfget] at hfile
  have hfeq : entries[0].file = "\x01" := Json.str.inj (Except.ok.inj hfile).symm
  rw [hfeq] at hfp
  have hsp : "\x01".splitOn "/" = ["\x01"] :=
    AdequacyConfig.splitOn_slash_single_byte "\x01" (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpart : "\x01" ∈ ("\x01".splitOn "/") := by rw [hsp]; simp
  exact diff_parseConfig_cleanCtrl.2 (hfp.1 "\x01" hpart).1

noncomputable def blindParseRatchetModel : ParseRatchetFn :=
  open Classical in
  fun j =>
    if h : ∃ m, BlindSecondModel.RatchetJson j m then .ok (Classical.choose h)
    else .error "blind"

theorem parseRatchet_separates_blind :
    RatchetRecords.parseRatchetRecord.Meets AdequacyRatchet.parseRatchetModel ∧
      ¬ BlindSecondModel.parseRatchetRecord.Meets AdequacyRatchet.parseRatchetModel := by
  refine ⟨AdequacyRatchet.parseRatchetModel_meets, fun hb => ?_⟩
  have hbm := hb.2 _ List.mem_cons_self ctrlRatchetJson
  cases hf : AdequacyRatchet.parseRatchetModel ctrlRatchetJson with
  | error msg =>
    exact AdequacyRatchet.validRatchetJson_and_refusal_disjoint ctrlRatchetJson_valid
      (AdequacyRatchet.parseRatchetModel_meets.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
        ctrlRatchetJson msg hf)
  | ok m =>
    rw [hf] at hbm
    exact ctrlRatchetJson_not_blind m hbm

theorem parseRatchet_blind_separates :
    BlindSecondModel.parseRatchetRecord.Meets blindParseRatchetModel ∧
      ¬ RatchetRecords.parseRatchetRecord.Meets blindParseRatchetModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro j
      dsimp [blindParseRatchetModel]
      split <;> rename_i h
      · exact Classical.choose_spec h
      · exact h
    exact nomatch hp
  · have hno : ¬ ∃ m, BlindSecondModel.RatchetJson ctrlRatchetJson m :=
      fun ⟨m, h⟩ => ctrlRatchetJson_not_blind m h
    have herr : blindParseRatchetModel ctrlRatchetJson = .error "blind" := by
      dsimp [blindParseRatchetModel]
      simp [hno]
    exact AdequacyRatchet.validRatchetJson_and_refusal_disjoint ctrlRatchetJson_valid
      (hc.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) ctrlRatchetJson "blind" herr)

def truncDashFileMap : FileMap :=
  { source := "--a", positions := #[0] }

def truncDashInputCtx : Parser.InputContext where
  inputString := "--a"
  fileName := "<spec>"
  fileMap := truncDashFileMap
  endPos := ⟨3⟩
  endPos_valid := String.Pos.Raw.le_iff.mpr (by decide)

noncomputable def truncDashCtx : Parser.ParserContextCore where
  toInputContext := truncDashInputCtx
  env := AdequacyCore.emptyEnv
  options := ∅
  prec := 0
  tokens := {}

noncomputable def truncDashRange : Core.CommandRange where
  ctx := truncDashCtx
  stx := .missing
  prevPos := ⟨0⟩
  nextPos := ⟨2⟩

theorem truncDashRange_healthy :
    Healthy.Collect [truncDashRange] AdequacyCollect.emptyAcc := by
  refine ⟨Healthy.insertSpan (Healthy.stateOfAcc AdequacyCollect.emptyAcc) "line" 0 2, ?_⟩
  refine Healthy.RangesOk.cons (mid := ⟨0⟩) (state1 := Healthy.stateOfAcc AdequacyCollect.emptyAcc)
    (by decide) (by decide) ?_ ?_ Healthy.RangesOk.nil
  · exact Healthy.SyntaxOk.other (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  · refine Healthy.Trivia.line (eol := ⟨2⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (Healthy.LineEnd.done (by decide)) ?_ (Healthy.Trivia.done (by decide))
    refine ⟨by decide, ?_⟩
    simp [Healthy.stateOfAcc, AdequacyCollect.emptyAcc]

theorem tiling_le_of_valid {r : Core.CommandRange} {lo hi : Nat} {parts : List BlindSecondModel.ScanPart}
    (ht : BlindSecondModel.Tiling lo parts hi)
    (hv : ∀ p ∈ parts, BlindSecondModel.ValidPart r p) :
    lo ≤ hi := by
  induction parts generalizing lo with
  | nil => exact Nat.le_of_eq ht
  | cons p rest ih =>
    rcases ht with ⟨rfl, ht'⟩
    have hp := hv p List.mem_cons_self
    rcases hp with ⟨_, raw, _, _, _, hhi, _⟩
    have hle : p.hi ≤ hi := ih ht' (fun q hq => hv q (List.mem_cons_of_mem _ hq))
    omega

theorem tiling_first_pos {r : Core.CommandRange} {lo hi : Nat}
    {parts : List BlindSecondModel.ScanPart}
    (ht : BlindSecondModel.Tiling lo parts hi)
    (hv : ∀ p ∈ parts, BlindSecondModel.ValidPart r p)
    (hlt : lo < hi) :
    ∃ p ∈ parts, p.lo = lo ∧ lo < p.hi ∧ p.hi ≤ hi := by
  induction parts generalizing lo with
  | nil =>
    have : lo = hi := ht
    omega
  | cons p rest ih =>
    rcases ht with ⟨rfl, ht'⟩
    have hvp := hv p List.mem_cons_self
    rcases hvp with ⟨_, raw, _, _, _, hhi, _⟩
    have hvr : ∀ q ∈ rest, BlindSecondModel.ValidPart r q :=
      fun q hq => hv q (List.mem_cons_of_mem _ hq)
    have hle : p.hi ≤ hi := tiling_le_of_valid ht' hvr
    by_cases hpos : p.lo < p.hi
    · exact ⟨p, List.mem_cons_self, rfl, hpos, hle⟩
    · have heq : p.lo = p.hi := by omega
      obtain ⟨q, hqm, hqlo, hqpos, hqhi⟩ := ih ht' hvr (by omega)
      exact ⟨q, List.mem_cons_of_mem _ hqm, hqlo.trans heq.symm, by omega, hqhi⟩

theorem truncDashRange_not_blind (acc' : Core.CommentAcc) :
    ¬ BlindSecondModel.Collected [truncDashRange] AdequacyCollect.emptyAcc acc' := by
  intro hc
  rcases hc with ⟨scans, hmap, hscans, _⟩
  rcases scans with _ | ⟨⟨r, parts⟩, _ | _⟩
  · cases hmap
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    subst hmap
    have hrscan := hscans (truncDashRange, parts) List.mem_cons_self
    dsimp only at hrscan
    obtain ⟨p, hpmem, hplo, hpos, hphi⟩ :=
      tiling_first_pos hrscan.2.1 hrscan.2.2.1 (by decide)
    have hvp := hrscan.2.2.1 p hpmem
    rcases hvp with ⟨before, raw, after, hstr, hblo, hp_hi, hpc⟩
    have hp0 : truncDashRange.prevPos.byteIdx = 0 := rfl
    have hp2 : truncDashRange.nextPos.byteIdx = 2 := rfl
    have hb0 : before.utf8ByteSize = 0 := by omega
    have hbe : before = "" := String.utf8ByteSize_eq_zero_iff.mp hb0
    subst hbe
    simp only [String.empty_append] at hstr
    have hlists : raw.toList ++ after.toList = ['-', '-', 'a'] := by
      have := congrArg String.toList hstr
      simpa [truncDashRange, truncDashCtx, truncDashInputCtx, String.toList_append,
        String.reduceToList] using this.symm
    have hraw_ne : raw ≠ "" := fun h => by rw [h] at hp_hi; simp at hp_hi; omega
    have hraw_nonnil : raw.toList ≠ [] := fun h => hraw_ne (String.toList_eq_nil_iff.mp h)
    have hcases : (raw.toList = ['-'] ∧ after.toList = ['-', 'a']) ∨
        (raw.toList = ['-', '-'] ∧ after.toList = ['a']) := by
      cases hrl : raw.toList with
      | nil => exact absurd hrl hraw_nonnil
      | cons c1 rest1 =>
        rw [hrl] at hlists
        cases rest1 with
        | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlists
          exact .inl ⟨by rw [hlists.1], hlists.2⟩
        | cons c2 rest2 =>
          cases rest2 with
          | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlists
            exact .inr ⟨by rw [hlists.1, hlists.2.1], hlists.2.2⟩
          | cons c3 rest3 =>
            exfalso
            simp only [List.cons_append, List.cons.injEq] at hlists
            have hrest3 : rest3 = [] := (List.append_eq_nil_iff.mp hlists.2.2.2).1
            have hraw_eq : raw = "--a" := by
              rw [← String.ofList_toList (s := raw), hrl, hlists.1, hlists.2.1, hlists.2.2.1, hrest3]
            rw [hraw_eq] at hp_hi
            have h3 : ("--a" : String).utf8ByteSize = 3 := rfl
            omega
    dsimp only [BlindSecondModel.PartContent] at hpc
    cases hpi : p.item with
    | some x =>
      rcases x with ⟨tok, tag⟩
      rw [hpi] at hpc
      cases tag with
      | none =>
        cases hpc_cm : p.comment with
        | none =>
          rw [hpc_cm] at hpc
          cases hpc.1
        | some _ => rw [hpc_cm] at hpc; exact hpc.elim
      | some _ =>
        cases hpc_cm : p.comment with
        | none => rw [hpc_cm] at hpc; exact hpc.elim
        | some _ =>
          rw [hpc_cm] at hpc
          cases hpc.1
    | none =>
      rw [hpi] at hpc
      cases hpc_cm : p.comment with
      | none =>
        rw [hpc_cm] at hpc
        have hmem : '-' ∈ raw.toList := by
          rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp
        have hws := hpc '-' hmem
        exact absurd hws (by decide)
      | some c =>
        rw [hpc_cm] at hpc
        rcases hpc.1.1 with ⟨_, _, _, hafter⟩ | ⟨body, hbl, _⟩
        · rcases hafter with rfl | hnl
          · rcases hcases with ⟨_, ha⟩ | ⟨_, ha⟩ <;> simp at ha
          · have hpref : "\n".toList <+: after.toList :=
              (String.startsWith_string_iff).mp hnl
            simp only [String.reduceToList] at hpref
            rcases hpref with ⟨t, ht⟩
            rcases hcases with ⟨_, ha⟩ | ⟨_, ha⟩ <;> rw [ha] at ht <;> cases ht
        · rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hbl <;> cases hbl
  · cases hmap

noncomputable def blindCollectRangesModel : CollectRangesFn :=
  open Classical in
  fun ranges acc =>
    if h : ∃ acc', BlindSecondModel.Collected ranges acc acc' then .ok (Classical.choose h)
    else .error "blind"

theorem collectRanges_separates_blind :
    CoreRecords.collectRangesRecord.Meets AdequacyCollect.collectRangesModel ∧
      ¬ BlindSecondModel.collectRangesRecord.Meets AdequacyCollect.collectRangesModel := by
  refine ⟨AdequacyCollect.collectRangesModel_meets, fun hb => ?_⟩
  obtain ⟨acc', hok⟩ := AdequacyCollect.collectRanges_healthy_owed AdequacyCollect.collectRangesModel
    [truncDashRange] AdequacyCollect.emptyAcc AdequacyCollect.collectRangesModel_meets truncDashRange_healthy
  have hbm := hb.2 _ List.mem_cons_self [truncDashRange] AdequacyCollect.emptyAcc
  rw [hok] at hbm
  exact truncDashRange_not_blind acc' hbm

theorem collectRanges_blind_separates :
    BlindSecondModel.collectRangesRecord.Meets blindCollectRangesModel ∧
      ¬ CoreRecords.collectRangesRecord.Meets blindCollectRangesModel := by
  refine ⟨⟨(fun _ h => nomatch h), fun p hp => ?_⟩, fun hc => ?_⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · intro ranges acc
      dsimp [blindCollectRangesModel]
      split <;> rename_i h
      · exact Classical.choose_spec h
      · exact h
    exact nomatch hp
  · have hno : ¬ ∃ acc', BlindSecondModel.Collected [truncDashRange] AdequacyCollect.emptyAcc acc' :=
      fun ⟨acc', h⟩ => truncDashRange_not_blind acc' h
    have herr : blindCollectRangesModel [truncDashRange] AdequacyCollect.emptyAcc = .error "blind" := by
      dsimp [blindCollectRangesModel]
      simp [hno]
    obtain ⟨acc', hok⟩ := AdequacyCollect.collectRanges_healthy_owed blindCollectRangesModel
      [truncDashRange] AdequacyCollect.emptyAcc hc truncDashRange_healthy
    rw [herr] at hok
    cases hok

end NoCommentsSpecification.Comparison
