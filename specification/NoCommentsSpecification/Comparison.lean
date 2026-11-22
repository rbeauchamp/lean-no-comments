module

import all Init.Data.String.Substring
import all Init.Data.String.Basic
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

end NoCommentsSpecification.Comparison
