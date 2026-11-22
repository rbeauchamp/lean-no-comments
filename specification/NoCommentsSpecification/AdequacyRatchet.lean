module

public import LeanIntent.Obligations
public import LeanIntent.Pairs
public import LeanIntent.Progress
public import Std.Data.HashMap.Lemmas
public import NoCommentsSpecification.Healthy
public import NoCommentsSpecification.RatchetRecords
public import NoCommentsSpecification.AdequacyCore
public import NoCommentsSpecification.AdequacyConfig

@[expose] public section

namespace NoCommentsSpecification.AdequacyRatchet

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.RatchetSpec
open NoCommentsSpecification.RatchetRecords
open NoCommentsSpecification.AdequacyCore
open NoCommentsSpecification.AdequacyConfig

def analyzeCommentsModel : AnalyzeCommentsFn :=
  fun file comments =>
    { file := file
      comments := comments
      lines := distinctLinesModel comments
      fingerprints := sortFpModel (comments.map (·.fingerprint)) }

theorem analyzeCommentsModel_meets : analyzeCommentsRecord.Meets analyzeCommentsModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro file comments
    refine ⟨rfl, rfl, distinctLinesModel_meets.2 _ List.mem_cons_self comments, ?_⟩
    intro a
    simpa [analyzeCommentsModel] using
      sortFpModel_meets.2 _ List.mem_cons_self (comments.map (·.fingerprint)) a
  exact nomatch hp

theorem analyzeComments_o2 : O2 analyzeCommentsRecord := by
  refine (o2_correct _).mpr ⟨⟨analyzeCommentsModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨("", #[], analyzeCommentsModel "" #[]),
      analyzeCommentsModel_meets.2 _ List.mem_cons_self "" #[]⟩
  exact nomatch hp

theorem analyzeComments_o2Run : O2Run analyzeCommentsRecord :=
  o2Run_of_meets analyzeCommentsModel_meets

theorem analyzeComments_o3 : O3 analyzeCommentsRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => analyzeCommentsModel "" #[], fun h => ?_⟩
    obtain ⟨hf, _⟩ := h "a.lean" #[]
    simp [analyzeCommentsModel] at hf
  exact nomatch hc

theorem analyzeComments_o4 : O4 analyzeCommentsRecord := o4_function _ rfl

theorem sortedFingerprints_eq_of_count_eq {s1 s2 : Core.SortedFingerprints}
    (h : ∀ a, s1.values.toList.count a = s2.values.toList.count a) : s1 = s2 := by
  have hperm : s1.values.toList.Perm s2.values.toList := List.perm_iff_count.mpr h
  have heq : s1.values.toList = s2.values.toList :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ hle1 hle2 => Std.le_antisymm hle1 hle2)
      s1.sorted s2.sorted hperm
  cases s1
  cases s2
  simp only [Core.SortedFingerprints.mk.injEq]
  apply Array.ext'
  simpa using heq

theorem distinctLines_unique_val {comments : Array Core.Comment} {n1 n2 : Nat}
    (h1 : CoreSpec.DistinctLines comments n1) (h2 : CoreSpec.DistinctLines comments n2) :
    n1 = n2 := by
  obtain ⟨ls1, hnd1, hm1, rfl⟩ := h1
  obtain ⟨ls2, hnd2, hm2, rfl⟩ := h2
  have hperm : ls1.Perm ls2 :=
    (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun x => (hm1 x).trans (hm2 x).symm
  exact hperm.length_eq

theorem analyzeComments_o5 : O5 analyzeCommentsRecord .eq := by
  refine ⟨fun f g hf hg => funext fun file => funext fun comments => ?_, trivial⟩
  obtain ⟨hf1, hc1, hl1, hm1⟩ := hf.2 _ List.mem_cons_self file comments
  obtain ⟨hf2, hc2, hl2, hm2⟩ := hg.2 _ List.mem_cons_self file comments
  have hfile : (f file comments).file = (g file comments).file := hf1.trans hf2.symm
  have hcom : (f file comments).comments = (g file comments).comments := hc1.trans hc2.symm
  have hlines : (f file comments).lines = (g file comments).lines :=
    distinctLines_unique_val hl1 hl2
  have hfps : (f file comments).fingerprints = (g file comments).fingerprints :=
    sortedFingerprints_eq_of_count_eq fun a => (hm1 a).trans (hm2 a).symm
  cases hfres : f file comments
  cases hgres : g file comments
  rw [hfres, hgres] at hfile hcom hlines hfps
  simp only at hfile hcom hlines hfps
  subst hfile hcom hlines hfps
  rfl

theorem analyzeComments_oPair_whole :
    ∀ c ∈ analyzeCommentsRecord.props,
      OPair (Pair.whole analyzeCommentsRecord c) analyzeCommentsRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨analyzeCommentsModel, analyzeCommentsModel_meets, fun _ => analyzeCommentsModel_meets.2 c hc⟩

def analyzePerInputPair : Pair AnalyzeCommentsFn where
  Input := String × Array Core.Comment
  pre := fun _ => True
  post := fun i f => AnalyzeCommentsSpec i.1 i.2 (f i.1 i.2)

theorem analyzeComments_perInput_pairOf :
    analyzeCommentsRecord.PairOf
      ⟨"exact_file_comments_lines_fingerprints",
        fun f => ∀ file comments, AnalyzeCommentsSpec file comments (f file comments)⟩
      analyzePerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, analyzeCommentsRecord, Pair.Met, analyzePerInputPair]

theorem analyzeComments_perInput_table_attack :
    ∀ i : analyzePerInputPair.Input, analyzePerInputPair.pre i →
      ∃ f : AnalyzeCommentsFn, (∀ fl cs, f fl cs = f i.1 i.2) ∧
        analyzePerInputPair.post i f := by
  intro i _
  refine ⟨fun _ _ => analyzeCommentsModel i.1 i.2, fun _ _ => rfl, ?_⟩
  exact analyzeCommentsModel_meets.2 _ List.mem_cons_self i.1 i.2

theorem analyzeComments_interim_const_fails :
    ∀ c, ¬ analyzeCommentsRecord.Meets (fun _ _ => c) := by
  intro c hm
  obtain ⟨hf, _⟩ := hm.2 _ List.mem_cons_self "a.lean" #[]
  obtain ⟨hf2, _⟩ := hm.2 _ List.mem_cons_self "b.lean" #[]
  simp at hf hf2
  rw [hf] at hf2
  simp at hf2

theorem healthy_isFpStr_iff (s : String) :
    Healthy.isFingerprintStr s ↔ CoreSpec.IsFingerprint s := Iff.rfl

theorem validRatchetEntryJson_file_unique {j : Json} {e1 e2 : RatchetCore.RatchetEntry}
    (h1 : ValidRatchetEntryJson j e1) (h2 : ValidRatchetEntryJson j e2) : e1.file = e2.file := by
  rcases h1 with ⟨obj1, f1, _, rfl, _, hf1, hnr1, _⟩
  rcases h2 with ⟨obj2, f2, _, heq, _, hf2, hnr2, _⟩
  cases heq
  rw [hf1] at hf2
  cases hf2
  exact normRelFile_unique hnr1 hnr2

def hashMapOfEntries (entries : List RatchetCore.RatchetEntry) :
    Std.HashMap String RatchetCore.RatchetEntry :=
  entries.foldl (fun acc e => acc.insert e.file e) Std.HashMap.emptyWithCapacity

theorem foldl_insert_getElem?_of_nodup (entries : List RatchetCore.RatchetEntry)
    (init : Std.HashMap String RatchetCore.RatchetEntry)
    (hnd : (entries.map (·.file)).Nodup)
    (hdisj : ∀ e ∈ entries, init[e.file]? = none) :
    ∀ k, (entries.foldl (fun acc e => acc.insert e.file e) init)[k]? =
      match entries.find? (·.file == k) with
      | some e => some e
      | none => init[k]? := by
  induction entries generalizing init with
  | nil =>
    intro k
    rfl
  | cons hd rest ih =>
    intro k
    rw [List.map_cons, List.nodup_cons] at hnd
    have hdisj' : ∀ e ∈ rest, (init.insert hd.file hd)[e.file]? = none := by
      intro e he
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i hbe
        have heq : hd.file = e.file := beq_iff_eq.mp hbe
        exfalso
        exact hnd.1 (heq ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
      · exact hdisj e (List.mem_cons_of_mem _ he)
    simp only [List.foldl_cons, List.find?_cons]
    rw [ih (init.insert hd.file hd) hnd.2 hdisj' k]
    by_cases hkf : hd.file == k
    · simp only [hkf]
      have hnone : rest.find? (·.file == k) = none := by
        cases hrf : rest.find? (·.file == k) with
        | none => rfl
        | some e' =>
          exfalso
          have hmem := List.mem_of_find?_eq_some hrf
          have hp := List.find?_some hrf
          have hfeq : hd.file = e'.file := (beq_iff_eq.mp hkf).trans (beq_iff_eq.mp hp).symm
          exact hnd.1 (hfeq ▸ List.mem_map.mpr ⟨e', hmem, rfl⟩)
      rw [hnone]
      rw [Std.HashMap.getElem?_insert]
      simp [hkf]
    · have hkfb : (hd.file == k) = false := Bool.eq_false_iff.mpr hkf
      simp only [hkfb]
      cases hrf : rest.find? (·.file == k) with
      | some e' => rfl
      | none =>
        rw [Std.HashMap.getElem?_insert]
        simp [hkfb]

theorem hashMapOfEntries_lookup {entries : List RatchetCore.RatchetEntry}
    (hnd : (entries.map (·.file)).Nodup) (k : String) :
    (hashMapOfEntries entries)[k]? = entries.find? (·.file == k) := by
  dsimp [hashMapOfEntries]
  rw [foldl_insert_getElem?_of_nodup entries Std.HashMap.emptyWithCapacity hnd (fun _ _ => by simp)]
  cases entries.find? (·.file == k) <;> simp

theorem validRatchetJson_total (text : String) :
    (∃ m, ValidRatchetJson text m) ∨ RatchetRefusal text := by
  cases hp : Json.parse text with
  | error _ => exact .inr (.badJson fun j h => by rw [hp] at h; cases h)
  | ok j =>
    cases j with
    | arr arr =>
      by_cases hElts : ∀ (i : Nat) (_ : i < arr.size), ∃ e, ValidRatchetEntryJson arr[i] e
      · let entries : List RatchetCore.RatchetEntry :=
          List.ofFn fun idx : Fin arr.size => Classical.choose (hElts idx.1 idx.2)
        have hlen : entries.length = arr.size := List.length_ofFn
        have helts : ∀ (i : Nat) (h : i < arr.size),
            ∃ (he : i < entries.length), ValidRatchetEntryJson arr[i] entries[i] := by
          intro i hi
          refine ⟨by omega, ?_⟩
          have hget : entries[i]'(by omega) = Classical.choose (hElts i hi) := by
            simp [entries]
          rw [hget]
          exact Classical.choose_spec (hElts i hi)
        by_cases hnd : (entries.map (·.file)).Nodup
        · exact .inl ⟨hashMapOfEntries entries, arr, entries, hp, hlen, helts, hnd,
            hashMapOfEntries_lookup hnd⟩
        · obtain ⟨i, j, hi, hj, hne, heq⟩ := (list_not_nodup_iff_dup_idx (entries.map (·.file))).mp hnd
          simp only [List.length_map, hlen] at hi hj
          obtain ⟨_, hv1⟩ := helts i hi
          obtain ⟨_, hv2⟩ := helts j hj
          have hfeq : entries[i].file = entries[j].file := by
            simpa [List.getElem_map] using heq
          exact .inr (.duplicateFile hi hj hp hne hv1 hv2 hfeq)
      · have hnot : ∃ i, ∃ (_ : i < arr.size), ∀ e, ¬ ValidRatchetEntryJson arr[i] e := by
          obtain ⟨i, hni⟩ := Classical.not_forall.mp hElts
          obtain ⟨hi, hne⟩ := Classical.not_forall.mp hni
          exact ⟨i, hi, fun e he => hne ⟨e, he⟩⟩
        obtain ⟨i, hi, hne⟩ := hnot
        exact .inr (.invalidEntry hi hp hne)
    | _ => exact .inr (.notArray hp fun _ h => by cases h)

theorem validRatchetJson_and_refusal_disjoint {text : String}
    {m : Std.HashMap String RatchetCore.RatchetEntry}
    (hv : ValidRatchetJson text m) (hr : RatchetRefusal text) : False := by
  rcases hv with ⟨arr, entries, hp, hlen, helts, hnd, _⟩
  cases hr with
  | badJson hbad => exact hbad _ hp
  | notArray hp2 hna => rw [hp] at hp2; cases hp2; exact hna arr rfl
  | @invalidEntry arr2 i hi hp2 hne =>
    rw [hp] at hp2; cases hp2
    obtain ⟨_, hve⟩ := helts i hi
    exact hne _ hve
  | @duplicateFile arr2 i j e1 e2 hi hj hp2 hne hv1 hv2 hfeq =>
    rw [hp] at hp2; cases hp2
    obtain ⟨hei, hvi⟩ := helts i hi
    obtain ⟨hej, hvj⟩ := helts j hj
    have hf1 : e1.file = entries[i].file := validRatchetEntryJson_file_unique hv1 hvi
    have hf2 : e2.file = entries[j].file := validRatchetEntryJson_file_unique hv2 hvj
    have hdup := (list_not_nodup_iff_dup_idx (entries.map (·.file))).mpr
      ⟨i, j, by simpa [hlen] using hi, by simpa [hlen] using hj, hne,
        by simp [List.getElem_map, ← hf1, ← hf2, hfeq]⟩
    exact hdup hnd

theorem validRatchetEntry_iff_healthy (j : Json) (fileOut : String) :
    (∃ e, ValidRatchetEntryJson j e ∧ e.file = fileOut) ↔ Healthy.ValidRatchetEntryJson j fileOut := by
  constructor
  · rintro ⟨e, ⟨obj, fileRaw, fpsJson, rfl, hkeys, hf, hnr, hc, hcp, hl, hlp, hfp, hmap, hsz, hval⟩, rfl⟩
    refine ⟨obj, fileRaw, ↑e.comments, ↑e.lines, fpsJson, e.fingerprints.values.toList,
      rfl, hkeys, hf, (healthy_validRelFile_iff _ _).mpr hnr, hc, by omega,
      hl, by omega, hfp, hmap, by simpa using congrArg Nat.cast hsz,
      fun fp hm => (healthy_isFpStr_iff _).mpr (hval fp hm), e.fingerprints.sorted⟩
  · rintro ⟨obj, fileRaw, comments, lines, fpsJson, fpsStrs, rfl, hkeys, hf, hnr,
      hc, hcp, hl, hlp, hfp, hmap, hlen, hval, hpw⟩
    have hsorted : fpsStrs.toArray.toList.Pairwise (· ≤ ·) := by simpa using hpw
    let sf : Core.SortedFingerprints := ⟨fpsStrs.toArray, hsorted⟩
    have hc_eq : ↑comments.toNat = comments := Int.toNat_of_nonneg (Int.le_of_lt hcp)
    have hl_eq : ↑lines.toNat = lines := Int.toNat_of_nonneg (Int.le_of_lt hlp)
    let entry : RatchetCore.RatchetEntry :=
      { file := fileOut
        comments := comments.toNat
        lines := lines.toNat
        fingerprints := sf }
    refine ⟨entry, ⟨obj, fileRaw, fpsJson, rfl, hkeys, hf, (healthy_validRelFile_iff _ _).mp hnr,
      ?_, Int.lt_toNat.mpr hcp, ?_, Int.lt_toNat.mpr hlp, hfp, ?_, ?_, ?_⟩, rfl⟩
    · simpa [entry, hc_eq] using hc
    · simpa [entry, hl_eq] using hl
    · simpa [entry, sf] using hmap
    · simp only [entry, sf, List.size_toArray]
      exact Int.ofNat.inj (hlen.trans hc_eq.symm)
    · intro fp hmem
      exact (healthy_isFpStr_iff _).mp (hval fp (by simpa [entry, sf] using hmem))

theorem validRatchetJson_iff_healthy {text : String} :
    (∃ m, ValidRatchetJson text m) ↔ Healthy.RatchetText text := by
  constructor
  · rintro ⟨m, arr, entries, hp, hlen, helts, hnd, _⟩
    refine ⟨arr, entries.map (·.file), hp, by simpa using hlen, hnd, fun i hi => ?_⟩
    refine ⟨by simpa [hlen] using hi, ?_⟩
    obtain ⟨_, hve⟩ := helts i hi
    simpa [List.getElem_map] using (validRatchetEntry_iff_healthy arr[i] entries[i].file).mp ⟨_, hve, rfl⟩
  · rintro ⟨arr, files, hp, hlen, hnd, helts⟩
    have helts' : ∀ (i : Nat) (_ : i < arr.size),
        ∃ e, ValidRatchetEntryJson arr[i] e ∧ e.file = files[i]'(by omega) := by
      intro i hi
      obtain ⟨hf, hve⟩ := helts i hi
      exact (validRatchetEntry_iff_healthy arr[i] files[i]).mpr hve
    let entries : List RatchetCore.RatchetEntry :=
      List.ofFn fun idx : Fin arr.size => Classical.choose (helts' idx.1 idx.2)
    have heLen : entries.length = arr.size := List.length_ofFn
    have heFiles : entries.map (·.file) = files := by
      apply List.ext_getElem
      · simp [entries, hlen]
      · intro i h1 h2
        have hi : i < arr.size := by simpa [entries] using h1
        have hget : entries[i]'(by simpa [entries] using hi) = Classical.choose (helts' i hi) := by
          simp [entries]
        simpa [List.getElem_map, hget] using (Classical.choose_spec (helts' i hi)).2
    have hndE : (entries.map (·.file)).Nodup := heFiles ▸ hnd
    refine ⟨hashMapOfEntries entries, arr, entries, hp, heLen, fun i hi => ?_, hndE,
      hashMapOfEntries_lookup hndE⟩
    refine ⟨by omega, ?_⟩
    have hget : entries[i]'(by omega) = Classical.choose (helts' i hi) := by simp [entries]
    rw [hget]
    exact (Classical.choose_spec (helts' i hi)).1

noncomputable def parseRatchetModelWith (errMsg : String) : ParseRatchetFn :=
  open Classical in
  fun text =>
    if h : ∃ m, ValidRatchetJson text m then .ok (Classical.choose h)
    else .error errMsg

noncomputable def parseRatchetModel : ParseRatchetFn :=
  parseRatchetModelWith "invalid ratchet"

theorem parseRatchetModelWith_meets (errMsg : String) :
    parseRatchetRecord.Meets (parseRatchetModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro text m hok
    dsimp [parseRatchetModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact Classical.choose_spec h
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro text msg herr
    dsimp [parseRatchetModelWith] at herr
    split at herr
    · contradiction
    · rename_i hno
      rcases validRatchetJson_total text with hok | href
      · exact absurd hok hno
      · exact href
  exact nomatch hp

theorem parseRatchetModel_meets : parseRatchetRecord.Meets parseRatchetModel :=
  parseRatchetModelWith_meets "invalid ratchet"

def JsonRatchetOracle : Prop :=
  (∀ j, Json.parse "" ≠ .ok j) ∧ ∃ text m, ValidRatchetJson text m

theorem parseRatchet_o2_of_oracle (ho : JsonRatchetOracle) : O2 parseRatchetRecord := by
  refine (o2_correct _).mpr ⟨⟨parseRatchetModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · rcases ho.2 with ⟨text, m, hv⟩
    exact ⟨(text, m), hv⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨"", .badJson ho.1⟩
  exact nomatch hp

theorem parseRatchet_o2Run : O2Run parseRatchetRecord :=
  o2Run_of_meets parseRatchetModel_meets

theorem parseRatchet_o3_of_oracle (ho : JsonRatchetOracle) : O3 parseRatchetRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases ho with ⟨hempty, text, m, hv⟩
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => .ok m, fun h => ?_⟩
    exact validRatchetJson_and_refusal_disjoint (h "" m rfl) (.badJson hempty)
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => .error "always", fun h => ?_⟩
    exact validRatchetJson_and_refusal_disjoint hv (h text "always" rfl)
  exact nomatch hc

theorem parseRatchet_o4 : O4 parseRatchetRecord := o4_function _ rfl

def ParseRatchetFreedom : Freedom ParseRatchetFn :=
  .rel fun f g => ∀ text,
    ((f text).isOk = (g text).isOk) ∧
    (∀ m1 m2, f text = .ok m1 → g text = .ok m2 → ∀ (k : String), m1[k]? = m2[k]?)

theorem validRatchetEntryJson_unique {j : Json} {e1 e2 : RatchetCore.RatchetEntry}
    (h1 : ValidRatchetEntryJson j e1) (h2 : ValidRatchetEntryJson j e2) : e1 = e2 := by
  rcases h1 with ⟨obj1, f1, fj1, rfl, _, hf1, hnr1, hc1, _, hl1, _, hfp1, hm1, _, _⟩
  rcases h2 with ⟨obj2, f2, fj2, heq, _, hf2, hnr2, hc2, _, hl2, _, hfp2, hm2, _, _⟩
  cases heq
  rw [hf1] at hf2; cases hf2
  have hfile : e1.file = e2.file := normRelFile_unique hnr1 hnr2
  rw [hc1] at hc2
  have hcom : e1.comments = e2.comments := by
    have := JsonNumber.mk.inj (Json.num.inj (Option.some.inj hc2))
    exact Int.ofNat.inj this.1
  rw [hl1] at hl2
  have hlines : e1.lines = e2.lines := by
    have := JsonNumber.mk.inj (Json.num.inj (Option.some.inj hl2))
    exact Int.ofNat.inj this.1
  rw [hfp1] at hfp2; cases hfp2
  rw [hm1] at hm2
  have hfpsList : e1.fingerprints.values.toList = e2.fingerprints.values.toList := by
    suffices ∀ xs ys : List String, xs.map Json.str = ys.map Json.str → xs = ys from
      this _ _ hm2
    intro xs
    induction xs with
    | nil => intro ys h; cases ys <;> simp_all
    | cons x xr ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons y yr =>
        simp only [List.map_cons, List.cons.injEq, Json.str.injEq] at h
        rw [h.1, ih yr h.2]
  have hsf : e1.fingerprints = e2.fingerprints := by
    cases e1_fp : e1.fingerprints
    cases e2_fp : e2.fingerprints
    simp only [Core.SortedFingerprints.mk.injEq]
    apply Array.ext'
    simpa [e1_fp, e2_fp] using hfpsList
  cases e1; cases e2
  simp only at hfile hcom hlines hsf
  subst hfile hcom hlines hsf
  rfl

theorem validRatchetJson_lookup_unique {text : String}
    {m1 m2 : Std.HashMap String RatchetCore.RatchetEntry}
    (h1 : ValidRatchetJson text m1) (h2 : ValidRatchetJson text m2) :
    ∀ (k : String), m1[k]? = m2[k]? := by
  rcases h1 with ⟨arr1, es1, hp1, hl1, he1, _, lk1⟩
  rcases h2 with ⟨arr2, es2, hp2, hl2, he2, _, lk2⟩
  rw [hp1] at hp2; cases hp2
  have heq : es1 = es2 := by
    apply List.ext_getElem
    · rw [hl1, hl2]
    · intro i hi1 hi2
      have hi : i < arr1.size := by omega
      obtain ⟨_, hv1⟩ := he1 i hi
      obtain ⟨_, hv2⟩ := he2 i hi
      exact validRatchetEntryJson_unique hv1 hv2
  subst heq
  intro k
  rw [lk1 k, lk2 k]

theorem parseRatchet_healthy_owed :
    ∀ f text, parseRatchetRecord.Meets f →
      Healthy.RatchetText text → ∃ m, f text = .ok m := by
  intro f text hf hh
  cases hfv : f text with
  | ok m => exact ⟨m, rfl⟩
  | error msg =>
    exfalso
    have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) text msg hfv
    obtain ⟨m, hv⟩ := validRatchetJson_iff_healthy.mpr hh
    exact validRatchetJson_and_refusal_disjoint hv href

theorem parseRatchet_o5 : O5 parseRatchetRecord ParseRatchetFreedom := by
  refine ⟨fun f g hf hg text => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self text
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) text
  have hgok := hg.2 _ List.mem_cons_self text
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) text
  refine ⟨?_, fun m1 m2 h1 h2 => validRatchetJson_lookup_unique (hfok m1 h1) (hgok m2 h2)⟩
  cases h1 : f text with
  | ok m1 =>
    cases h2 : g text with
    | ok _ => rfl
    | error msg =>
      exfalso
      exact validRatchetJson_and_refusal_disjoint (hfok m1 h1) (hgerr msg h2)
  | error msg =>
    cases h2 : g text with
    | error _ => rfl
    | ok m2 =>
      exfalso
      exact validRatchetJson_and_refusal_disjoint (hgok m2 h2) (hferr msg h1)

theorem parseRatchet_not_o5_eq_of_oracle (ho : JsonRatchetOracle) :
    ¬ O5 parseRatchetRecord .eq := by
  refine not_o5_eq parseRatchetModel_meets (parseRatchetModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun heq ""
  have hna : ¬ ∃ m, ValidRatchetJson "" m := by
    rintro ⟨m, hv⟩
    exact validRatchetJson_and_refusal_disjoint hv (.badJson ho.1)
  dsimp [parseRatchetModel, parseRatchetModelWith] at hdiff
  simp [hna] at hdiff

theorem parseRatchet_oPair_whole :
    ∀ c ∈ parseRatchetRecord.props, OPair (Pair.whole parseRatchetRecord c) parseRatchetRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨parseRatchetModel, parseRatchetModel_meets, fun _ => parseRatchetModel_meets.2 c hc⟩

def parseRatchetPerInputPair : Pair ParseRatchetFn where
  Input := String
  pre := fun _ => True
  post := fun i f => ∀ m, f i = .ok m → ValidRatchetJson i m

theorem parseRatchet_perInput_pairOf :
    ∀ c ∈ parseRatchetRecord.props, c.name = "ok_valid_ratchet_map" →
      parseRatchetRecord.PairOf c parseRatchetPerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, parseRatchetRecord, Pair.Met, parseRatchetPerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem parseRatchet_perInput_table_attack :
    ∀ i : parseRatchetPerInputPair.Input, parseRatchetPerInputPair.pre i →
      ∃ f : ParseRatchetFn, (∀ s, f s = f "") ∧ parseRatchetPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ => .error "table", fun _ => rfl, ?_⟩
  intro _ h; contradiction

theorem parseRatchet_interim_const_fails_of_oracle (ho : JsonRatchetOracle) :
    ∀ c, ¬ parseRatchetRecord.Meets (fun _ => c) := by
  rcases ho with ⟨hempty, text, _, hv⟩
  intro c hm
  cases c with
  | ok m =>
    have hbad := hm.2 _ List.mem_cons_self "" m rfl
    exact validRatchetJson_and_refusal_disjoint hbad (.badJson hempty)
  | error msg =>
    have href := hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) text msg rfl
    exact validRatchetJson_and_refusal_disjoint hv href

theorem parseRatchet_healthy_nonempty_of_oracle (ho : JsonRatchetOracle) :
    ∃ text, Healthy.RatchetText text :=
  let ⟨text, m, hv⟩ := ho.2
  ⟨text, validRatchetJson_iff_healthy.mp ⟨m, hv⟩⟩

theorem parseRatchet_negative_external_model_of_oracle (ho : JsonRatchetOracle) :
    ∃ (f : ParseRatchetFn), ∃ text,
      (∀ s m, f s = .ok m → ValidRatchetJson s m) ∧
      Healthy.RatchetText text ∧
      ¬ ∃ m, f text = .ok m := by
  rcases ho.2 with ⟨text, m, hv⟩
  refine ⟨fun _ => .error "denied", text, (fun _ _ h => nomatch h),
    validRatchetJson_iff_healthy.mp ⟨m, hv⟩, fun ⟨_, h⟩ => nomatch h⟩

theorem parseRatchet_reason_classified :
    ∀ f text msg, parseRatchetRecord.Meets f → f text = .error msg →
      RatchetRefusal text ∧ ¬ Healthy.RatchetText text := by
  intro f text msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) text msg herr
  exact ⟨href, fun hh =>
    let ⟨_, hv⟩ := validRatchetJson_iff_healthy.mpr hh
    validRatchetJson_and_refusal_disjoint hv href⟩

def emptyAnalysis : RatchetCore.FileAnalysis where
  file := "Foo.lean"
  comments := #[]
  lines := 0
  fingerprints := Core.SortedFingerprints.empty

def nonEmptyAnalysis : RatchetCore.FileAnalysis where
  file := "Foo.lean"
  comments := #[sampleComment1]
  lines := 1
  fingerprints := ⟨#[zeroFp], List.pairwise_singleton _ _⟩

noncomputable def checkExactSyncModelWith (errMsg : String) : CheckExactSyncFn :=
  open Classical in
  fun analysis entry? => if ExactSyncOk analysis entry? then #[] else #[errMsg]

noncomputable def checkExactSyncModel : CheckExactSyncFn :=
  checkExactSyncModelWith "sync mismatch"

theorem checkExactSyncModelWith_meets (errMsg : String) :
    checkExactSyncRecord.Meets (checkExactSyncModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro analysis entry?
    dsimp [checkExactSyncModelWith]
    split <;> rename_i h <;> simp [Array.isEmpty, h]
  exact nomatch hp

theorem checkExactSyncModel_meets : checkExactSyncRecord.Meets checkExactSyncModel :=
  checkExactSyncModelWith_meets "sync mismatch"

theorem checkExactSync_o2 : O2 checkExactSyncRecord := by
  refine (o2_correct _).mpr ⟨⟨checkExactSyncModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(emptyAnalysis, none), rfl, rfl⟩
  exact nomatch hp

theorem checkExactSync_o2Run : O2Run checkExactSyncRecord :=
  o2Run_of_meets checkExactSyncModel_meets

theorem checkExactSync_o3 : O3 checkExactSyncRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => #[], fun h => ?_⟩
    have := (h nonEmptyAnalysis none).mp rfl
    simp [ExactSyncOk, nonEmptyAnalysis] at this
  exact nomatch hc

theorem checkExactSync_o4 : O4 checkExactSyncRecord := o4_function _ rfl

def CheckExactSyncFreedom : Freedom CheckExactSyncFn :=
  .rel fun f g => ∀ analysis entry?, (f analysis entry?).isEmpty = (g analysis entry?).isEmpty

theorem checkExactSync_o5 : O5 checkExactSyncRecord CheckExactSyncFreedom := by
  refine ⟨fun f g hf hg analysis entry? => ?_, trivial⟩
  have hfiff := hf.2 _ List.mem_cons_self analysis entry?
  have hgiff := hg.2 _ List.mem_cons_self analysis entry?
  cases h1 : (f analysis entry?).isEmpty <;> cases h2 : (g analysis entry?).isEmpty
  · rfl
  · exfalso
    exact Bool.false_ne_true (h1.symm.trans (hfiff.mpr (hgiff.mp h2)))
  · exfalso
    exact Bool.false_ne_true (h2.symm.trans (hgiff.mpr (hfiff.mp h1)))
  · rfl

theorem checkExactSync_not_o5_eq : ¬ O5 checkExactSyncRecord .eq := by
  refine not_o5_eq checkExactSyncModel_meets (checkExactSyncModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun heq nonEmptyAnalysis) none
  have hnot : ¬ ExactSyncOk nonEmptyAnalysis none := by
    intro ⟨h, _⟩
    simp [nonEmptyAnalysis] at h
  dsimp [checkExactSyncModel, checkExactSyncModelWith] at hdiff
  simp [hnot] at hdiff

theorem checkExactSync_oPair_whole :
    ∀ c ∈ checkExactSyncRecord.props,
      OPair (Pair.whole checkExactSyncRecord c) checkExactSyncRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨checkExactSyncModel, checkExactSyncModel_meets, fun _ => checkExactSyncModel_meets.2 c hc⟩

def checkExactSyncPerInputPair : Pair CheckExactSyncFn where
  Input := RatchetCore.FileAnalysis × Option RatchetCore.RatchetEntry
  pre := fun _ => True
  post := fun i f => (f i.1 i.2).isEmpty = true ↔ ExactSyncOk i.1 i.2

theorem checkExactSync_perInput_pairOf :
    checkExactSyncRecord.PairOf
      ⟨"empty_errors_iff_exact_sync",
        fun f => ∀ analysis entry?, (f analysis entry?).isEmpty = true ↔ ExactSyncOk analysis entry?⟩
      checkExactSyncPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, checkExactSyncRecord, Pair.Met, checkExactSyncPerInputPair]

theorem checkExactSync_perInput_table_attack :
    ∀ i : checkExactSyncPerInputPair.Input, checkExactSyncPerInputPair.pre i →
      ∃ f : CheckExactSyncFn, (∀ a e, f a e = f i.1 i.2) ∧
        checkExactSyncPerInputPair.post i f := by
  intro i _
  refine ⟨fun _ _ => checkExactSyncModel i.1 i.2, fun _ _ => rfl, ?_⟩
  exact checkExactSyncModel_meets.2 _ List.mem_cons_self i.1 i.2

theorem checkExactSync_interim_const_fails :
    ∀ c, ¬ checkExactSyncRecord.Meets (fun _ _ => c) := by
  intro c hm
  by_cases hempty : c.isEmpty = true
  · have := (hm.2 _ List.mem_cons_self nonEmptyAnalysis none).mp hempty
    simp [ExactSyncOk, nonEmptyAnalysis] at this
  · have := (hm.2 _ List.mem_cons_self emptyAnalysis none).mpr ⟨rfl, rfl⟩
    exact hempty this

theorem checkExactSync_healthy_nonempty :
    ∃ analysis entry?, Healthy.ExactSyncHolds analysis entry? :=
  ⟨emptyAnalysis, none, rfl, rfl⟩

theorem checkExactSync_healthy_owed :
    ∀ f analysis entry?, checkExactSyncRecord.Meets f →
      Healthy.ExactSyncHolds analysis entry? → (f analysis entry?).isEmpty = true := by
  intro f analysis entry? hf hh
  exact (hf.2 _ List.mem_cons_self analysis entry?).mpr hh

theorem checkExactSync_negative_external_model :
    ∃ (f : CheckExactSyncFn), ∃ analysis entry?,
      (∀ a e, (f a e).isEmpty = true → ExactSyncOk a e) ∧
      Healthy.ExactSyncHolds analysis entry? ∧
      ¬ (f analysis entry?).isEmpty = true := by
  refine ⟨fun _ _ => #["denied"], emptyAnalysis, none, (fun _ _ h => by simp at h),
    ⟨rfl, rfl⟩, by simp⟩

noncomputable def checkMonotonicModelWith (errMsg : String) : CheckMonotonicFn :=
  open Classical in
  fun _ liveFps _ liveLines baseEntry? =>
    if MonotonicOk liveFps liveLines baseEntry? then #[] else #[errMsg]

noncomputable def checkMonotonicModel : CheckMonotonicFn :=
  checkMonotonicModelWith "monotonic regression"

theorem checkMonotonicModelWith_meets (errMsg : String) :
    checkMonotonicFileRecord.Meets (checkMonotonicModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro _ liveFps _ liveLines baseEntry?
    dsimp [checkMonotonicModelWith]
    split <;> rename_i h <;> simp [Array.isEmpty, h]
  exact nomatch hp

theorem checkMonotonicModel_meets : checkMonotonicFileRecord.Meets checkMonotonicModel :=
  checkMonotonicModelWith_meets "monotonic regression"

theorem checkMonotonicFile_o2 : O2 checkMonotonicFileRecord := by
  refine (o2_correct _).mpr ⟨⟨checkMonotonicModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨(Core.SortedFingerprints.empty, 0, none), ?_, Nat.le_refl 0⟩
    intro a
    simp [Core.SortedFingerprints.empty]
  exact nomatch hp

theorem checkMonotonicFile_o2Run : O2Run checkMonotonicFileRecord :=
  o2Run_of_meets checkMonotonicModel_meets

theorem checkMonotonicFile_o3 : O3 checkMonotonicFileRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ _ _ _ => #[], fun h => ?_⟩
    have := (h "Foo.lean" Core.SortedFingerprints.empty 0 1 none).mp rfl
    simp [MonotonicOk] at this
  exact nomatch hc

theorem checkMonotonicFile_o4 : O4 checkMonotonicFileRecord := o4_function _ rfl

def CheckMonotonicFreedom : Freedom CheckMonotonicFn :=
  .rel fun f g => ∀ file liveFps liveComments liveLines baseEntry?,
    (f file liveFps liveComments liveLines baseEntry?).isEmpty =
      (g file liveFps liveComments liveLines baseEntry?).isEmpty

theorem checkMonotonicFile_o5 : O5 checkMonotonicFileRecord CheckMonotonicFreedom := by
  refine ⟨fun f g hf hg file liveFps liveComments liveLines baseEntry? => ?_, trivial⟩
  have hfiff := hf.2 _ List.mem_cons_self file liveFps liveComments liveLines baseEntry?
  have hgiff := hg.2 _ List.mem_cons_self file liveFps liveComments liveLines baseEntry?
  cases h1 : (f file liveFps liveComments liveLines baseEntry?).isEmpty <;>
    cases h2 : (g file liveFps liveComments liveLines baseEntry?).isEmpty
  · rfl
  · exfalso
    exact Bool.false_ne_true (h1.symm.trans (hfiff.mpr (hgiff.mp h2)))
  · exfalso
    exact Bool.false_ne_true (h2.symm.trans (hgiff.mpr (hfiff.mp h1)))
  · rfl

theorem checkMonotonicFile_not_o5_eq : ¬ O5 checkMonotonicFileRecord .eq := by
  refine not_o5_eq checkMonotonicModel_meets (checkMonotonicModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun (congrFun (congrFun (congrFun heq "Foo.lean")
    Core.SortedFingerprints.empty) 0) 1) none
  have hnot : ¬ MonotonicOk Core.SortedFingerprints.empty 1 none := by
    intro ⟨_, hl⟩
    simp at hl
  dsimp [checkMonotonicModel, checkMonotonicModelWith] at hdiff
  simp [hnot] at hdiff

theorem checkMonotonicFile_oPair_whole :
    ∀ c ∈ checkMonotonicFileRecord.props,
      OPair (Pair.whole checkMonotonicFileRecord c) checkMonotonicFileRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨checkMonotonicModel, checkMonotonicModel_meets, fun _ => checkMonotonicModel_meets.2 c hc⟩

def checkMonotonicPerInputPair : Pair CheckMonotonicFn where
  Input := String × Core.SortedFingerprints × Nat × Nat × Option RatchetCore.RatchetEntry
  pre := fun _ => True
  post := fun i f => (f i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).isEmpty = true ↔
    MonotonicOk i.2.1 i.2.2.2.1 i.2.2.2.2

theorem checkMonotonicFile_perInput_pairOf :
    checkMonotonicFileRecord.PairOf
      ⟨"empty_errors_iff_monotonic",
        fun f => ∀ file liveFps liveComments liveLines baseEntry?,
          (f file liveFps liveComments liveLines baseEntry?).isEmpty = true ↔
            MonotonicOk liveFps liveLines baseEntry?⟩
      checkMonotonicPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, checkMonotonicFileRecord, Pair.Met, checkMonotonicPerInputPair]

theorem checkMonotonicFile_perInput_table_attack :
    ∀ i : checkMonotonicPerInputPair.Input, checkMonotonicPerInputPair.pre i →
      ∃ f : CheckMonotonicFn, (∀ fl fps cs ls be, f fl fps cs ls be = f i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2) ∧
        checkMonotonicPerInputPair.post i f := by
  intro i _
  refine ⟨fun _ _ _ _ _ => checkMonotonicModel i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2,
    fun _ _ _ _ _ => rfl, ?_⟩
  exact checkMonotonicModel_meets.2 _ List.mem_cons_self i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2

theorem checkMonotonicFile_interim_const_fails :
    ∀ c, ¬ checkMonotonicFileRecord.Meets (fun _ _ _ _ _ => c) := by
  intro c hm
  by_cases hempty : c.isEmpty = true
  · have := (hm.2 _ List.mem_cons_self "Foo.lean" Core.SortedFingerprints.empty 0 1 none).mp hempty
    simp [MonotonicOk] at this
  · have hok : MonotonicOk Core.SortedFingerprints.empty 0 none := by
      refine ⟨fun a => ?_, Nat.le_refl 0⟩
      simp [Core.SortedFingerprints.empty]
    exact hempty ((hm.2 _ List.mem_cons_self "Foo.lean" Core.SortedFingerprints.empty 0 0 none).mpr hok)

theorem checkMonotonicFile_healthy_nonempty :
    ∃ liveFps liveLines baseEntry?, Healthy.MonotonicHolds liveFps liveLines baseEntry? :=
  ⟨Core.SortedFingerprints.empty, 0, none, fun a => by simp [Core.SortedFingerprints.empty], Nat.le_refl 0⟩

theorem checkMonotonicFile_healthy_owed :
    ∀ f file liveFps liveComments liveLines baseEntry?,
      checkMonotonicFileRecord.Meets f →
      Healthy.MonotonicHolds liveFps liveLines baseEntry? →
      (f file liveFps liveComments liveLines baseEntry?).isEmpty = true := by
  intro f file liveFps liveComments liveLines baseEntry? hf hh
  exact (hf.2 _ List.mem_cons_self file liveFps liveComments liveLines baseEntry?).mpr hh

theorem checkMonotonicFile_negative_external_model :
    ∃ (f : CheckMonotonicFn), ∃ file liveFps liveComments liveLines baseEntry?,
      (∀ fl fps cs ls be, (f fl fps cs ls be).isEmpty = true → MonotonicOk fps ls be) ∧
      Healthy.MonotonicHolds liveFps liveLines baseEntry? ∧
      ¬ (f file liveFps liveComments liveLines baseEntry?).isEmpty = true := by
  refine ⟨fun _ _ _ _ _ => #["denied"], "Foo.lean", Core.SortedFingerprints.empty, 0, 0, none,
    (fun _ _ _ _ _ h => by simp at h),
    ⟨fun a => by simp [Core.SortedFingerprints.empty], Nat.le_refl 0⟩, by simp⟩

theorem validateOk_iff_healthy (analyses : Array RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (targetFile? : Option String) :
    Healthy.ValidateInput analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? ↔
      ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := Iff.rfl

theorem validateOk_total (analyses : Array RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (targetFile? : Option String) :
    ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? ∨
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := by
  by_cases hcur : ∀ f e, currentRatchet[f]? = some e → f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList
  · have hbaseCase :
      (match baseRatchet? with
        | some base => ∀ f e, base[f]? = some e → f ∉ excludedFiles.toList
        | none => True) ∨
        ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := by
      cases hb : baseRatchet? with
      | none => exact .inl trivial
      | some base =>
        by_cases hbe : ∀ f e, base[f]? = some e → f ∉ excludedFiles.toList
        · exact .inl hbe
        · obtain ⟨f, hnf⟩ := Classical.not_forall.mp hbe
          obtain ⟨e, hne⟩ := Classical.not_forall.mp hnf
          have ⟨hget, hnin⟩ := Classical.not_imp.mp hne
          exact .inr (.baseRatchetExcluded rfl hget (Classical.not_not.mp hnin))
    rcases hbaseCase with hbase | href
    · cases htf : targetFile? with
      | some target =>
        cases hfind : analyses.find? (·.file == target) with
        | none => exact .inr (.missingTargetAnalysis rfl hfind)
        | some live =>
          by_cases hsync : ExactSyncOk live currentRatchet[target]?
          · cases hb : baseRatchet? with
            | none =>
              refine .inl ⟨hcur, ?_, ?_⟩
              · rw [hb] at hbase; exact hbase
              · exact ⟨live, hfind, hsync, trivial⟩
            | some base =>
              by_cases hmono : MonotonicOk live.fingerprints live.lines base[target]?
              · refine .inl ⟨hcur, ?_, ?_⟩
                · rw [hb] at hbase; exact hbase
                · exact ⟨live, hfind, hsync, hmono⟩
              · exact .inr (.targetMonotonicFailed rfl rfl hfind hmono)
          · exact .inr (.targetSyncFailed rfl hfind hsync)
      | none =>
        by_cases hallSync : ∀ a ∈ analyses.toList, ExactSyncOk a currentRatchet[a.file]?
        · cases hb : baseRatchet? with
          | none =>
            refine .inl ⟨hcur, ?_, ?_⟩
            · rw [hb] at hbase; exact hbase
            · intro a ha; exact ⟨hallSync a ha, trivial⟩
          | some base =>
            by_cases hallMono : ∀ a ∈ analyses.toList, MonotonicOk a.fingerprints a.lines base[a.file]?
            · refine .inl ⟨hcur, ?_, ?_⟩
              · rw [hb] at hbase; exact hbase
              · intro a ha; exact ⟨hallSync a ha, hallMono a ha⟩
            · obtain ⟨a, hna⟩ := Classical.not_forall.mp hallMono
              obtain ⟨ha, hnm⟩ := Classical.not_imp.mp hna
              exact .inr (.analysisMonotonicFailed rfl rfl ha hnm)
        · obtain ⟨a, hna⟩ := Classical.not_forall.mp hallSync
          obtain ⟨ha, hns⟩ := Classical.not_imp.mp hna
          exact .inr (.analysisSyncFailed rfl ha hns)
    · exact .inr href
  · obtain ⟨f, hnf⟩ := Classical.not_forall.mp hcur
    obtain ⟨e, hne⟩ := Classical.not_forall.mp hnf
    have ⟨hget, hbad⟩ := Classical.not_imp.mp hne
    by_cases hex : f ∈ excludedFiles.toList
    · exact .inr (.currentRatchetExcluded hget hex)
    · exact .inr (.currentRatchetUnknown hget fun hch => hbad ⟨hex, hch⟩)

theorem validateOk_and_refusal_disjoint {analyses : Array RatchetCore.FileAnalysis}
    {checkedFiles excludedFiles : Array String}
    {currentRatchet : Std.HashMap String RatchetCore.RatchetEntry}
    {baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry)}
    {targetFile? : Option String}
    (hok : ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?)
    (href : ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?) :
    False := by
  rcases hok with ⟨hcur, hbase, hbody⟩
  cases href with
  | currentRatchetExcluded hget hex => exact (hcur _ _ hget).1 hex
  | currentRatchetUnknown hget huch => exact huch (hcur _ _ hget).2
  | baseRatchetExcluded hb hget hex =>
    rw [hb] at hbase
    exact hbase _ _ hget hex
  | missingTargetAnalysis htf hnone =>
    rw [htf] at hbody
    rcases hbody with ⟨live, hfind, _⟩
    rw [hnone] at hfind
    cases hfind
  | targetSyncFailed htf hfind hns =>
    rw [htf] at hbody
    rcases hbody with ⟨live2, hfind2, hsync, _⟩
    rw [hfind] at hfind2; cases hfind2
    exact hns hsync
  | targetMonotonicFailed htf hb hfind hnm =>
    rw [htf] at hbody
    rcases hbody with ⟨live2, hfind2, _, hmono⟩
    rw [hfind] at hfind2; cases hfind2
    rw [hb] at hmono
    exact hnm hmono
  | analysisSyncFailed htf ha hns =>
    rw [htf] at hbody
    exact hns (hbody _ ha).1
  | analysisMonotonicFailed htf hb ha hnm =>
    rw [htf] at hbody
    have hmono := (hbody _ ha).2
    rw [hb] at hmono
    exact hnm hmono

noncomputable def validateCheckModelWith (errMsg : String) : ValidateCheckFn :=
  open Classical in
  fun analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? =>
    if ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? then
      .ok ()
    else
      .error errMsg

noncomputable def validateCheckModel : ValidateCheckFn :=
  validateCheckModelWith "validate failed"

theorem validateCheckModelWith_meets (errMsg : String) :
    validateCheckRecord.Meets (validateCheckModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro analyses checked excluded cur base? target? hok
    dsimp [validateCheckModelWith] at hok
    split at hok
    · assumption
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro analyses checked excluded cur base? target? msg herr
    dsimp [validateCheckModelWith] at herr
    split at herr
    · contradiction
    · rename_i hno
      rcases validateOk_total analyses checked excluded cur base? target? with hok | href
      · exact absurd hok hno
      · exact href
  exact nomatch hp

theorem validateCheckModel_meets : validateCheckRecord.Meets validateCheckModel :=
  validateCheckModelWith_meets "validate failed"

def emptyRatchetMap : Std.HashMap String RatchetCore.RatchetEntry := {}

theorem emptyRatchet_validateOk :
    ValidateOk #[] #[] #[] emptyRatchetMap none none := by
  refine ⟨fun f e h => ?_, trivial, fun a ha => ?_⟩
  · simp [emptyRatchetMap] at h
  · simp at ha

theorem emptyRatchet_missingTarget :
    ValidateRefusal #[] #[] #[] emptyRatchetMap none (some "Foo.lean") :=
  .missingTargetAnalysis rfl rfl

theorem validateCheck_o2 : O2 validateCheckRecord := by
  refine (o2_correct _).mpr ⟨⟨validateCheckModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(#[], #[], #[], emptyRatchetMap, none, none), emptyRatchet_validateOk⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(#[], #[], #[], emptyRatchetMap, none, some "Foo.lean"), emptyRatchet_missingTarget⟩
  exact nomatch hp

theorem validateCheck_o2Run : O2Run validateCheckRecord :=
  o2Run_of_meets validateCheckModel_meets

theorem validateCheck_o3 : O3 validateCheckRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ _ _ _ _ => .ok (), fun h => ?_⟩
    exact validateOk_and_refusal_disjoint
      (h #[] #[] #[] emptyRatchetMap none (some "Foo.lean") rfl)
      emptyRatchet_missingTarget
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ _ _ _ _ => .error "always", fun h => ?_⟩
    exact validateOk_and_refusal_disjoint
      emptyRatchet_validateOk
      (h #[] #[] #[] emptyRatchetMap none none "always" rfl)
  exact nomatch hc

theorem validateCheck_o4 : O4 validateCheckRecord := o4_function _ rfl

def ValidateCheckFreedom : Freedom ValidateCheckFn :=
  .rel fun f g => ∀ analyses checked excluded cur base? target?,
    (f analyses checked excluded cur base? target?).toOption =
      (g analyses checked excluded cur base? target?).toOption

theorem validateCheck_o5 : O5 validateCheckRecord ValidateCheckFreedom := by
  refine ⟨fun f g hf hg analyses checked excluded cur base? target? => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self analyses checked excluded cur base? target?
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) analyses checked excluded cur base? target?
  have hgok := hg.2 _ List.mem_cons_self analyses checked excluded cur base? target?
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) analyses checked excluded cur base? target?
  cases h1 : f analyses checked excluded cur base? target? with
  | ok u1 =>
    cases u1
    cases h2 : g analyses checked excluded cur base? target? with
    | ok u2 => cases u2; rfl
    | error msg =>
      exfalso
      exact validateOk_and_refusal_disjoint (hfok h1) (hgerr msg h2)
  | error msg =>
    cases h2 : g analyses checked excluded cur base? target? with
    | error _ => rfl
    | ok _ =>
      exfalso
      exact validateOk_and_refusal_disjoint (hgok h2) (hferr msg h1)

theorem validateCheck_not_o5_eq : ¬ O5 validateCheckRecord .eq := by
  refine not_o5_eq validateCheckModel_meets (validateCheckModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun heq #[]) #[]) #[])
    emptyRatchetMap) none) (some "Foo.lean")
  have hnot : ¬ ValidateOk #[] #[] #[] emptyRatchetMap none (some "Foo.lean") :=
    fun h => validateOk_and_refusal_disjoint h emptyRatchet_missingTarget
  dsimp [validateCheckModel, validateCheckModelWith] at hdiff
  simp [hnot] at hdiff

theorem validateCheck_oPair_whole :
    ∀ c ∈ validateCheckRecord.props,
      OPair (Pair.whole validateCheckRecord c) validateCheckRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨validateCheckModel, validateCheckModel_meets, fun _ => validateCheckModel_meets.2 c hc⟩

def validateCheckPerInputPair : Pair ValidateCheckFn where
  Input := Array RatchetCore.FileAnalysis × Array String × Array String ×
    Std.HashMap String RatchetCore.RatchetEntry ×
    Option (Std.HashMap String RatchetCore.RatchetEntry) × Option String
  pre := fun _ => True
  post := fun i f => f i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 = .ok () →
    ValidateOk i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2

theorem validateCheck_perInput_pairOf :
    ∀ c ∈ validateCheckRecord.props, c.name = "ok_only_when_valid" →
      validateCheckRecord.PairOf c validateCheckPerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, validateCheckRecord, Pair.Met, validateCheckPerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem validateCheck_perInput_table_attack :
    ∀ i : validateCheckPerInputPair.Input, validateCheckPerInputPair.pre i →
      ∃ f : ValidateCheckFn, (∀ a c e cur b t, f a c e cur b t = f #[] #[] #[] emptyRatchetMap none none) ∧
        validateCheckPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ _ _ _ _ _ => .error "table", fun _ _ _ _ _ _ => rfl, ?_⟩
  intro h; contradiction

theorem validateCheck_interim_const_fails :
    ∀ c, ¬ validateCheckRecord.Meets (fun _ _ _ _ _ _ => c) := by
  intro c hm
  cases c with
  | ok u =>
    cases u
    exact validateOk_and_refusal_disjoint
      (hm.2 _ List.mem_cons_self #[] #[] #[] emptyRatchetMap none (some "Foo.lean") rfl)
      emptyRatchet_missingTarget
  | error msg =>
    exact validateOk_and_refusal_disjoint
      emptyRatchet_validateOk
      (hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) #[] #[] #[] emptyRatchetMap none none msg rfl)

theorem validateCheck_healthy_nonempty :
    ∃ analyses checked excluded cur base? target?,
      Healthy.ValidateInput analyses checked excluded cur base? target? :=
  ⟨#[], #[], #[], emptyRatchetMap, none, none, emptyRatchet_validateOk⟩

theorem validateCheck_healthy_owed :
    ∀ f analyses checked excluded cur base? target?,
      validateCheckRecord.Meets f →
      Healthy.ValidateInput analyses checked excluded cur base? target? →
      ∃ u, f analyses checked excluded cur base? target? = .ok u := by
  intro f analyses checked excluded cur base? target? hf hh
  cases hfv : f analyses checked excluded cur base? target? with
  | ok u => exact ⟨u, rfl⟩
  | error msg =>
    exfalso
    exact validateOk_and_refusal_disjoint hh
      (hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) analyses checked excluded cur base? target? msg hfv)

theorem validateCheck_negative_external_model :
    ∃ (f : ValidateCheckFn), ∃ analyses checked excluded cur base? target?,
      (∀ a ch ex cu ba ta, f a ch ex cu ba ta = .ok () → ValidateOk a ch ex cu ba ta) ∧
      Healthy.ValidateInput analyses checked excluded cur base? target? ∧
      ¬ ∃ u, f analyses checked excluded cur base? target? = .ok u := by
  refine ⟨fun _ _ _ _ _ _ => .error "denied", #[], #[], #[], emptyRatchetMap, none, none,
    (fun _ _ _ _ _ _ h => nomatch h), emptyRatchet_validateOk, fun ⟨_, h⟩ => nomatch h⟩

theorem validateCheck_reason_classified :
    ∀ f analyses checked excluded cur base? target? msg,
      validateCheckRecord.Meets f →
      f analyses checked excluded cur base? target? = .error msg →
      ValidateRefusal analyses checked excluded cur base? target? ∧
        ¬ Healthy.ValidateInput analyses checked excluded cur base? target? := by
  intro f analyses checked excluded cur base? target? msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) analyses checked excluded cur base? target? msg herr
  exact ⟨href, fun hh => validateOk_and_refusal_disjoint hh href⟩

end NoCommentsSpecification.AdequacyRatchet