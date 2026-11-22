module

public import LeanIntent.Degenerate
public import LeanIntent.TrivialWitnesses
public import LeanIntent.Progress
public import Std.Data.HashMap.Lemmas
public import NoCommentsSpecification.Healthy
public import NoCommentsSpecification.CoreRecords
import all Init.Prelude

@[expose] public section

namespace NoCommentsSpecification.AdequacyCore

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreSpec
open NoCommentsSpecification.CoreRecords

def zeroFp : String := "0000000000000000"

def oneFp : String := "1111111111111111"

def twoFp : String := "2222222222222222"

theorem zeroFp_valid : IsFingerprint zeroFp := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [zeroFp] at hc
  subst hc
  decide

theorem oneFp_valid : IsFingerprint oneFp := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [oneFp] at hc
  subst hc
  decide

theorem twoFp_valid : IsFingerprint twoFp := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [twoFp] at hc
  subst hc
  decide

theorem not_isFp_empty : ¬ IsFingerprint "" := by
  intro ⟨h, _⟩
  simp at h

def sampleComment1 : Core.Comment :=
  { kind := "line", startLine := 1, endLine := 1, fingerprint := zeroFp }

def sampleComment13 : Core.Comment :=
  { kind := "block", startLine := 1, endLine := 3, fingerprint := oneFp }

noncomputable def emptyEnv : Environment := Classical.choice (inferInstance : Nonempty Environment)

noncomputable def emptyCtx : Parser.ParserContextCore where
  toInputContext := Parser.mkInputContext "" "<spec>"
  env := emptyEnv
  options := ∅
  prec := 0
  tokens := {}

theorem containsOpener_x : containsOpener "x" = false := by decide

theorem crossesBoundary_x_space : crossesBoundary "x" ' ' = false := by decide

theorem containsOpener_dash : containsOpener "--" = true := by decide

theorem hasCharPair_healthy_eq_spec (a b : Char) (cs : List Char) :
    Healthy.hasCharPair a b cs = CoreSpec.hasCharPair a b cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    cases rest with
    | nil => rfl
    | cons d tl =>
      simp only [Healthy.hasCharPair, CoreSpec.hasCharPair]
      rw [ih]

theorem healthy_literal_eq (env : Environment) (tok : Syntax) (raw : String) :
    Healthy.literalToken env tok raw = literalToken env tok raw := rfl

theorem healthy_sym_eq (ctx : Parser.ParserContextCore) (tok : Syntax) :
    Healthy.registeredSymbol ctx tok = registeredSymbol ctx tok := rfl

theorem tokenSafe_emptyCtx : TokenSafe emptyCtx .missing "x" ' ' := by
  right; right
  exact ⟨containsOpener_x, crossesBoundary_x_space⟩

theorem tokenUnsafe_check : TokenRefusal emptyCtx .missing "--" ' ' := by
  refine TokenRefusal.openerInRaw ?_ ?_ containsOpener_dash
  · simp [literalToken]
  · simp [registeredSymbol]

theorem token_healthy_nonempty : ∃ ctx tok raw next, Healthy.Token ctx tok raw next := by
  refine ⟨emptyCtx, .missing, "x", ' ', ?_⟩
  right; right
  decide

theorem token_healthy_and_refusal_disjoint :
    ∀ ctx tok raw next, TokenRefusal ctx tok raw next → ¬ Healthy.Token ctx tok raw next := by
  intro ctx tok raw next hr hh
  cases hr with
  | openerInRaw hlit hsym hop =>
    rcases hh with h | h | ⟨hno, _⟩
    · rw [healthy_literal_eq, hlit] at h; contradiction
    · rw [healthy_sym_eq, hsym] at h; contradiction
    · simp only [Healthy.noOpener, Bool.and_eq_true, Bool.not_eq_true',
        hasCharPair_healthy_eq_spec] at hno
      simp only [containsOpener, Bool.or_eq_true] at hop
      rcases hop with h1 | h2
      · exact Bool.false_ne_true (hno.1.symm.trans h1)
      · exact Bool.false_ne_true (hno.2.symm.trans h2)
  | boundaryCross hlit hsym hcr =>
    rcases hh with h | h | ⟨_, hnc⟩
    · rw [healthy_literal_eq, hlit] at h; contradiction
    · rw [healthy_sym_eq, hsym] at h; contradiction
    · simp only [Healthy.noBoundaryCross, crossesBoundary] at hnc hcr
      rw [hcr] at hnc
      contradiction

def isFpClause : Clause IsFingerprintFn :=
  ⟨"exact_16_lowercase_hex", fun f => ∀ s, (f s = true) ↔ IsFingerprint s⟩

theorem isFingerprint_o2 : O2 isFingerprintRecord := by
  refine (o2_correct _).mpr ⟨⟨fun _ => true, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨zeroFp, zeroFp_valid⟩
  exact nomatch hp

def isFpModel : IsFingerprintFn :=
  fun s => decide (s.length = 16 ∧ ∀ c ∈ s.toList, isHexLowerChar c = true)

theorem isFpModel_meets : isFingerprintRecord.Meets isFpModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro s; simp [isFpModel, IsFingerprint]
  exact nomatch hp

theorem isFingerprint_o2Run : O2Run isFingerprintRecord :=
  o2Run_of_meets isFpModel_meets

theorem isFingerprint_o3 : O3 isFingerprintRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => false, ?_⟩
    intro h
    have := (h zeroFp).mpr zeroFp_valid
    simp at this
  exact nomatch hc

theorem isFingerprint_o4 : O4 isFingerprintRecord := o4_function _ rfl

theorem isFingerprint_o5 : O5 isFingerprintRecord .eq := by
  refine ⟨fun f g hf hg => funext fun s => ?_, trivial⟩
  have h1 := hf.2 _ List.mem_cons_self s
  have h2 := hg.2 _ List.mem_cons_self s
  cases hfval : f s <;> cases hgval : g s <;> simp_all

theorem isFingerprint_oPair_whole :
    ∀ c ∈ isFingerprintRecord.props, OPair (Pair.whole isFingerprintRecord c) isFingerprintRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨isFpModel, isFpModel_meets, fun _ => isFpModel_meets.2 c hc⟩

def isFingerprintPerInputPair : Pair IsFingerprintFn where
  Input := String
  pre := fun _ => True
  post := fun s f => (f s = true) ↔ IsFingerprint s

theorem isFingerprint_perInput_pairOf :
    isFingerprintRecord.PairOf isFpClause isFingerprintPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, isFingerprintRecord, isFpClause, Pair.Met, isFingerprintPerInputPair]

theorem isFingerprint_perInput_oPair_table :
    OPair isFingerprintPerInputPair Witness.Constant := by
  refine ⟨⟨zeroFp, trivial⟩, ?_, trivial⟩
  intro s _
  by_cases hs : IsFingerprint s
  · exact ⟨fun _ => true, ⟨true, funext fun _ => rfl⟩, by simp [isFingerprintPerInputPair, hs]⟩
  · exact ⟨fun _ => false, ⟨false, funext fun _ => rfl⟩, by simp [isFingerprintPerInputPair, hs]⟩

theorem isFingerprint_verdicts : Verdicts isFingerprintRecord [false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, trivial⟩
  · have := (h.2 _ List.mem_cons_self zeroFp).mpr zeroFp_valid
    change (fun _ : String => false) zeroFp = true at this
    simp at this
  · have := (h.2 _ List.mem_cons_self "").mp rfl
    exact not_isFp_empty this

theorem isFingerprint_witnesses_whole :
    WitnessVerdicts (Pair.whole isFingerprintRecord isFpClause) [false, false, false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, trivial⟩
  · have := (h (fun _ => false) () trivial (fun _ hc => nomatch hc) zeroFp).mpr zeroFp_valid
    simp at this
  · obtain ⟨w, ⟨c, rfl⟩, hw⟩ := h () trivial
    have h1 := (hw (fun _ hc => nomatch hc) zeroFp).mpr zeroFp_valid
    have h2 := (hw (fun _ hc => nomatch hc) "").mp
    cases c
    · contradiction
    · exact not_isFp_empty (h2 rfl)
  · subst e
    have := (h () trivial (fun _ hc => nomatch hc) zeroFp).mpr zeroFp_valid
    change (fun _ : String => false) zeroFp = true at this
    simp at this
  · subst e
    have := (h () trivial (fun _ hc => nomatch hc) "").mp rfl
    exact not_isFp_empty this

theorem isFingerprint_perInput_witnesses :
    WitnessVerdicts isFingerprintPerInputPair [false, true, false, false] := by
  refine ⟨fun h => ?_, ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, trivial⟩
  · have := (h (fun _ => false) zeroFp trivial).mpr zeroFp_valid
    simp at this
  · exact isFingerprint_perInput_oPair_table.2.1
  · subst e
    have := (h zeroFp trivial).mpr zeroFp_valid
    change (fun _ : String => false) zeroFp = true at this
    simp at this
  · subst e
    have := (h "" trivial).mp rfl
    exact not_isFp_empty this

def fpValidClause : Clause FingerprintFn :=
  ⟨"outputs_valid_fingerprint", fun f => ∀ text, IsFingerprint (f text)⟩

def fpNonConstClause : Clause FingerprintFn :=
  ⟨"non_constant_digest", fun f => ∃ a b, f a ≠ f b⟩

def fpModel : FingerprintFn :=
  fun s => if s == "" then zeroFp else oneFp

theorem fpModel_meets : fingerprintRecord.Meets fpModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro s; dsimp [fpModel]; split
    · exact zeroFp_valid
    · exact oneFp_valid
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨"", "a", by simp [fpModel, zeroFp, oneFp]⟩
  exact nomatch hp

theorem fingerprint_o2 : O2 fingerprintRecord := by
  refine (o2_correct _).mpr ⟨⟨fpModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨zeroFp, zeroFp_valid⟩
  exact nomatch hp

theorem fingerprint_o2Run : O2Run fingerprintRecord :=
  o2Run_of_meets fpModel_meets

theorem fingerprint_o3 : O3 fingerprintRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨fun _ => "", fun h => not_isFp_empty (h "")⟩
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨fun _ => zeroFp, fun ⟨a, b, h⟩ => h rfl⟩
  exact nomatch hc

theorem fingerprint_o4 : O4 fingerprintRecord := o4_function _ rfl

def FingerprintFreedom : Freedom FingerprintFn :=
  .rel fun f g => (∀ s, IsFingerprint (f s)) ∧ (∀ s, IsFingerprint (g s))

theorem fingerprint_o5 : O5 fingerprintRecord FingerprintFreedom :=
  ⟨fun _ _ hf hg => ⟨hf.2 _ List.mem_cons_self, hg.2 _ List.mem_cons_self⟩, trivial⟩

theorem fingerprint_not_o5_eq : ¬ O5 fingerprintRecord .eq := by
  let fpModel2 : FingerprintFn := fun s => if s == "" then oneFp else twoFp
  have h2 : fingerprintRecord.Meets fpModel2 := by
    refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro s; dsimp [fpModel2]; split
      · exact oneFp_valid
      · exact twoFp_valid
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨"", "a", by simp [fpModel2, oneFp, twoFp]⟩
    exact nomatch hp
  refine not_o5_eq fpModel_meets h2 fun heq => ?_
  have := congrFun heq ""
  simp [fpModel, fpModel2, zeroFp, oneFp] at this

theorem fingerprint_oPair_whole :
    ∀ c ∈ fingerprintRecord.props, OPair (Pair.whole fingerprintRecord c) fingerprintRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨fpModel, fpModel_meets, fun _ => fpModel_meets.2 c hc⟩

def fpValidPerInputPair : Pair FingerprintFn where
  Input := String
  pre := fun _ => True
  post := fun s f => IsFingerprint (f s)

theorem fpValid_perInput_pairOf :
    fingerprintRecord.PairOf fpValidClause fpValidPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, fingerprintRecord, fpValidClause, Pair.Met, fpValidPerInputPair]

theorem fpValid_perInput_witnesses :
    WitnessVerdicts fpValidPerInputPair [false, true, false, false] := by
  refine ⟨fun h => not_isFp_empty (h (fun _ => "") "" trivial), ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, trivial⟩
  · intro _ _
    exact ⟨fun _ => zeroFp, ⟨zeroFp, funext fun _ => rfl⟩, zeroFp_valid⟩
  · subst e
    exact not_isFp_empty (h "" trivial)
  · subst e
    have hid :
        Degenerate.projSubject (W := FingerprintFn)
          (ArgPath.here (Ty.Proj.ofEq rfl)) "" = "" := rfl
    have hres := h "" trivial
    dsimp [fpValidPerInputPair] at hres
    rw [hid] at hres
    exact not_isFp_empty hres

theorem fingerprint_verdicts : Verdicts fingerprintRecord [false, false] := by
  refine ⟨fun h => not_isFp_empty (h.2 _ List.mem_cons_self ""), fun h => ?_, trivial⟩
  have hid :
      Degenerate.projSubject (W := FingerprintFn)
        (ArgPath.here (Ty.Proj.ofEq rfl)) "" = "" := rfl
  have hres := h.2 _ List.mem_cons_self ""
  rw [hid] at hres
  exact not_isFp_empty hres

theorem fingerprint_witnesses_whole_valid :
    WitnessVerdicts (Pair.whole fingerprintRecord fpValidClause) [false, true, false, false] := by
  refine ⟨fun h => ?_, ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, trivial⟩
  · have := h (fun _ => "") () trivial (fun _ hc => nomatch hc) ""
    exact not_isFp_empty this
  · intro _ _
    exact ⟨fun _ => zeroFp, ⟨zeroFp, funext fun _ => rfl⟩, fun _ _ => zeroFp_valid⟩
  · subst e
    exact not_isFp_empty (h () trivial (fun _ hc => nomatch hc) "")
  · subst e
    have hid :
        Degenerate.projSubject (W := FingerprintFn)
          (ArgPath.here (Ty.Proj.ofEq rfl)) "" = "" := rfl
    have hres := h () trivial (fun _ hc => nomatch hc) ""
    rw [hid] at hres
    exact not_isFp_empty hres

theorem fingerprint_witnesses_whole_nonconst :
    WitnessVerdicts (Pair.whole fingerprintRecord fpNonConstClause) [false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, ?_, trivial⟩
  · obtain ⟨a, b, hab⟩ := h (fun _ => "") () trivial (fun _ hc => nomatch hc)
    exact hab rfl
  · obtain ⟨w, ⟨c, rfl⟩, hw⟩ := h () trivial
    obtain ⟨a, b, hab⟩ := hw (fun _ hc => nomatch hc)
    exact hab rfl
  · subst e
    obtain ⟨a, b, hab⟩ := h () trivial (fun _ hc => nomatch hc)
    exact hab rfl
  · refine ⟨_, rfl, fun _ _ _ => ⟨"", "a", ?_⟩⟩
    have h0 : Degenerate.projSubject (W := FingerprintFn)
        (ArgPath.here (Ty.Proj.ofEq rfl)) "" = "" := rfl
    have h1 : Degenerate.projSubject (W := FingerprintFn)
        (ArgPath.here (Ty.Proj.ofEq rfl)) "a" = "a" := rfl
    rw [h0, h1]
    decide

def checkTokenOkClause : Clause CheckTokenFn :=
  ⟨"ok_only_when_token_safe",
    fun f => ∀ ctx tok raw next start, f ctx tok raw next start = .ok () → TokenSafe ctx tok raw next⟩

theorem tokenSafe_dichotomy (ctx : Parser.ParserContextCore) (tok : Syntax) (raw : String) (next : Char) :
    TokenSafe ctx tok raw next ∨ TokenRefusal ctx tok raw next := by
  by_cases hl : literalToken ctx.env tok raw = true
  · exact .inl (.inl hl)
  have hlf : literalToken ctx.env tok raw = false := Bool.eq_false_iff.mpr hl
  by_cases hs : registeredSymbol ctx tok = true
  · exact .inl (.inr (.inl hs))
  have hsf : registeredSymbol ctx tok = false := Bool.eq_false_iff.mpr hs
  by_cases ho : containsOpener raw = true
  · exact .inr (TokenRefusal.openerInRaw hlf hsf ho)
  have hof : containsOpener raw = false := Bool.eq_false_iff.mpr ho
  by_cases hc : crossesBoundary raw next = true
  · exact .inr (TokenRefusal.boundaryCross hlf hsf hc)
  have hcf : crossesBoundary raw next = false := Bool.eq_false_iff.mpr hc
  exact .inl (.inr (.inr ⟨hof, hcf⟩))

noncomputable def checkTokenModel : CheckTokenFn :=
  open Classical in
  fun ctx tok raw next _ => if TokenSafe ctx tok raw next then .ok () else .error "unsafe token"

theorem checkTokenModel_meets : checkTokenRecord.Meets checkTokenModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ctx tok raw next start hok
    dsimp [checkTokenModel] at hok
    split at hok
    · assumption
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ctx tok raw next start msg herr
    dsimp [checkTokenModel] at herr
    split at herr
    · contradiction
    · rename_i hns
      rcases tokenSafe_dichotomy ctx tok raw next with hs | hr
      · exact absurd hs hns
      · exact hr
  exact nomatch hp

theorem checkToken_o2 : O2 checkTokenRecord := by
  refine (o2_correct _).mpr ⟨⟨checkTokenModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(emptyCtx, .missing, "x", ' '), tokenSafe_emptyCtx⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(emptyCtx, .missing, "--", ' '), tokenUnsafe_check⟩
  exact nomatch hp

theorem checkToken_o2Run : O2Run checkTokenRecord :=
  o2Run_of_meets checkTokenModel_meets

theorem checkToken_o3 : O3 checkTokenRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ _ _ _ => .ok (), fun h => ?_⟩
    have hts := h emptyCtx .missing "--" ' ' 0 rfl
    rcases hts with h1 | h1 | ⟨hno, _⟩
    · simp [literalToken] at h1
    · simp [registeredSymbol] at h1
    · rw [containsOpener_dash] at hno; contradiction
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ _ _ _ => .error "always", fun h => ?_⟩
    have htr := h emptyCtx .missing "x" ' ' 0 "always" rfl
    cases htr with
    | openerInRaw _ _ hop => rw [containsOpener_x] at hop; contradiction
    | boundaryCross _ _ hcr =>
      have : crossesBoundary "x" ' ' = false := crossesBoundary_x_space
      rw [this] at hcr; contradiction
  exact nomatch hc

theorem checkToken_o4 : O4 checkTokenRecord := o4_function _ rfl

def CheckTokenFreedom : Freedom CheckTokenFn :=
  .rel fun f g => ∀ ctx tok raw next start, (f ctx tok raw next start).toOption = (g ctx tok raw next start).toOption

theorem checkToken_o5 : O5 checkTokenRecord CheckTokenFreedom := by
  refine ⟨fun f g hf hg ctx tok raw next start => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self ctx tok raw next start
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) ctx tok raw next start
  have hgok := hg.2 _ List.mem_cons_self ctx tok raw next start
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) ctx tok raw next start
  cases hfval : f ctx tok raw next start with
  | ok u =>
    cases u
    have hts := hfok hfval
    cases hgval : g ctx tok raw next start with
    | ok v => cases v; rfl
    | error msg =>
      exfalso
      have htr := hgerr msg hgval
      cases htr with
      | openerInRaw hl hs ho =>
        rcases hts with h1 | h1 | ⟨h1, _⟩ <;> simp_all
      | boundaryCross hl hs hc =>
        rcases hts with h1 | h1 | ⟨_, h1⟩ <;> simp_all
  | error msg =>
    have htr := hferr msg hfval
    cases hgval : g ctx tok raw next start with
    | error _ => rfl
    | ok v =>
      exfalso
      cases v
      have hts := hgok hgval
      cases htr with
      | openerInRaw hl hs ho =>
        rcases hts with h1 | h1 | ⟨h1, _⟩ <;> simp_all
      | boundaryCross hl hs hc =>
        rcases hts with h1 | h1 | ⟨_, h1⟩ <;> simp_all

theorem checkToken_not_o5_eq : ¬ O5 checkTokenRecord .eq := by
  let m2 : CheckTokenFn := open Classical in
    fun ctx tok raw next _ => if TokenSafe ctx tok raw next then .ok () else .error "rejected"
  have hm2 : checkTokenRecord.Meets m2 := by
    refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · intro ctx tok raw next start hok
      dsimp [m2] at hok; split at hok
      · assumption
      · contradiction
    rcases List.mem_cons.mp hp with rfl | hp
    · intro ctx tok raw next start msg herr
      dsimp [m2] at herr; split at herr
      · contradiction
      · rename_i hns
        rcases tokenSafe_dichotomy ctx tok raw next with hs | hr
        · exact absurd hs hns
        · exact hr
    exact nomatch hp
  refine not_o5_eq checkTokenModel_meets hm2 fun heq => ?_
  have hdiff := congrFun (congrFun (congrFun (congrFun (congrFun heq emptyCtx) .missing) "--") ' ') 0
  dsimp [checkTokenModel, m2] at hdiff
  have hns : ¬ TokenSafe emptyCtx .missing "--" ' ' := by
    intro h
    rcases h with h1 | h1 | ⟨h1, _⟩
    · simp [literalToken] at h1
    · simp [registeredSymbol] at h1
    · rw [containsOpener_dash] at h1; contradiction
  simp [hns] at hdiff

theorem checkToken_interim_const_fails :
    ∀ c, ¬ checkTokenRecord.Meets (fun _ _ _ _ _ => c) := by
  intro c hm
  cases c with
  | ok u =>
    have hts := hm.2 _ List.mem_cons_self emptyCtx .missing "--" ' ' 0 rfl
    rcases hts with h1 | h1 | ⟨h1, _⟩
    · simp [literalToken] at h1
    · simp [registeredSymbol] at h1
    · rw [containsOpener_dash] at h1; contradiction
  | error msg =>
    have htr := hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) emptyCtx .missing "x" ' ' 0 msg rfl
    cases htr with
    | openerInRaw _ _ ho => rw [containsOpener_x] at ho; contradiction
    | boundaryCross _ _ hc => rw [crossesBoundary_x_space] at hc; contradiction

theorem checkToken_healthy_owed :
    ∀ f ctx tok raw next start, checkTokenRecord.Meets f →
      Healthy.Token ctx tok raw next → ∃ u, f ctx tok raw next start = .ok u := by
  intro f ctx tok raw next start hf hh
  cases hfv : f ctx tok raw next start with
  | ok u => exact ⟨u, rfl⟩
  | error msg =>
    exfalso
    have hr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) ctx tok raw next start msg hfv
    exact token_healthy_and_refusal_disjoint ctx tok raw next hr hh

theorem checkToken_negative_external_model :
    ∃ (f : CheckTokenFn), ∃ ctx tok raw next start,
      (∀ c t r n s, f c t r n s = .ok () → TokenSafe c t r n) ∧
      Healthy.Token ctx tok raw next ∧
      ¬ ∃ u, f ctx tok raw next start = .ok u := by
  refine ⟨fun _ _ _ _ _ => .error "denied", emptyCtx, .missing, "x", ' ', 0, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ h; contradiction
  · right; right; decide
  · intro ⟨_, h⟩; contradiction

theorem checkToken_oPair_whole :
    ∀ c ∈ checkTokenRecord.props, OPair (Pair.whole checkTokenRecord c) checkTokenRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨checkTokenModel, checkTokenModel_meets, fun _ => checkTokenModel_meets.2 c hc⟩

def checkTokenPerInputPair : Pair CheckTokenFn where
  Input := Parser.ParserContextCore × Syntax × String × Char × String.Pos.Raw
  pre := fun _ => True
  post := fun i f => f i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 = .ok () →
    TokenSafe i.1 i.2.1 i.2.2.1 i.2.2.2.1

theorem checkToken_perInput_pairOf :
    checkTokenRecord.PairOf checkTokenOkClause checkTokenPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, checkTokenRecord, checkTokenOkClause, Pair.Met, checkTokenPerInputPair]

theorem checkToken_perInput_table_attack :
    ∀ i : checkTokenPerInputPair.Input, checkTokenPerInputPair.pre i →
      ∃ f : CheckTokenFn, (∀ a b c d e, f a b c d e = f emptyCtx .missing "" ' ' 0) ∧
        checkTokenPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ _ _ _ _ => .error "table", fun _ _ _ _ _ => rfl, ?_⟩
  intro h; contradiction

def distinctClause : Clause DistinctLinesFn :=
  ⟨"exact_distinct_comment_line_count", fun f => ∀ comments, DistinctLines comments (f comments)⟩

def addRangeLines (lo hi : Nat) (acc : List Nat) : List Nat :=
  (List.range (hi + 1 - lo)).foldl (fun l d =>
    let x := lo + d
    if x ∈ l then l else x :: l) acc

theorem addRangeLines_nodup {lo hi : Nat} {acc : List Nat} (h : acc.Nodup) :
    (addRangeLines lo hi acc).Nodup := by
  dsimp [addRangeLines]
  induction (List.range (hi + 1 - lo)) generalizing acc with
  | nil => exact h
  | cons d ds ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · exact List.nodup_cons.mpr ⟨‹_›, h⟩

theorem mem_addRangeLines {lo hi : Nat} {acc : List Nat} {l : Nat} :
    l ∈ addRangeLines lo hi acc ↔ (l ∈ acc ∨ (lo ≤ l ∧ l ≤ hi)) := by
  dsimp [addRangeLines]
  suffices ∀ (xs : List Nat) (a : List Nat),
      l ∈ xs.foldl (fun cur d => let x := lo + d; if x ∈ cur then cur else x :: cur) a ↔
        (l ∈ a ∨ ∃ d ∈ xs, l = lo + d) by
    rw [this]
    constructor
    · rintro (ha | ⟨d, hd, rfl⟩)
      · exact .inl ha
      · rw [List.mem_range] at hd
        exact .inr ⟨Nat.le_add_right _ _, by omega⟩
    · rintro (ha | ⟨hlo, hhi⟩)
      · exact .inl ha
      · refine .inr ⟨l - lo, List.mem_range.mpr (by omega), by omega⟩
  intro xs
  induction xs with
  | nil => intro a; simp
  | cons d ds ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rename_i hm
      constructor
      · rintro (ha | ⟨d', hd', rfl⟩)
        · exact .inl ha
        · exact .inr ⟨d', List.mem_cons_of_mem _ hd', rfl⟩
      · rintro (ha | ⟨d', hd', rfl⟩)
        · exact .inl ha
        · rcases List.mem_cons.mp hd' with rfl | hd''
          · exact .inl hm
          · exact .inr ⟨d', hd'', rfl⟩
    · simp only [List.mem_cons]
      constructor
      · rintro ((rfl | ha) | ⟨d', hd', rfl⟩)
        · exact .inr ⟨d, Or.inl rfl, rfl⟩
        · exact .inl ha
        · exact .inr ⟨d', Or.inr hd', rfl⟩
      · rintro (ha | ⟨d', hd', rfl⟩)
        · exact .inl (.inr ha)
        · rcases hd' with rfl | hd''
          · exact .inl (.inl rfl)
          · exact .inr ⟨d', hd'', rfl⟩

def distinctLinesRefList (cs : List Core.Comment) : List Nat :=
  cs.foldl (fun acc c => addRangeLines c.startLine c.endLine acc) []

theorem distinctLinesRefList_nodup (cs : List Core.Comment) :
    (distinctLinesRefList cs).Nodup := by
  dsimp [distinctLinesRefList]
  suffices ∀ acc : List Nat, acc.Nodup →
      (cs.foldl (fun a c => addRangeLines c.startLine c.endLine a) acc).Nodup from
    this [] List.nodup_nil
  induction cs with
  | nil => intro acc h; exact h
  | cons c rest ih =>
    intro acc h
    exact ih _ (addRangeLines_nodup h)

theorem mem_distinctLinesRefList (cs : List Core.Comment) (l : Nat) :
    l ∈ distinctLinesRefList cs ↔ ∃ c ∈ cs, c.startLine ≤ l ∧ l ≤ c.endLine := by
  dsimp [distinctLinesRefList]
  suffices ∀ acc : List Nat,
      l ∈ cs.foldl (fun a c => addRangeLines c.startLine c.endLine a) acc ↔
        l ∈ acc ∨ ∃ c ∈ cs, c.startLine ≤ l ∧ l ≤ c.endLine by
    simpa using this []
  induction cs with
  | nil => intro acc; simp
  | cons c rest ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, mem_addRangeLines]
    constructor
    · rintro ((ha | h1) | ⟨c', hc', h2⟩)
      · exact .inl ha
      · exact .inr ⟨c, List.mem_cons_self, h1⟩
      · exact .inr ⟨c', List.mem_cons.mpr (.inr hc'), h2⟩
    · rintro (ha | ⟨c', hc', h2⟩)
      · exact .inl (.inl ha)
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · exact .inl (.inr h2)
        · exact .inr ⟨c', hc'', h2⟩

def distinctLinesModel : DistinctLinesFn :=
  fun cs => (distinctLinesRefList cs.toList).length

theorem distinctLinesModel_meets : distinctCommentLinesRecord.Meets distinctLinesModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro cs
    exact ⟨distinctLinesRefList cs.toList, distinctLinesRefList_nodup _,
      mem_distinctLinesRefList _, rfl⟩
  exact nomatch hp

theorem distinctCommentLines_o2 : O2 distinctCommentLinesRecord := by
  refine (o2_correct _).mpr ⟨⟨distinctLinesModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(#[], 0), [], List.nodup_nil, by simp, rfl⟩
  exact nomatch hp

theorem distinctCommentLines_o2Run : O2Run distinctCommentLinesRecord :=
  o2Run_of_meets distinctLinesModel_meets

theorem distinctCommentLines_o3 : O3 distinctCommentLinesRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => 1, fun h => ?_⟩
    obtain ⟨ls, _, hmem, hlen⟩ := h #[]
    cases ls with
    | nil => simp at hlen
    | cons x _ =>
      have := (hmem x).mp List.mem_cons_self
      simp at this
  exact nomatch hc

theorem distinctCommentLines_o4 : O4 distinctCommentLinesRecord := o4_function _ rfl

theorem distinctCommentLines_o5 : O5 distinctCommentLinesRecord .eq := by
  refine ⟨fun f g hf hg => funext fun cs => ?_, trivial⟩
  obtain ⟨ls1, hnd1, hm1, hl1⟩ := hf.2 _ List.mem_cons_self cs
  obtain ⟨ls2, hnd2, hm2, hl2⟩ := hg.2 _ List.mem_cons_self cs
  have hperm : ls1.Perm ls2 :=
    (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun x => (hm1 x).trans (hm2 x).symm
  rw [hl1, hl2, hperm.length_eq]

theorem distinctCommentLines_oPair_whole :
    ∀ c ∈ distinctCommentLinesRecord.props,
      OPair (Pair.whole distinctCommentLinesRecord c) distinctCommentLinesRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨distinctLinesModel, distinctLinesModel_meets, fun _ => distinctLinesModel_meets.2 c hc⟩

def distinctPerInputPair : Pair DistinctLinesFn where
  Input := Array Core.Comment
  pre := fun _ => True
  post := fun cs f => DistinctLines cs (f cs)

theorem distinct_perInput_pairOf :
    distinctCommentLinesRecord.PairOf distinctClause distinctPerInputPair := by
  refine ⟨List.mem_cons_self, fun f => ?_⟩
  simp [IntentRecord.Dom, distinctCommentLinesRecord, distinctClause, Pair.Met, distinctPerInputPair]

theorem distinct_perInput_oPair_table : OPair distinctPerInputPair Witness.Constant := by
  refine ⟨⟨#[], trivial⟩, ?_, trivial⟩
  intro cs _
  exact ⟨fun _ => distinctLinesModel cs, ⟨distinctLinesModel cs, funext fun _ => rfl⟩,
    distinctLinesModel_meets.2 _ List.mem_cons_self cs⟩

theorem distinctCommentLines_verdicts : Verdicts distinctCommentLinesRecord [false] := by
  refine ⟨fun h => ?_, trivial⟩
  obtain ⟨ls, _, hmem, hlen⟩ := h.2 _ List.mem_cons_self #[sampleComment1]
  have h1 : 1 ∈ ls := (hmem 1).mpr ⟨sampleComment1, by simp [sampleComment1], by decide, by decide⟩
  cases ls with
  | nil => contradiction
  | cons _ _ =>
    change (fun _ : Array Core.Comment => 0) #[sampleComment1] = _ at hlen
    simp at hlen

theorem distinctCommentLines_witnesses_whole :
    WitnessVerdicts (Pair.whole distinctCommentLinesRecord distinctClause) [false, false, false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun h => ?_, trivial⟩
  · obtain ⟨ls, _, hmem, hlen⟩ := h (fun _ => 1) () trivial (fun _ hc => nomatch hc) #[]
    cases ls with
    | nil => simp at hlen
    | cons x _ => have := (hmem x).mp List.mem_cons_self; simp at this
  · obtain ⟨w, ⟨c, rfl⟩, hw⟩ := h () trivial
    obtain ⟨ls0, _, hm0, hl0⟩ := hw (fun _ hc => nomatch hc) #[]
    obtain ⟨ls1, _, hm1, hl1⟩ := hw (fun _ hc => nomatch hc) #[sampleComment1]
    have hnil : ls0 = [] := by
      cases ls0 with
      | nil => rfl
      | cons x _ => have := (hm0 x).mp List.mem_cons_self; simp at this
    subst hnil
    have h1 : 1 ∈ ls1 := (hm1 1).mpr ⟨sampleComment1, by simp [sampleComment1], by decide, by decide⟩
    have hc0 : Degenerate.constantSubject c #[] = c := rfl
    have hc1 : Degenerate.constantSubject c #[sampleComment1] = c := rfl
    rw [hc0] at hl0
    rw [hc1] at hl1
    cases ls1 with
    | nil => contradiction
    | cons _ _ =>
      dsimp [Covered.sig, Sig.ofTy, ExactCode.code, Ty.denote] at c hl0 hl1
      rw [hl0] at hl1
      omega
  · subst e
    obtain ⟨ls, _, hmem, hlen⟩ := h () trivial (fun _ hc => nomatch hc) #[sampleComment1]
    have h1 : 1 ∈ ls := (hmem 1).mpr ⟨sampleComment1, by simp [sampleComment1], by decide, by decide⟩
    cases ls with
    | nil => contradiction
    | cons _ _ =>
      change (fun _ : Array Core.Comment => 0) #[sampleComment1] = _ at hlen
      simp at hlen
  · obtain ⟨w, htimed, hw⟩ := h () trivial
    let a1 := (HasCode.iso (α := Array Core.Comment)).to #[sampleComment1]
    let a13 := (HasCode.iso (α := Array Core.Comment)).to #[sampleComment13]
    have hread_eq : ∀ a : Array (HasCode.code Core.Comment).denote,
        Sig.Fn.apply (Covered.iso.to w) (a, ()) = w (HasCode.iso.inv a) := fun _ => rfl
    have hsame_raw := htimed (a1, ()) (a13, ()) (by
      simp only [ArgClock.read, ClockRead.read, Place.ArgPath.read, Place.Path.get,
        Place.viewIso, Place.viewOf, Place.Count.read, Ty.viewOf, Iso.refl, a1, a13, HasCode.iso,
        Iso.array, Array.size_map]
      rfl)
    rw [hread_eq, hread_eq, Iso.inv_to, Iso.inv_to] at hsame_raw
    obtain ⟨lsA, hndA, hmA, hlA⟩ := hw (fun _ hc => nomatch hc) #[sampleComment1]
    obtain ⟨lsB, hndB, hmB, hlB⟩ := hw (fun _ hc => nomatch hc) #[sampleComment13]
    have ha1 : lsA.length = 1 := by
      have hperm : lsA.Perm [1] := (List.perm_ext_iff_of_nodup hndA (by decide)).mpr fun x => by
        rw [hmA x]; simp [sampleComment1]; omega
      exact hperm.length_eq
    have hb3 : lsB.length = 3 := by
      have hperm : lsB.Perm [1, 2, 3] := (List.perm_ext_iff_of_nodup hndB (by decide)).mpr fun x => by
        rw [hmB x]; simp [sampleComment13]; omega
      exact hperm.length_eq
    rw [hsame_raw, hlB, hb3] at hlA
    omega

def firstOutClause : Clause FirstOutOfOrderFn :=
  ⟨"first_descending_neighbor", fun f => ∀ l, FirstOutOfOrderSpec l (f l)⟩

def firstOutOfOrderModel : FirstOutOfOrderFn
  | [] => none
  | [_] => none
  | a :: b :: rest => if b < a then some b else firstOutOfOrderModel (b :: rest)

theorem firstOutOfOrderModel_spec (l : List String) :
    FirstOutOfOrderSpec l (firstOutOfOrderModel l) := by
  induction l with
  | nil => simp [firstOutOfOrderModel, FirstOutOfOrderSpec]
  | cons a rest ih =>
    cases rest with
    | nil => simp [firstOutOfOrderModel, FirstOutOfOrderSpec]
    | cons b tail =>
      dsimp [firstOutOfOrderModel]
      by_cases hlt : b < a
      · simp only [hlt, ↓reduceIte]
        constructor
        · constructor
          · intro hc; contradiction
          · intro hp
            have hle : a ≤ b := (List.pairwise_cons.mp hp).1 b List.mem_cons_self
            exact absurd hlt (Std.not_lt.mpr hle)
        · intro x hx
          cases hx
          exact ⟨[], a, tail, rfl, List.pairwise_singleton _ _, hlt⟩
      · simp only [hlt, ↓reduceIte]
        have hle : a ≤ b := Std.not_lt.mp hlt
        obtain ⟨hiff, hsome⟩ := ih
        constructor
        · rw [hiff]
          constructor
          · intro hpb
            refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hpb⟩
            rcases List.mem_cons.mp hy with rfl | hyt
            · exact hle
            · exact Std.le_trans hle ((List.pairwise_cons.mp hpb).1 y hyt)
          · exact fun h => (List.pairwise_cons.mp h).2
        · intro x hx
          obtain ⟨pfx, a', sfx, heq, hpfx, hlt'⟩ := hsome x hx
          refine ⟨a :: pfx, a', sfx, by simp [heq], ?_, hlt'⟩
          rw [List.cons_append, List.pairwise_cons]
          refine ⟨fun y hy => ?_, hpfx⟩
          have hhead : ∃ rest', pfx ++ [a'] = b :: rest' := by
            cases pfx with
            | nil =>
              simp only [List.nil_append] at heq
              cases heq
              exact ⟨[], rfl⟩
            | cons p0 ps =>
              simp only [List.cons_append] at heq
              cases heq
              exact ⟨ps ++ [a'], rfl⟩
          obtain ⟨rest', hpb⟩ := hhead
          rw [hpb] at hpfx hy
          rcases List.mem_cons.mp hy with rfl | hyr
          · exact hle
          · exact Std.le_trans hle ((List.pairwise_cons.mp hpfx).1 y hyr)

theorem firstOutOfOrderModel_meets : firstOutOfOrderRecord.Meets firstOutOfOrderModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact firstOutOfOrderModel_spec
  exact nomatch hp

theorem firstOutOfOrder_o2 : O2 firstOutOfOrderRecord := by
  refine (o2_correct _).mpr ⟨⟨firstOutOfOrderModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨([], none), by simp, fun b hb => by contradiction⟩
  exact nomatch hp

theorem firstOutOfOrder_o2Run : O2Run firstOutOfOrderRecord :=
  o2Run_of_meets firstOutOfOrderModel_meets

theorem firstOutOfOrder_o3 : O3 firstOutOfOrderRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => some "", fun h => ?_⟩
    have := (h []).1.mpr List.Pairwise.nil
    contradiction
  exact nomatch hc

theorem firstOutOfOrder_o4 : O4 firstOutOfOrderRecord := o4_function _ rfl

theorem firstOutOfOrder_o5 : O5 firstOutOfOrderRecord .eq := by
  refine ⟨fun f g hf hg => funext fun l => ?_, trivial⟩
  have ⟨hiff1, hs1⟩ := hf.2 _ List.mem_cons_self l
  have ⟨hiff2, hs2⟩ := hg.2 _ List.mem_cons_self l
  cases hfval : f l with
  | none =>
    cases hgval : g l with
    | none => rfl
    | some y =>
      have hp := hiff1.mp hfval
      obtain ⟨pfx, a, sfx, heq, _, hlt⟩ := hs2 y hgval
      rw [heq, List.append_assoc] at hp
      have hpa := (List.pairwise_append.mp hp).2.1
      have ha_le : a ≤ y := (List.pairwise_cons.mp hpa).1 y List.mem_cons_self
      exact absurd hlt (Std.not_lt.mpr ha_le)
  | some x =>
    cases hgval : g l with
    | none =>
      have hp := hiff2.mp hgval
      obtain ⟨pfx, a, sfx, heq, _, hlt⟩ := hs1 x hfval
      rw [heq, List.append_assoc] at hp
      have hpa := (List.pairwise_append.mp hp).2.1
      have ha_le : a ≤ x := (List.pairwise_cons.mp hpa).1 x List.mem_cons_self
      exact absurd hlt (Std.not_lt.mpr ha_le)
    | some y =>
      obtain ⟨pfx1, a1, sfx1, heq1, hp1, hlt1⟩ := hs1 x hfval
      obtain ⟨pfx2, a2, sfx2, heq2, hp2, hlt2⟩ := hs2 y hgval
      have hnotlt : ∀ p1 a1' x' s1 p2 a2' y' s2,
          l = p1 ++ [a1', x'] ++ s1 → l = p2 ++ [a2', y'] ++ s2 →
          (p1 ++ [a1']).Pairwise (· ≤ ·) → (p2 ++ [a2']).Pairwise (· ≤ ·) →
          x' < a1' → y' < a2' → ¬ p1.length < p2.length := by
        intro p1 a1' x' s1 p2 a2' y' s2 e1 e2 _ hpp2 hxlt _ hlt_len
        have hidx1 : (p1 ++ [a1', x'] ++ s1)[p1.length + 1]? = some x' := by simp [List.append_assoc]
        have hidx0 : (p1 ++ [a1', x'] ++ s1)[p1.length]? = some a1' := by simp [List.append_assoc]
        have h_in_p2_a : (p2 ++ [a2', y'] ++ s2)[p1.length]? = some p2[p1.length] := by
          rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_eq_getElem hlt_len]
        have h_in_p2_x : (p2 ++ [a2', y'] ++ s2)[p1.length + 1]? =
            some ((p2 ++ [a2'])[p1.length + 1]'(by rw [List.length_append, List.length_singleton]; omega)) := by
          rw [List.append_assoc]
          have heq_p2 : p2 ++ ([a2', y'] ++ s2) = (p2 ++ [a2']) ++ (y' :: s2) := by simp
          rw [heq_p2, List.getElem?_append_left (by simp; omega),
            List.getElem?_eq_getElem (by rw [List.length_append, List.length_singleton]; omega)]
        rw [← e1, e2] at hidx0 hidx1
        rw [hidx0] at h_in_p2_a
        rw [hidx1] at h_in_p2_x
        injection h_in_p2_a with ha1_eq
        injection h_in_p2_x with hx_eq
        have hp2' := (List.pairwise_iff_getElem.mp hpp2) p1.length (p1.length + 1)
          (by simp; omega) (by simp; omega) (by omega)
        rw [List.getElem_append_left hlt_len] at hp2'
        rw [ha1_eq, hx_eq] at hxlt
        exact absurd hxlt (Std.not_lt.mpr hp2')
      have hlen : pfx1.length = pfx2.length := by
        have h1 := hnotlt pfx1 a1 x sfx1 pfx2 a2 y sfx2 heq1 heq2 hp1 hp2 hlt1 hlt2
        have h2 := hnotlt pfx2 a2 y sfx2 pfx1 a1 x sfx1 heq2 heq1 hp2 hp1 hlt2 hlt1
        omega
      have h_x : (pfx1 ++ [a1, x] ++ sfx1)[pfx1.length + 1]? = some x := by simp [List.append_assoc]
      have h_y : (pfx2 ++ [a2, y] ++ sfx2)[pfx2.length + 1]? = some y := by simp [List.append_assoc]
      rw [← hlen, ← heq2, heq1, h_x] at h_y
      exact h_y

theorem firstOutOfOrder_oPair_whole :
    ∀ c ∈ firstOutOfOrderRecord.props,
      OPair (Pair.whole firstOutOfOrderRecord c) firstOutOfOrderRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨firstOutOfOrderModel, firstOutOfOrderModel_meets, fun _ => firstOutOfOrderModel_meets.2 c hc⟩

theorem firstOutOfOrder_verdicts : Verdicts firstOutOfOrderRecord [false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, trivial⟩
  · have := (h.2 _ List.mem_cons_self ["b", "a"]).1.mp rfl
    have hba : "b" ≤ "a" := (List.pairwise_cons.mp this).1 "a" List.mem_cons_self
    exact (by decide : ¬ ['b'] ≤ ['a']) (String.toList_le_toList_iff.mpr hba)
  · have hzero := (h.2 _ List.mem_cons_self []).1.mpr List.Pairwise.nil
    have hcs : @Degenerate.constantSubject FirstOutOfOrderFn _ (some "") [] = some "" := rfl
    rw [hcs] at hzero
    contradiction

theorem firstOutOfOrder_witnesses_whole :
    WitnessVerdicts (Pair.whole firstOutOfOrderRecord firstOutClause)
      [false, false, false, false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, fun h => ?_, trivial⟩
  · have := (h (fun _ => some "") () trivial (fun _ hc => nomatch hc) []).1.mpr List.Pairwise.nil
    contradiction
  · obtain ⟨w, ⟨c, rfl⟩, hw⟩ := h () trivial
    have hnil := (hw (fun _ hc => nomatch hc) []).1.mpr List.Pairwise.nil
    have hc0 : @Degenerate.constantSubject FirstOutOfOrderFn _ c [] = c := rfl
    have hc1 : @Degenerate.constantSubject FirstOutOfOrderFn _ c ["b", "a"] = c := rfl
    rw [hc0] at hnil
    subst hnil
    have hbad := (hw (fun _ hc => nomatch hc) ["b", "a"]).1.mp hc1
    have hba : "b" ≤ "a" := (List.pairwise_cons.mp hbad).1 "a" List.mem_cons_self
    exact (by decide : ¬ ['b'] ≤ ['a']) (String.toList_le_toList_iff.mpr hba)
  · subst e
    have hc1 : @Degenerate.constantSubject FirstOutOfOrderFn _ none ["b", "a"] = none := rfl
    have hbad := (h () trivial (fun _ hc => nomatch hc) ["b", "a"]).1.mp hc1
    have hba : "b" ≤ "a" := (List.pairwise_cons.mp hbad).1 "a" List.mem_cons_self
    exact (by decide : ¬ ['b'] ≤ ['a']) (String.toList_le_toList_iff.mpr hba)
  · subst e
    have hzero := (h () trivial (fun _ hc => nomatch hc) []).1.mpr List.Pairwise.nil
    have hcs : @Degenerate.constantSubject FirstOutOfOrderFn _ (some "") [] = some "" := rfl
    rw [hcs] at hzero
    contradiction
  · obtain ⟨w, htimed, hw⟩ := h () trivial
    have hread :
        ∀ xs ys : Sig.Args (Covered.sig FirstOutOfOrderFn).args,
          (Sig.Fn.apply (Covered.iso.to w) xs = Sig.Fn.apply (Covered.iso.to w) ys) ↔
            w xs.1 = w ys.1 :=
      fun ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ => Iff.rfl
    have hsame := htimed (["a", "b"], ()) (["b", "a"], ()) rfl
    rw [hread] at hsame
    have hab_le : "a" ≤ "b" := String.toList_le_toList_iff.mp (by decide)
    have hab : w ["a", "b"] = none :=
      (hw (fun _ hc => nomatch hc) ["a", "b"]).1.mpr (List.pairwise_cons.mpr ⟨by simp [hab_le], List.pairwise_singleton _ _⟩)
    have hba := (hw (fun _ hc => nomatch hc) ["b", "a"]).1.mp (by rw [← hsame, hab])
    have hle : "b" ≤ "a" := (List.pairwise_cons.mp hba).1 "a" List.mem_cons_self
    exact (by decide : ¬ ['b'] ≤ ['a']) (String.toList_le_toList_iff.mpr hle)

def sourceOrderModel : SourceOrderFn :=
  fun acc => (acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2.2) |>.toArray

theorem sourceOrderModel_spec (acc : Core.CommentAcc) :
    SourceOrdered acc (sourceOrderModel acc) := by
  refine ⟨acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1)), ?_, ?_, by simp [sourceOrderModel]⟩
  · have hperm : (acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).Perm acc.spans.toList :=
      List.mergeSort_perm _ _
    have hdist : (acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise
        (fun a b => (a.1 == b.1) = false) := by
      have hd := Std.HashMap.distinct_keys_toList (m := acc.spans)
      exact hd.perm hperm.symm fun {a b} h => by
        simp only [beq_eq_false_iff_ne, ne_eq] at h ⊢
        exact Ne.symm h
    have hle : (acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise
        (fun a b => a.1 ≤ b.1) := by
      simpa using List.pairwise_mergeSort
        (le := fun a b : Nat × Nat × Core.Comment => decide (a.1 ≤ b.1))
        (fun _ _ _ h1 h2 => by simp_all; omega)
        (fun _ _ => by simp; omega)
        acc.spans.toList
    refine (hdist.and hle).imp ?_
    intro a b ⟨hne, hle'⟩
    have hneq : (a.fst == b.fst) = false := hne
    simp only [beq_eq_false_iff_ne] at hneq
    omega
  · intro sb eb c
    have hperm : (acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).Perm acc.spans.toList :=
      List.mergeSort_perm _ _
    rw [hperm.mem_iff, Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem sourceOrderModel_meets : sourceOrderRecord.Meets sourceOrderModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact sourceOrderModel_spec
  exact nomatch hp

theorem sourceOrder_o2 : O2 sourceOrderRecord := by
  refine (o2_correct _).mpr ⟨⟨sourceOrderModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨({}, #[]), [], List.Pairwise.nil, by simp, rfl⟩
  exact nomatch hp

theorem sourceOrder_o2Run : O2Run sourceOrderRecord :=
  o2Run_of_meets sourceOrderModel_meets

theorem sourceOrder_o3 : O3 sourceOrderRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => #[], fun h => ?_⟩
    obtain ⟨entries, _, hm, hl⟩ := h { spans := ({} : Std.HashMap Nat (Nat × Core.Comment)).insert 0 (1, sampleComment1) }
    have hmem : (0, 1, sampleComment1) ∈ entries := (hm 0 1 sampleComment1).mpr (by simp)
    cases entries with
    | nil => contradiction
    | cons _ _ => simp at hl
  exact nomatch hc

theorem sourceOrder_o4 : O4 sourceOrderRecord := o4_function _ rfl

theorem sourceOrder_o5 : O5 sourceOrderRecord .eq := by
  refine ⟨fun f g hf hg => funext fun acc => ?_, trivial⟩
  obtain ⟨e1, hp1, hm1, hl1⟩ := hf.2 _ List.mem_cons_self acc
  obtain ⟨e2, hp2, hm2, hl2⟩ := hg.2 _ List.mem_cons_self acc
  have hnodup1 : e1.Nodup := hp1.imp fun h => by intro heq; rw [heq] at h; omega
  have hnodup2 : e2.Nodup := hp2.imp fun h => by intro heq; rw [heq] at h; omega
  have hperm : e1.Perm e2 := (List.perm_ext_iff_of_nodup hnodup1 hnodup2).mpr fun ⟨sb, eb, c⟩ =>
    (hm1 sb eb c).trans (hm2 sb eb c).symm
  have heq_list : e1 = e2 :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd h1 (by omega)) hp1 hp2 hperm
  apply Array.ext'
  rw [hl1, hl2, heq_list]

theorem sourceOrder_interim_const_fails :
    ∀ c, ¬ sourceOrderRecord.Meets (fun _ => c) := by
  intro c hm
  by_cases hnil : c.toList = []
  · obtain ⟨entries, _, hm1, hl1⟩ := hm.2 _ List.mem_cons_self
      { spans := ({} : Std.HashMap Nat (Nat × Core.Comment)).insert 0 (1, sampleComment1) }
    have hmem : (0, 1, sampleComment1) ∈ entries := (hm1 0 1 sampleComment1).mpr (by simp)
    rw [hnil] at hl1
    cases entries with
    | nil => contradiction
    | cons _ _ => simp at hl1
  · obtain ⟨entries, _, hm0, hl0⟩ := hm.2 _ List.mem_cons_self { spans := {} }
    have hnil_e : entries = [] := by
      cases entries with
      | nil => rfl
      | cons hd _ =>
        have := (hm0 hd.1 hd.2.1 hd.2.2).mp List.mem_cons_self
        simp at this
    subst hnil_e
    have hl0' : c.toList = [] := by simp [hl0]
    exact hnil hl0'

theorem sourceOrder_oPair_whole :
    ∀ c ∈ sourceOrderRecord.props, OPair (Pair.whole sourceOrderRecord c) sourceOrderRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨sourceOrderModel, sourceOrderModel_meets, fun _ => sourceOrderModel_meets.2 c hc⟩

def sortFpModel : SortFingerprintsFn :=
  fun xs =>
    ⟨(xs.toList.mergeSort (fun a b => decide (a ≤ b))).toArray, by
      simpa using List.pairwise_mergeSort (le := fun a b : String => decide (a ≤ b))
        (fun _ _ _ h1 h2 => by simp_all; exact Std.le_trans h1 h2)
        (fun a b => by simp; exact Std.Total.total a b)
        xs.toList⟩

theorem sortFpModel_meets : sortFingerprintsRecord.Meets sortFpModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro xs a
    simpa [sortFpModel] using (List.mergeSort_perm xs.toList (fun x y => decide (x ≤ y))).count_eq a
  exact nomatch hp

theorem sortFingerprints_o2 : O2 sortFingerprintsRecord := by
  refine (o2_correct _).mpr ⟨⟨sortFpModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨([], []), fun _ => rfl⟩
  exact nomatch hp

theorem sortFingerprints_o2Run : O2Run sortFingerprintsRecord :=
  o2Run_of_meets sortFpModel_meets

theorem sortFingerprints_o3 : O3 sortFingerprintsRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => Core.SortedFingerprints.empty, fun h => ?_⟩
    have := h #[zeroFp] zeroFp
    simp [Core.SortedFingerprints.empty] at this
  exact nomatch hc

theorem sortFingerprints_o4 : O4 sortFingerprintsRecord := o4_function _ rfl

theorem sortFingerprints_o5 : O5 sortFingerprintsRecord .eq := by
  refine ⟨fun f g hf hg => funext fun xs => ?_, trivial⟩
  have h1 := hf.2 _ List.mem_cons_self xs
  have h2 := hg.2 _ List.mem_cons_self xs
  have hperm : (f xs).values.toList.Perm (g xs).values.toList :=
    List.perm_iff_count.mpr fun a => (h1 a).trans (h2 a).symm
  have heq : (f xs).values.toList = (g xs).values.toList :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ hle1 hle2 => Std.le_antisymm hle1 hle2)
      (f xs).sorted (g xs).sorted hperm
  cases hfxs : f xs
  cases hgxs : g xs
  simp only [Core.SortedFingerprints.mk.injEq]
  apply Array.ext'
  simpa [hfxs, hgxs] using heq

theorem sortFingerprints_interim_const_fails :
    ∀ c, ¬ sortFingerprintsRecord.Meets (fun _ => c) := by
  intro c hm
  by_cases hnil : c.values.toList = []
  · have := hm.2 _ List.mem_cons_self #[zeroFp] zeroFp
    rw [hnil] at this
    simp at this
  · have := hm.2 _ List.mem_cons_self #[]
    cases hlist : c.values.toList with
    | nil => exact hnil hlist
    | cons x _ =>
      have hx := this x
      rw [hlist] at hx
      simp at hx

theorem sortFingerprints_oPair_whole :
    ∀ c ∈ sortFingerprintsRecord.props,
      OPair (Pair.whole sortFingerprintsRecord c) sortFingerprintsRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨sortFpModel, sortFpModel_meets, fun _ => sortFpModel_meets.2 c hc⟩

def missingFromModel : MissingFromFn :=
  fun xs ys => (ys.values.toList.foldl (fun acc y => acc.erase y) xs.values.toList).toArray

theorem missingFromModel_meets : missingFromRecord.Meets missingFromModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro xs ys a
    dsimp [missingFromModel]
    suffices ∀ (zs acc : List String),
        (zs.foldl (fun l y => l.erase y) acc).count a = acc.count a - zs.count a by
      simpa using this ys.values.toList xs.values.toList
    intro zs
    induction zs with
    | nil => intro acc; simp
    | cons z rest ih =>
      intro acc
      simp only [List.foldl_cons, List.count_cons]
      rw [ih, List.count_erase]
      split <;> rename_i h <;> simp_all <;> omega
  exact nomatch hp

theorem missingFrom_o2 : O2 missingFromRecord := by
  refine (o2_correct _).mpr ⟨⟨missingFromModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨([], [], []), fun _ => rfl⟩
  exact nomatch hp

theorem missingFrom_o2Run : O2Run missingFromRecord :=
  o2Run_of_meets missingFromModel_meets

theorem missingFrom_o3 : O3 missingFromRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun xs _ => xs.values, fun h => ?_⟩
    have := h ⟨#[zeroFp], List.pairwise_singleton _ _⟩ ⟨#[zeroFp], List.pairwise_singleton _ _⟩ zeroFp
    simp at this
  exact nomatch hc

theorem missingFrom_o4 : O4 missingFromRecord := o4_function _ rfl

def MissingFromFreedom : Freedom MissingFromFn :=
  .rel fun f g => ∀ xs ys, (f xs ys).toList.Perm (g xs ys).toList

theorem missingFrom_o5 : O5 missingFromRecord MissingFromFreedom := by
  refine ⟨fun f g hf hg xs ys => ?_, trivial⟩
  exact List.perm_iff_count.mpr fun a =>
    (hf.2 _ List.mem_cons_self xs ys a).trans (hg.2 _ List.mem_cons_self xs ys a).symm

theorem zeroFp_le_oneFp : zeroFp ≤ oneFp :=
  String.toList_le_toList_iff.mp (by decide)

def missingFromUnsortedModel : MissingFromFn :=
  fun xs ys => (ys.values.toList.foldl (fun acc y => acc.erase y) xs.values.toList).reverse.toArray

theorem missingFromUnsortedModel_meets : missingFromRecord.Meets missingFromUnsortedModel := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro xs ys a
    have h1 := missingFromModel_meets.2 _ List.mem_cons_self xs ys a
    simpa [missingFromUnsortedModel, missingFromModel, List.count_reverse] using h1
  exact nomatch hp

theorem missingFrom_not_o5_eq : ¬ O5 missingFromRecord .eq := by
  refine not_o5_eq missingFromModel_meets missingFromUnsortedModel_meets fun heq => ?_
  let xs : Core.SortedFingerprints :=
    ⟨#[zeroFp, oneFp], List.pairwise_cons.mpr ⟨by simp [zeroFp_le_oneFp], List.pairwise_singleton _ _⟩⟩
  have hdiff := congrFun (congrFun heq xs) Core.SortedFingerprints.empty
  have h1 : (missingFromModel xs Core.SortedFingerprints.empty).toList = [zeroFp, oneFp] := rfl
  have h2 : (missingFromUnsortedModel xs Core.SortedFingerprints.empty).toList = [oneFp, zeroFp] := rfl
  have := congrArg Array.toList hdiff
  rw [h1, h2] at this
  simp [zeroFp, oneFp] at this

theorem missingFrom_interim_degenerate :
    (∀ c, ¬ missingFromRecord.Meets (fun _ _ => c)) ∧
    (¬ missingFromRecord.Meets (fun xs _ => xs.values)) ∧
    (¬ missingFromRecord.Meets (fun _ ys => ys.values)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hm
    by_cases hnil : c.toList = []
    · have := hm.2 _ List.mem_cons_self ⟨#[zeroFp], List.pairwise_singleton _ _⟩ Core.SortedFingerprints.empty zeroFp
      rw [hnil] at this; simp [Core.SortedFingerprints.empty] at this
    · have := hm.2 _ List.mem_cons_self Core.SortedFingerprints.empty Core.SortedFingerprints.empty
      cases hcl : c.toList with
      | nil => exact hnil hcl
      | cons x _ =>
        have hx := this x
        rw [hcl] at hx
        simp [Core.SortedFingerprints.empty] at hx
  · intro hm
    have := hm.2 _ List.mem_cons_self ⟨#[zeroFp], List.pairwise_singleton _ _⟩ ⟨#[zeroFp], List.pairwise_singleton _ _⟩ zeroFp
    simp at this
  · intro hm
    have := hm.2 _ List.mem_cons_self Core.SortedFingerprints.empty ⟨#[zeroFp], List.pairwise_singleton _ _⟩ zeroFp
    simp [Core.SortedFingerprints.empty] at this

theorem missingFrom_oPair_whole :
    ∀ c ∈ missingFromRecord.props, OPair (Pair.whole missingFromRecord c) missingFromRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨missingFromModel, missingFromModel_meets, fun _ => missingFromModel_meets.2 c hc⟩

end NoCommentsSpecification.AdequacyCore
