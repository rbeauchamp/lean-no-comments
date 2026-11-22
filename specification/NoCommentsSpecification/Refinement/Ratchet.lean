module

import all Init.Data.Range.Basic
import all Lean.Data.Json.Basic
import all NoComments.Config
import all NoComments.Core
import all NoComments.RatchetCore
public import LeanIntent.Refinement
public import Std.Data.HashMap.Lemmas
public import NoCommentsSpecification.RatchetRecords
public import NoCommentsSpecification.Refinement.Core
public import NoCommentsSpecification.Refinement.Config

@[expose] public section

namespace NoCommentsSpecification.Refinement.Ratchet

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.RatchetSpec
open NoCommentsSpecification.RatchetRecords
open NoCommentsSpecification.Refinement.Config (except_bind_ok except_bind_err except_bind_assoc)

theorem analyzeComments_meets :
    analyzeCommentsRecord.Meets NoComments.RatchetCore.analyzeComments := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro file comments
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rcases NoComments.Core.distinctCommentLines_exact comments with ⟨ls, hpw, hiff, hlen⟩
      exact ⟨ls, List.Pairwise.imp (fun {a b} hlt => by omega) hpw, hiff, hlen⟩
    · intro a
      simpa [NoComments.RatchetCore.analyzeComments, Array.toList_map] using
        NoComments.Core.sortFingerprints_count (comments.map (·.fingerprint)) a
  exact nomatch hp

theorem analyzeComments_refines :
    Refines analyzeCommentsRecord (fun f => f) (· = NoComments.RatchetCore.analyzeComments) :=
  fun _ hf _ => hf ▸ analyzeComments_meets.2

theorem analyzeComments_fulfilled :
    analyzeCommentsRecord.Fulfilled NoComments.RatchetCore.analyzeComments :=
  fulfils analyzeComments_refines rfl

private theorem append_isEmpty (a b : Array String) :
    (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
  cases a with
  | mk l1 =>
    cases b with
    | mk l2 =>
      cases l1 <;> cases l2 <;> simp [Array.isEmpty]

private theorem forIn_congr_body {α β : Type} {m : Type → Type} [Monad m]
    (l : List α) (b : β) (f g : α → β → m (ForInStep β))
    (hfg : ∀ x s, f x s = g x s) :
    forIn l b f = forIn l b g := by
  congr 1; funext x s; exact hfg x s

private theorem ite_eq_true_elim {α : Type} (c : Bool) (t e : α) :
    (if c = true then t else e) = (match c with | true => t | false => e) := by
  cases c <;> rfl

private theorem array_push_isEmpty_false (a : Array String) (x : String) :
    (a.push x).isEmpty = false := by
  simp [Array.isEmpty]

theorem checkExactSync_iff (analysis : NoComments.RatchetCore.FileAnalysis)
    (entry? : Option NoComments.RatchetCore.RatchetEntry) :
    (NoComments.RatchetCore.checkExactSync analysis entry?).isEmpty = true ↔
      ExactSyncOk analysis entry? := by
  unfold NoComments.RatchetCore.checkExactSync ExactSyncOk
  dsimp only [Id.run, pure, bind, Id.instMonad]
  cases entry? with
  | none =>
    dsimp only
    rw [ite_eq_true_elim]
    cases hbad : (!analysis.comments.isEmpty || (analysis.lines != 0))
    · simp only [Array.isEmpty_empty, true_iff]
      rw [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hbad
      exact hbad
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hc, hl⟩
        rw [hc, hl] at hbad
        cases hbad
  | some entry =>
    dsimp only
    repeat rw [ite_eq_true_elim]
    cases h1 : (entry.comments != analysis.comments.size) <;>
      cases h2 : (entry.lines != analysis.lines) <;>
      cases h3 : ((NoComments.Core.missingFrom analysis.fingerprints entry.fingerprints).isEmpty &&
        (NoComments.Core.missingFrom entry.fingerprints analysis.fingerprints).isEmpty) <;>
      dsimp only
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨_, _, hms⟩
        have hb := (NoComments.Core.missingFrom_both_isEmpty_iff
          analysis.fingerprints entry.fingerprints).mpr hms
        rw [hb] at h3
        cases h3
    · simp only [Array.isEmpty_empty, true_iff]
      rw [bne_eq_false_iff_eq] at h1 h2
      rw [NoComments.Core.missingFrom_both_isEmpty_iff] at h3
      exact ⟨h1, h2, h3⟩
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨_, hl, _⟩
        rw [hl, bne_self_eq_false] at h2
        cases h2
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨_, hl, _⟩
        rw [hl, bne_self_eq_false] at h2
        cases h2
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hc, _, _⟩
        rw [hc, bne_self_eq_false] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hc, _, _⟩
        rw [hc, bne_self_eq_false] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hc, _, _⟩
        rw [hc, bne_self_eq_false] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hc, _, _⟩
        rw [hc, bne_self_eq_false] at h1
        cases h1

theorem checkExactSync_meets :
    checkExactSyncRecord.Meets NoComments.RatchetCore.checkExactSync := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact checkExactSync_iff
  exact nomatch hp

theorem checkExactSync_refines :
    Refines checkExactSyncRecord (fun f => f) (· = NoComments.RatchetCore.checkExactSync) :=
  fun _ hf _ => hf ▸ checkExactSync_meets.2

theorem checkExactSync_fulfilled :
    checkExactSyncRecord.Fulfilled NoComments.RatchetCore.checkExactSync :=
  fulfils checkExactSync_refines rfl

theorem checkMonotonicFile_iff (file : String) (liveFps : NoComments.Core.SortedFingerprints)
    (liveComments liveLines : Nat) (baseEntry? : Option NoComments.RatchetCore.RatchetEntry) :
    (NoComments.RatchetCore.checkMonotonicFile file liveFps liveComments liveLines
      baseEntry?).isEmpty = true ↔
      MonotonicOk liveFps liveLines baseEntry? := by
  unfold NoComments.RatchetCore.checkMonotonicFile MonotonicOk
  dsimp only [Id.run, pure, bind, Id.instMonad]
  cases baseEntry? with
  | none =>
    dsimp only
    rw [ite_eq_true_elim]
    cases h1 : (NoComments.Core.missingFrom liveFps NoComments.Core.SortedFingerprints.empty).isEmpty <;>
      dsimp only <;>
      by_cases h2 : liveLines > 0 <;>
      simp only [h2, ↓reduceIte]
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hcnt, _⟩
        have hem : (NoComments.Core.missingFrom liveFps
            NoComments.Core.SortedFingerprints.empty).isEmpty = true := by
          rw [NoComments.Core.missingFrom_isEmpty_iff]
          intro a
          simpa [NoComments.Core.SortedFingerprints.empty] using hcnt a
        rw [hem] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hcnt, _⟩
        have hem : (NoComments.Core.missingFrom liveFps
            NoComments.Core.SortedFingerprints.empty).isEmpty = true := by
          rw [NoComments.Core.missingFrom_isEmpty_iff]
          intro a
          simpa [NoComments.Core.SortedFingerprints.empty] using hcnt a
        rw [hem] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨_, hle⟩
        omega
    · simp only [Array.isEmpty_empty, true_iff]
      rw [NoComments.Core.missingFrom_isEmpty_iff] at h1
      exact ⟨fun a => by simpa [NoComments.Core.SortedFingerprints.empty] using h1 a,
        Nat.le_of_not_lt h2⟩
  | some e =>
    dsimp only
    rw [ite_eq_true_elim]
    cases h1 : (NoComments.Core.missingFrom liveFps e.fingerprints).isEmpty <;>
      dsimp only <;>
      by_cases h2 : liveLines > e.lines <;>
      simp only [h2, ↓reduceIte]
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hcnt, _⟩
        have hem : (NoComments.Core.missingFrom liveFps e.fingerprints).isEmpty = true :=
          (NoComments.Core.missingFrom_isEmpty_iff liveFps e.fingerprints).mpr hcnt
        rw [hem] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨hcnt, _⟩
        have hem : (NoComments.Core.missingFrom liveFps e.fingerprints).isEmpty = true :=
          (NoComments.Core.missingFrom_isEmpty_iff liveFps e.fingerprints).mpr hcnt
        rw [hem] at h1
        cases h1
    · rw [array_push_isEmpty_false]
      constructor
      · intro h; cases h
      · intro ⟨_, hle⟩
        omega
    · simp only [Array.isEmpty_empty, true_iff]
      rw [NoComments.Core.missingFrom_isEmpty_iff] at h1
      exact ⟨h1, Nat.le_of_not_lt h2⟩

theorem checkMonotonicFile_meets :
    checkMonotonicFileRecord.Meets NoComments.RatchetCore.checkMonotonicFile := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact checkMonotonicFile_iff
  exact nomatch hp

theorem checkMonotonicFile_refines :
    Refines checkMonotonicFileRecord (fun f => f) (· = NoComments.RatchetCore.checkMonotonicFile) :=
  fun _ hf _ => hf ▸ checkMonotonicFile_meets.2

theorem checkMonotonicFile_fulfilled :
    checkMonotonicFileRecord.Fulfilled NoComments.RatchetCore.checkMonotonicFile :=
  fulfils checkMonotonicFile_refines rfl

private theorem checkMonotonicFile_empty (f : String)
    (baseEntry? : Option NoComments.RatchetCore.RatchetEntry) :
    NoComments.RatchetCore.checkMonotonicFile f NoComments.Core.SortedFingerprints.empty 0 0
      baseEntry? = #[] := by
  have hmono : MonotonicOk NoComments.Core.SortedFingerprints.empty 0 baseEntry? := by
    refine ⟨fun a => ?_, by cases baseEntry? <;> simp⟩
    cases baseEntry? with
    | none => simp [NoComments.Core.SortedFingerprints.empty]
    | some e => simp [NoComments.Core.SortedFingerprints.empty]
  have hempty : (NoComments.RatchetCore.checkMonotonicFile f
      NoComments.Core.SortedFingerprints.empty 0 0 baseEntry?).isEmpty = true :=
    (checkMonotonicFile_iff f NoComments.Core.SortedFingerprints.empty 0 0 baseEntry?).mpr hmono
  cases h : NoComments.RatchetCore.checkMonotonicFile f
      NoComments.Core.SortedFingerprints.empty 0 0 baseEntry? with
  | mk l =>
    cases l with
    | nil => rfl
    | cons x xs =>
      rw [h] at hempty
      simp [Array.isEmpty] at hempty

private theorem ratchetCheckAllowedKeys_iff (ctx : String)
    (obj : Std.TreeMap.Raw String Json compare) (allowed : Array String) :
    NoComments.RatchetCore.checkAllowedKeys ctx obj allowed = Except.ok () ↔
      ∀ kv ∈ obj.toList, kv.1 ∈ allowed.toList := by
  unfold NoComments.RatchetCore.checkAllowedKeys
  exact Refinement.Config.checkAllowedKeysLoop_iff ctx allowed obj.toList

private theorem ratchetGetRequiredField_iff (ctx : String)
    (obj : Std.TreeMap.Raw String Json compare) (key : String) (v : Json) :
    NoComments.RatchetCore.getRequiredField ctx obj key = .ok v ↔ obj.get? key = some v := by
  unfold NoComments.RatchetCore.getRequiredField
  cases obj.get? key <;> simp

private theorem mapM_getStr_iff (arr : Array Json) (out : Array String) :
    arr.mapM (fun j : Json => j.getStr?) = .ok out ↔
      arr.toList = out.toList.map Json.str := by
  rw [Refinement.Config.array_mapM_iff]
  constructor
  · rintro ⟨hsz, hidx⟩
    apply List.ext_getElem
    · simp [hsz]
    · intro i h1 h2
      have hi : i < arr.size := by simpa using h1
      rcases hidx i hi with ⟨ho, hstr⟩
      rw [Refinement.Config.getStr_iff] at hstr
      simpa using hstr
  · intro heq
    have hlen : out.size = arr.size := by
      have := congrArg List.length heq
      simp only [Array.length_toList, List.length_map] at this
      omega
    refine ⟨hlen, fun i hi => ?_⟩
    have ho : i < out.size := by omega
    refine ⟨ho, ?_⟩
    rw [Refinement.Config.getStr_iff]
    have hgi := congrArg (fun l : List Json => l[i]?) heq
    have h1 : i < arr.toList.length := by simpa using hi
    have h2 : i < (out.toList.map Json.str).length := by simpa [hlen] using hi
    simp only [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      List.getElem_map, Option.some.injEq] at hgi
    simpa using hgi

private theorem isFingerprint_iff_spec (fp : String) :
    NoComments.Core.isFingerprint fp = true ↔ CoreSpec.IsFingerprint fp := by
  have h1 : NoComments.Core.isFingerprint fp = true ↔
      (fp.length == 16 && fp.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))) = true := by
    rfl
  rw [h1]
  simp only [Bool.and_eq_true, beq_iff_eq, String.all_bool_eq, List.all_eq_true,
    CoreSpec.IsFingerprint, Refinement.Core.isHexLowerChar_eq_isDigit]

private theorem checkFingerprintsLoop_iff (ctx file : String) (l : List String) :
    (forIn (m := Except String) l () fun fp _ =>
      if NoComments.Core.isFingerprint fp = true then
        Except.ok (ForInStep.yield ())
      else
        Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'") = Except.ok () ↔
      ∀ fp ∈ l, CoreSpec.IsFingerprint fp := by
  induction l with
  | nil =>
    rw [List.forIn_nil]
    constructor
    · intro _ _ h; cases h
    · intro _; rfl
  | cons fp rest ih =>
    rw [List.forIn_cons]
    cases hc : NoComments.Core.isFingerprint fp with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [bind, Except.bind]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h; cases h
      · rintro ⟨hbad, _⟩
        rw [← isFingerprint_iff_spec] at hbad
        rw [hc] at hbad
        cases hbad
    | true =>
      simp only [↓reduceIte]
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [ih]
      exact ⟨fun h x hx => by
        rcases List.mem_cons.mp hx with hxeq | hx
        · subst hxeq
          exact (isFingerprint_iff_spec x).mp hc
        · exact h x hx,
        fun h x hx => h x (List.mem_cons_of_mem fp hx)⟩

private theorem checkFingerprintsLoop_eval (ctx file : String) (l : List String) :
    (∃ err, (forIn (m := Except String) l () fun fp _ =>
      if NoComments.Core.isFingerprint fp = true then
        Except.ok (ForInStep.yield ())
      else
        Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'") = Except.error err ∧
        ¬ (∀ fp ∈ l, CoreSpec.IsFingerprint fp)) ∨
      ((forIn (m := Except String) l () fun fp _ =>
        if NoComments.Core.isFingerprint fp = true then
          Except.ok (ForInStep.yield ())
        else
          Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'") = Except.ok () ∧
        ∀ fp ∈ l, CoreSpec.IsFingerprint fp) := by
  cases h : forIn (m := Except String) l () fun fp _ =>
      if NoComments.Core.isFingerprint fp = true then
        Except.ok (ForInStep.yield ())
      else
        Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'" with
  | error err =>
    left
    refine ⟨err, rfl, fun hall => ?_⟩
    have hok := (checkFingerprintsLoop_iff ctx file l).mpr hall
    rw [h] at hok
    cases hok
  | ok u =>
    right
    have heq : (forIn (m := Except String) l () fun fp _ =>
        if NoComments.Core.isFingerprint fp = true then
          Except.ok (ForInStep.yield ())
        else
          Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'") = Except.ok () :=
      h.trans (congrArg Except.ok rfl)
    exact ⟨congrArg Except.ok rfl, (checkFingerprintsLoop_iff ctx file l).mp heq⟩

private theorem parseRatchetEntry_iff (idx : Nat) (j : Json)
    (e : NoComments.RatchetCore.RatchetEntry) :
    NoComments.RatchetCore.parseRatchetEntry idx j = .ok e ↔
      ValidRatchetEntryJson j e := by
  unfold NoComments.RatchetCore.parseRatchetEntry ValidRatchetEntryJson
  generalize s!"ratchet[{idx}]" = ctx
  dsimp only
  cases j with
  | obj obj =>
    rw [show (Json.obj obj).getObj? = .ok obj from rfl, except_bind_ok]
    cases hkeys : NoComments.RatchetCore.checkAllowedKeys ctx obj
        #["file", "comments", "lines", "fingerprints"] with
    | error err =>
      rw [except_bind_err]
      constructor
      · intro h; cases h
      · rintro ⟨obj', _, _, heq, hall, _⟩
        injection heq with hobj
        subst hobj
        have hok := (ratchetCheckAllowedKeys_iff ctx obj
          #["file", "comments", "lines", "fingerprints"]).mpr hall
        rw [hkeys] at hok
        cases hok
    | ok _ =>
      rw [except_bind_ok]
      rw [ratchetCheckAllowedKeys_iff] at hkeys
      cases hfReq : NoComments.RatchetCore.getRequiredField ctx obj "file" with
      | error err =>
        rw [except_bind_err]
        constructor
        · intro h; cases h
        · rintro ⟨obj', fileRaw', _, heq, _, hreq', _⟩
          injection heq with hobj
          subst hobj
          have hok := (ratchetGetRequiredField_iff ctx obj "file" (.str fileRaw')).mpr hreq'
          rw [hfReq] at hok
          cases hok
      | ok fileJson =>
        rw [except_bind_ok]
        rw [ratchetGetRequiredField_iff] at hfReq
        cases fileJson with
        | str fileRaw =>
          rw [show (Json.str fileRaw).getStr? = .ok fileRaw from rfl, except_bind_ok]
          cases hfNorm : NoComments.Config.normalizeRelFile s!"{ctx}.file" fileRaw with
          | error err =>
            rw [except_bind_err]
            constructor
            · intro h; cases h
            · rintro ⟨obj', fileRaw', _, heq, _, hreq', hnorm', _⟩
              injection heq with hobj
              subst hobj
              rw [hfReq] at hreq'
              injection hreq' with hj
              injection hj with hr
              subst hr
              have hok := (Refinement.Config.normalizeRelFile_iff s!"{ctx}.file" fileRaw
                e.file).mpr hnorm'
              rw [hfNorm] at hok
              cases hok
          | ok file =>
            rw [except_bind_ok]
            rw [Refinement.Config.normalizeRelFile_iff] at hfNorm
            cases hcReq : NoComments.RatchetCore.getRequiredField ctx obj "comments" with
            | error err =>
              rw [except_bind_err]
              constructor
              · intro h; cases h
              · rintro ⟨obj', _, _, heq, _, _, _, hcreq, _⟩
                injection heq with hobj
                subst hobj
                have hok := (ratchetGetRequiredField_iff ctx obj "comments"
                  (.num ⟨↑e.comments, 0⟩)).mpr hcreq
                rw [hcReq] at hok
                cases hok
            | ok commentsJson =>
              rw [except_bind_ok]
              rw [ratchetGetRequiredField_iff] at hcReq
              cases hcNat : commentsJson.getNat? with
              | error err =>
                rw [except_bind_err]
                constructor
                · intro h; cases h
                · rintro ⟨obj', _, _, heq, _, _, _, hcreq, _⟩
                  injection heq with hobj
                  subst hobj
                  rw [hcReq] at hcreq
                  injection hcreq with hj
                  subst hj
                  have hok := (Refinement.Config.getNat_iff (.num ⟨↑e.comments, 0⟩) e.comments).mpr rfl
                  rw [hcNat] at hok
                  cases hok
              | ok comments =>
                rw [except_bind_ok]
                rw [Refinement.Config.getNat_iff] at hcNat
                cases hlReq : NoComments.RatchetCore.getRequiredField ctx obj "lines" with
                | error err =>
                  rw [except_bind_err]
                  constructor
                  · intro h; cases h
                  · rintro ⟨obj', _, _, heq, _, _, _, _, _, hlreq, _⟩
                    injection heq with hobj
                    subst hobj
                    have hok := (ratchetGetRequiredField_iff ctx obj "lines"
                      (.num ⟨↑e.lines, 0⟩)).mpr hlreq
                    rw [hlReq] at hok
                    cases hok
                | ok linesJson =>
                  rw [except_bind_ok]
                  rw [ratchetGetRequiredField_iff] at hlReq
                  cases hlNat : linesJson.getNat? with
                  | error err =>
                    rw [except_bind_err]
                    constructor
                    · intro h; cases h
                    · rintro ⟨obj', _, _, heq, _, _, _, _, _, hlreq, _⟩
                      injection heq with hobj
                      subst hobj
                      rw [hlReq] at hlreq
                      injection hlreq with hj
                      subst hj
                      have hok := (Refinement.Config.getNat_iff (.num ⟨↑e.lines, 0⟩) e.lines).mpr rfl
                      rw [hlNat] at hok
                      cases hok
                  | ok lines =>
                    rw [except_bind_ok]
                    rw [Refinement.Config.getNat_iff] at hlNat
                    cases hfpsReq : NoComments.RatchetCore.getRequiredField ctx obj "fingerprints" with
                    | error err =>
                      rw [except_bind_err]
                      constructor
                      · intro h; cases h
                      · rintro ⟨obj', _, fpsJson', heq, _, _, _, _, _, _, _, hfpsreq', _⟩
                        injection heq with hobj
                        subst hobj
                        have hok := (ratchetGetRequiredField_iff ctx obj "fingerprints"
                          (.arr fpsJson')).mpr hfpsreq'
                        rw [hfpsReq] at hok
                        cases hok
                    | ok fpsVal =>
                      rw [except_bind_ok]
                      rw [ratchetGetRequiredField_iff] at hfpsReq
                      cases hfpsArr : fpsVal.getArr? with
                      | error err =>
                        rw [except_bind_err]
                        constructor
                        · intro h; cases h
                        · rintro ⟨obj', _, fpsJson', heq, _, _, _, _, _, _, _, hfpsreq', _⟩
                          injection heq with hobj
                          subst hobj
                          rw [hfpsReq] at hfpsreq'
                          injection hfpsreq' with hj
                          subst hj
                          have hok := (Refinement.Config.getArr_iff (.arr fpsJson') fpsJson').mpr rfl
                          rw [hfpsArr] at hok
                          cases hok
                      | ok fpsJson =>
                        rw [except_bind_ok]
                        rw [Refinement.Config.getArr_iff] at hfpsArr
                        cases hfpsMap : fpsJson.mapM (fun item : Json => item.getStr?) with
                        | error err =>
                          rw [except_bind_err]
                          constructor
                          · intro h; cases h
                          · rintro ⟨obj', _, fpsJson', heq, _, _, _, _, _, _, _, hfpsreq', hlist', _⟩
                            injection heq with hobj
                            subst hobj
                            rw [hfpsReq] at hfpsreq'
                            injection hfpsreq' with hj
                            rw [hfpsArr] at hj
                            injection hj with hfa
                            subst hfa
                            have hok := (mapM_getStr_iff fpsJson e.fingerprints.values).mpr hlist'
                            rw [hfpsMap] at hok
                            cases hok
                        | ok fpsRaw =>
                          rw [except_bind_ok]
                          rw [mapM_getStr_iff] at hfpsMap
                          by_cases hc0 : comments = 0
                          · simp only [hc0, beq_self_eq_true, ↓reduceIte, throw, throwThe,
                              MonadExceptOf.throw, except_bind_err]
                            constructor
                            · intro h; cases h
                            · rintro ⟨obj', _, _, heq, _, _, _, hcreq, hcgt, _⟩
                              injection heq with hobj
                              subst hobj
                              rw [hcReq] at hcreq
                              injection hcreq with hj
                              rw [hcNat] at hj
                              injection hj with hnum
                              injection hnum with hm
                              rw [Int.ofNat_eq_natCast, Int.natCast_inj] at hm
                              omega
                          · have hc0b : (comments == 0) = false := beq_false_of_ne hc0
                            simp only [hc0b, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
                            by_cases hl0 : lines = 0
                            · simp only [hl0, beq_self_eq_true, ↓reduceIte, throw, throwThe,
                                MonadExceptOf.throw, except_bind_err]
                              constructor
                              · intro h; cases h
                              · rintro ⟨obj', _, _, heq, _, _, _, _, _, hlreq, hlgt, _⟩
                                injection heq with hobj
                                subst hobj
                                rw [hlReq] at hlreq
                                injection hlreq with hj
                                rw [hlNat] at hj
                                injection hj with hnum
                                injection hnum with hm
                                rw [Int.ofNat_eq_natCast, Int.natCast_inj] at hm
                                omega
                            · have hl0b : (lines == 0) = false := beq_false_of_ne hl0
                              simp only [hl0b, Bool.false_eq_true, ↓reduceIte]
                              by_cases hsz : fpsRaw.size = comments
                              · have hszb : (fpsRaw.size != comments) = false := by
                                  simp [hsz]
                                simp only [hszb, Bool.false_eq_true, ↓reduceIte]
                                rw [← Array.forIn_toList]
                                rw [forIn_congr_body fpsRaw.toList () _
                                  (fun fp _ =>
                                    if NoComments.Core.isFingerprint fp = true then
                                      Except.ok (ForInStep.yield ())
                                    else
                                      Except.error s!"{ctx} ({file}) contains invalid fingerprint '{fp}'")
                                  fun fp _ => by
                                    cases NoComments.Core.isFingerprint fp <;> rfl]
                                rcases checkFingerprintsLoop_eval ctx file fpsRaw.toList with
                                  ⟨err, hloop_err, hnot_fps⟩ | ⟨hloop_ok, hloop⟩
                                · rw [hloop_err, except_bind_err]
                                  constructor
                                  · intro h; cases h
                                  · rintro ⟨obj', _, fpsJson', heq, _, _, _, _, _, _, _, hfpsreq',
                                      hlist', _, hvalidFps⟩
                                    injection heq with hobj
                                    subst hobj
                                    rw [hfpsReq] at hfpsreq'
                                    injection hfpsreq' with hj
                                    rw [hfpsArr] at hj
                                    injection hj with hfa
                                    subst hfa
                                    have hlen_list : fpsRaw.toList.length =
                                        e.fingerprints.values.toList.length := by
                                      have h1 := congrArg List.length hfpsMap
                                      have h2 := congrArg List.length hlist'
                                      simp only [List.length_map] at h1 h2
                                      omega
                                    have hvaleq : fpsRaw = e.fingerprints.values := by
                                      apply Array.ext'
                                      apply List.ext_getElem hlen_list
                                      intro i h1 h2
                                      have hm := congrArg (fun l : List Json => l[i]?) hfpsMap
                                      have hm2 := congrArg (fun l : List Json => l[i]?) hlist'
                                      rw [hm] at hm2
                                      rw [List.getElem?_eq_getElem (by rw [List.length_map]; exact h1),
                                        List.getElem?_eq_getElem (by rw [List.length_map]; exact h2)] at hm2
                                      simp only [List.getElem_map, Option.some.injEq, Json.str.injEq] at hm2
                                      exact hm2
                                    rw [← hvaleq] at hvalidFps
                                    exact False.elim (hnot_fps hvalidFps)
                                · rw [hloop_ok, except_bind_ok]
                                  split
                                  · rename_i bad hord
                                    constructor
                                    · intro h; cases h
                                    · rintro ⟨obj', _, fpsJson', heq, _, _, _, _, _, _, _, hfpsreq',
                                        hlist', _, _⟩
                                      injection heq with hobj
                                      subst hobj
                                      rw [hfpsReq] at hfpsreq'
                                      injection hfpsreq' with hj
                                      rw [hfpsArr] at hj
                                      injection hj with hfa
                                      subst hfa
                                      have hlen_list : fpsRaw.toList.length =
                                          e.fingerprints.values.toList.length := by
                                        have h1 := congrArg List.length hfpsMap
                                        have h2 := congrArg List.length hlist'
                                        simp only [List.length_map] at h1 h2
                                        omega
                                      have hvaleq : fpsRaw = e.fingerprints.values := by
                                        apply Array.ext'
                                        apply List.ext_getElem hlen_list
                                        intro i h1 h2
                                        have hm := congrArg (fun l : List Json => l[i]?) hfpsMap
                                        have hm2 := congrArg (fun l : List Json => l[i]?) hlist'
                                        rw [hm] at hm2
                                        rw [List.getElem?_eq_getElem (by rw [List.length_map]; exact h1),
                                          List.getElem?_eq_getElem (by rw [List.length_map]; exact h2)] at hm2
                                        simp only [List.getElem_map, Option.some.injEq, Json.str.injEq] at hm2
                                        exact hm2
                                      have hpw : fpsRaw.toList.Pairwise (· ≤ ·) := by
                                        rw [hvaleq]
                                        exact e.fingerprints.sorted
                                      have hnone :=
                                        (NoComments.Core.firstOutOfOrder_eq_none_iff fpsRaw.toList).mpr hpw
                                      rw [hord] at hnone
                                      cases hnone
                                  · simp only [Except.ok.injEq]
                                    cases e with
                                    | mk ef ec el efps =>
                                      cases efps with
                                      | mk efpVals efpSorted =>
                                        constructor
                                        · intro heq
                                          injection heq with hf_eq hc_eq hl_eq hfps_eq
                                          subst hf_eq hc_eq hl_eq
                                          have hvals : efpVals = fpsRaw := by
                                            simpa using congrArg
                                              NoComments.Core.SortedFingerprints.values hfps_eq.symm
                                          subst hvals
                                          refine ⟨obj, fileRaw, fpsJson, rfl, hkeys, hfReq, hfNorm,
                                            by dsimp only; rw [hcReq, hcNat, Int.ofNat_eq_natCast],
                                            by dsimp only; omega,
                                            by dsimp only; rw [hlReq, hlNat, Int.ofNat_eq_natCast],
                                            by dsimp only; omega,
                                            by rw [hfpsReq, hfpsArr], hfpsMap, hsz, hloop⟩
                                        · rintro ⟨obj', fileRaw', fpsJson', heq, _, hfreq', hfnorm',
                                            hcreq', _, hlreq', _, hfpsreq', hlist', _, _⟩
                                          injection heq with hobj
                                          subst hobj
                                          rw [hfReq] at hfreq'
                                          injection hfreq' with hjf
                                          injection hjf with hfr
                                          subst hfr
                                          have hf_eq : file = ef := by
                                            have h1 := (Refinement.Config.normalizeRelFile_iff
                                              s!"{ctx}.file" fileRaw file).mpr hfNorm
                                            have h2 := (Refinement.Config.normalizeRelFile_iff
                                              s!"{ctx}.file" fileRaw ef).mpr hfnorm'
                                            rw [h1] at h2
                                            exact Except.ok.inj h2
                                          rw [hcReq] at hcreq'
                                          injection hcreq' with hjc
                                          rw [hcNat] at hjc
                                          injection hjc with hnc
                                          injection hnc with hmc
                                          rw [Int.ofNat_eq_natCast, Int.natCast_inj] at hmc
                                          have hc_eq : comments = ec := hmc
                                          rw [hlReq] at hlreq'
                                          injection hlreq' with hjl
                                          rw [hlNat] at hjl
                                          injection hjl with hnl
                                          injection hnl with hml
                                          rw [Int.ofNat_eq_natCast, Int.natCast_inj] at hml
                                          have hl_eq : lines = el := hml
                                          rw [hfpsReq] at hfpsreq'
                                          injection hfpsreq' with hjfps
                                          rw [hfpsArr] at hjfps
                                          injection hjfps with hfa
                                          subst hfa
                                          have hlen_list : fpsRaw.toList.length = efpVals.toList.length := by
                                            have h1 := congrArg List.length hfpsMap
                                            have h2 := congrArg List.length hlist'
                                            simp only [List.length_map] at h1 h2
                                            omega
                                          have hvals : fpsRaw = efpVals := by
                                            apply Array.ext'
                                            apply List.ext_getElem hlen_list
                                            intro i h1 h2
                                            have hm := congrArg (fun l : List Json => l[i]?) hfpsMap
                                            have hm2 := congrArg (fun l : List Json => l[i]?) hlist'
                                            rw [hm] at hm2
                                            rw [List.getElem?_eq_getElem (by rw [List.length_map]; exact h1),
                                              List.getElem?_eq_getElem (by rw [List.length_map]; exact h2)] at hm2
                                            simp only [List.getElem_map, Option.some.injEq, Json.str.injEq] at hm2
                                            exact hm2
                                          subst hf_eq hc_eq hl_eq hvals
                                          rfl
                              · have hszb : (fpsRaw.size != comments) = true := by
                                  simp [hsz]
                                simp only [hszb, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
                                  except_bind_err]
                                constructor
                                · intro h; cases h
                                · rintro ⟨obj', _, fpsJson', heq, _, _, _, hcreq, _, _, _,
                                    hfpsreq', hlist', hsz', _⟩
                                  injection heq with hobj
                                  subst hobj
                                  rw [hcReq] at hcreq
                                  injection hcreq with hjc
                                  rw [hcNat] at hjc
                                  injection hjc with hnc
                                  injection hnc with hmc
                                  rw [Int.ofNat_eq_natCast, Int.natCast_inj] at hmc
                                  have hc_eq : comments = e.comments := by omega
                                  rw [hfpsReq] at hfpsreq'
                                  injection hfpsreq' with hjfps
                                  rw [hfpsArr] at hjfps
                                  injection hjfps with hfa
                                  subst hfa
                                  have hlen_list : fpsRaw.toList.length =
                                      e.fingerprints.values.toList.length := by
                                    have h1 := congrArg List.length hfpsMap
                                    have h2 := congrArg List.length hlist'
                                    simp only [List.length_map] at h1 h2
                                    omega
                                  have : fpsRaw.size = e.fingerprints.values.size := by
                                    simpa using hlen_list
                                  omega
        | _ =>
          simp only [Lean.Json.getStr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          constructor
          · intro h; cases h
          · rintro ⟨obj', fileRaw', _, heq, _, hreq', _⟩
            injection heq with hobj
            subst hobj
            rw [hfReq] at hreq'
            cases hreq'
  | _ =>
    simp only [Lean.Json.getObj?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    constructor
    · intro h; cases h
    · rintro ⟨_, _, _, h, _⟩; cases h

private theorem parseRatchetLoop_ok_or_err (arr : Array Json)
    (xs : List Nat) (hxs_nd : xs.Nodup) (hx : ∀ idx ∈ xs, idx < arr.size)
    (initEntries : List NoComments.RatchetCore.RatchetEntry)
    (initIdxs : List Nat)
    (hdisj : ∀ a ∈ initIdxs, a ∉ xs)
    (hbi : ∀ a ∈ initIdxs, a < arr.size)
    (hlen : initEntries.length = initIdxs.length)
    (hvalid : ∀ (k : Nat) (hk : k < initEntries.length) (hk2 : k < initIdxs.length),
      ∃ hidx : initIdxs[k] < arr.size,
        ValidRatchetEntryJson arr[initIdxs[k]] initEntries[k])
    (hnodup : (initEntries.map (·.file)).Nodup)
    (map : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (hmap : ∀ k, map[k]? = initEntries.find? (·.file == k)) :
    match
      (forIn' xs map fun idx h m => do
        let entry ← NoComments.RatchetCore.parseRatchetEntry idx (arr[idx]'(hx idx h))
        if m.contains entry.file then
          throw s!"duplicate ratchet entry for '{entry.file}'"
        let m := m.insert entry.file entry
        return ForInStep.yield m)
    with
    | .ok outMap =>
      ∃ fullEntries : List NoComments.RatchetCore.RatchetEntry,
        fullEntries.length = initEntries.length + xs.length ∧
        (∀ (k : Nat) (hk : k < fullEntries.length) (hk2 : k < (initIdxs ++ xs).length),
          ∃ hidx : (initIdxs ++ xs)[k] < arr.size,
            ValidRatchetEntryJson arr[(initIdxs ++ xs)[k]] fullEntries[k]) ∧
        (fullEntries.map (·.file)).Nodup ∧
        (∀ k, outMap[k]? = fullEntries.find? (·.file == k))
    | .error _ =>
      (∃ idx, ∃ (_h : idx < arr.size), ∀ e, ¬ ValidRatchetEntryJson arr[idx] e) ∨
      (∃ i j e1 e2, ∃ (_hi : i < arr.size) (_hj : j < arr.size), i ≠ j ∧
        ValidRatchetEntryJson arr[i] e1 ∧ ValidRatchetEntryJson arr[j] e2 ∧ e1.file = e2.file) := by
  induction xs generalizing initEntries initIdxs map with
  | nil =>
    simp only [List.forIn'_nil, pure, Except.pure, List.length_nil, Nat.add_zero, List.append_nil]
    exact ⟨initEntries, rfl, hvalid, hnodup, hmap⟩
  | cons idx rest ih =>
    simp only [List.forIn'_cons]
    have hidx_lt : idx < arr.size := hx idx List.mem_cons_self
    have hnd_pair := List.nodup_cons.mp hxs_nd
    have hidx_not_rest : idx ∉ rest := hnd_pair.1
    have hrest_nd : rest.Nodup := hnd_pair.2
    have hrest_lt : ∀ j ∈ rest, j < arr.size := fun j hj => hx j (List.mem_cons_of_mem idx hj)
    cases hstep : NoComments.RatchetCore.parseRatchetEntry idx arr[idx] with
    | error e =>
      rw [except_bind_err]
      left
      refine ⟨idx, hidx_lt, fun ent hent => ?_⟩
      have hok := (parseRatchetEntry_iff idx arr[idx] ent).mpr hent
      rw [hstep] at hok
      cases hok
    | ok entry =>
      rw [except_bind_ok]
      have hentry_valid : ValidRatchetEntryJson arr[idx] entry :=
        (parseRatchetEntry_iff idx arr[idx] entry).mp hstep
      by_cases hdup : map.contains entry.file = true
      · simp only [hdup, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, except_bind_err]
        right
        have hsome : map[entry.file]?.isSome = true := by
          rw [← Std.HashMap.contains_eq_isSome_getElem?]
          exact hdup
        cases hm_eq : map[entry.file]? with
        | none =>
          rw [hm_eq] at hsome
          cases hsome
        | some prev =>
          have hfind : initEntries.find? (·.file == entry.file) = some prev := by
            rw [← hmap entry.file]
            exact hm_eq
          have hprev_mem : prev ∈ initEntries := List.mem_of_find?_eq_some hfind
          have hprev_eq_pred : (prev.file == entry.file) = true :=
            List.find?_some (p := fun x : NoComments.RatchetCore.RatchetEntry => x.file == entry.file) hfind
          have hfile_eq : prev.file = entry.file := beq_iff_eq.mp hprev_eq_pred
          rcases List.mem_iff_getElem.mp hprev_mem with ⟨k, hk, hget⟩
          rcases hvalid k hk (by omega) with ⟨hj_lt, hvalid_prev⟩
          rw [hget] at hvalid_prev
          have hj_in_init : initIdxs[k] ∈ initIdxs := List.getElem_mem (by omega)
          have hne : initIdxs[k] ≠ idx := fun heq => by
            rw [heq] at hj_in_init
            exact hdisj idx hj_in_init List.mem_cons_self
          exact ⟨initIdxs[k], idx, prev, entry, hj_lt, hidx_lt, hne,
            hvalid_prev, hentry_valid, hfile_eq⟩
      · have hdupf : map.contains entry.file = false := Bool.eq_false_iff.mpr hdup
        have hhead :
            (if map.contains entry.file = true then do
                throw s!"duplicate ratchet entry for '{entry.file}'"
                pure (ForInStep.yield (map.insert entry.file entry))
              else
                pure (ForInStep.yield (map.insert entry.file entry)) :
              Except String (ForInStep (Std.HashMap String NoComments.RatchetCore.RatchetEntry))) =
              Except.ok (ForInStep.yield (map.insert entry.file entry)) := by
          simp [hdupf]
          rfl
        rw [hhead, except_bind_ok]
        have hm_none : map[entry.file]? = none := by
          have := Std.HashMap.contains_eq_isSome_getElem? (m := map) (a := entry.file)
          rw [hdupf] at this
          cases hmc : map[entry.file]? with
          | none => rfl
          | some _ => rw [hmc] at this; cases this
        have hfind_none : initEntries.find? (·.file == entry.file) = none := by
          rw [← hmap entry.file]
          exact hm_none
        have hnot_mem_file : entry.file ∉ initEntries.map (·.file) := by
          intro hmem
          rcases List.mem_map.mp hmem with ⟨x, hxmem, hxf⟩
          have hfalse := (List.find?_eq_none.mp hfind_none) x hxmem
          simp [hxf] at hfalse
        have hdisj' : ∀ a ∈ initIdxs ++ [idx], a ∉ rest := by
          intro a ha hmem
          rcases List.mem_append.mp ha with ha1 | ha2
          · exact hdisj a ha1 (List.mem_cons_of_mem idx hmem)
          · simp only [List.mem_singleton] at ha2
            subst ha2
            exact hidx_not_rest hmem
        have hbi' : ∀ a ∈ initIdxs ++ [idx], a < arr.size := by
          intro a ha
          rcases List.mem_append.mp ha with ha1 | ha2
          · exact hbi a ha1
          · simp only [List.mem_singleton] at ha2
            subst ha2
            exact hidx_lt
        have hlen' : (initEntries ++ [entry]).length = (initIdxs ++ [idx]).length := by
          simp [hlen]
        have hvalid' : ∀ (k : Nat) (hk : k < (initEntries ++ [entry]).length)
            (hk2 : k < (initIdxs ++ [idx]).length),
            ∃ hidx : (initIdxs ++ [idx])[k] < arr.size,
              ValidRatchetEntryJson arr[(initIdxs ++ [idx])[k]] (initEntries ++ [entry])[k] := by
          intro k hk hk2
          simp only [List.length_append, List.length_singleton] at hk hk2
          by_cases hklt : k < initEntries.length
          · rcases hvalid k hklt (by omega) with ⟨h1, h2⟩
            refine ⟨?_, ?_⟩
            · simp only [List.getElem_append_left (by omega : k < initIdxs.length)]
              exact h1
            · simp only [List.getElem_append_left (by omega : k < initIdxs.length),
                List.getElem_append_left hklt]
              exact h2
          · have hkeq : k = initEntries.length := by omega
            subst hkeq
            have hget_idx : (initIdxs ++ [idx])[initEntries.length]'(by
                simp only [List.length_append, List.length_singleton]; omega) = idx := by
              rw [List.getElem_append_right (by omega)]
              simp [hlen]
            have hget_ent : (initEntries ++ [entry])[initEntries.length]'(by
                simp only [List.length_append, List.length_singleton]; omega) = entry := by
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp
            refine ⟨by rw [hget_idx]; exact hidx_lt, ?_⟩
            have heq_arr :
                arr[(initIdxs ++ [idx])[initEntries.length]'(by
                  simp only [List.length_append, List.length_singleton]; omega)] =
                arr[idx] := by
              congr 1
            rw [hget_ent, heq_arr]
            exact hentry_valid
        have hnodup' : ((initEntries ++ [entry]).map (·.file)).Nodup := by
          rw [List.map_append, List.map_singleton, List.nodup_append]
          refine ⟨hnodup, (by simp : ([entry.file]).Nodup), fun a ha b hb heq => ?_⟩
          simp only [List.mem_singleton] at hb
          subst hb
          subst heq
          exact hnot_mem_file ha
        have hmap' : ∀ k, (map.insert entry.file entry)[k]? =
            (initEntries ++ [entry]).find? (·.file == k) := by
          intro k
          rw [Std.HashMap.getElem?_insert, List.find?_append]
          by_cases hkeq : entry.file = k
          · have hkbeq : (entry.file == k) = true := beq_iff_eq.mpr hkeq
            have hfindk : initEntries.find? (·.file == k) = none := by
              rw [← hkeq]
              exact hfind_none
            simp [hkbeq, hfindk]
          · have hkbne : (entry.file == k) = false := beq_false_of_ne hkeq
            simp [hkbne, hmap k]
        have hrec := ih hrest_nd hrest_lt (initEntries ++ [entry]) (initIdxs ++ [idx])
          hdisj' hbi' hlen' hvalid' hnodup' (map.insert entry.file entry) hmap'
        simpa [List.length_append, List.length_singleton, List.append_assoc, Nat.add_assoc,
          Nat.add_comm 1] using hrec

private theorem parseRatchet_extract (arr : Array Json)
    (body : (idx : Nat) → idx ∈ [:arr.size] →
      Std.HashMap String NoComments.RatchetCore.RatchetEntry →
      Except String (ForInStep (Std.HashMap String NoComments.RatchetCore.RatchetEntry)))
    (k : Std.HashMap String NoComments.RatchetCore.RatchetEntry →
      Except String (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (res : Except String (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (heq : (forIn' [:arr.size] ({} : Std.HashMap String NoComments.RatchetCore.RatchetEntry) body >>= k) = res)
    (hbody : ∀ idx h m,
      body idx h m = do
        let entry ← NoComments.RatchetCore.parseRatchetEntry idx arr[idx]
        if m.contains entry.file then
          throw s!"duplicate ratchet entry for '{entry.file}'"
        let m := m.insert entry.file entry
        return ForInStep.yield m) :
    ((forIn' (List.range' 0 arr.size 1) ({} : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
      fun idx h m => do
        let entry ← NoComments.RatchetCore.parseRatchetEntry idx
          (arr[idx]'(Refinement.Config.range'_zero_mem h))
        if m.contains entry.file then
          throw s!"duplicate ratchet entry for '{entry.file}'"
        let m := m.insert entry.file entry
        return ForInStep.yield m) >>= k) = res := by
  rw [← heq]
  congr 1
  have hbase := @Std.Legacy.Range.forIn'_eq_forIn'_range'
  rw [hbase]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  funext idx h m
  exact (hbody idx _ m).symm

theorem parseRatchetJson_ok (text : String)
    (m : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (hok : NoComments.RatchetCore.parseRatchetJson text = .ok m) :
    ValidRatchetJson text m := by
  unfold NoComments.RatchetCore.parseRatchetJson at hok
  dsimp only at hok
  cases hparse : Json.parse text with
  | error e =>
    rw [hparse, except_bind_err] at hok
    cases hok
  | ok j =>
    rw [hparse, except_bind_ok] at hok
    cases j with
    | arr arr =>
      rw [show (Json.arr arr).getArr? = .ok arr from rfl, except_bind_ok] at hok
      have hex := parseRatchet_extract arr _ _ (.ok m) hok (fun _ _ _ => rfl)
      have hspec := parseRatchetLoop_ok_or_err arr (List.range' 0 arr.size 1)
        (List.nodup_range') (fun _ h => Refinement.Config.range'_zero_mem h)
        [] [] (fun _ h => nomatch h) (fun _ h => nomatch h) rfl
        (fun k hk _ => nomatch hk) List.nodup_nil {} (fun k => Std.HashMap.getElem?_empty)
      cases hloop :
          (forIn' (List.range' 0 arr.size 1)
            ({} : Std.HashMap String NoComments.RatchetCore.RatchetEntry) fun idx h m0 => do
            let entry ← NoComments.RatchetCore.parseRatchetEntry idx
              (arr[idx]'(Refinement.Config.range'_zero_mem h))
            if m0.contains entry.file then
              throw s!"duplicate ratchet entry for '{entry.file}'"
            let m0 := m0.insert entry.file entry
            return ForInStep.yield m0) with
      | error e =>
        rw [hloop, except_bind_err] at hex
        cases hex
      | ok outMap =>
        rw [hloop] at hspec
        rcases hspec with ⟨entries, hlen, hvalid, hnodup, hmap⟩
        rw [hloop, except_bind_ok] at hex
        have hout : outMap = m := by
          simpa [pure, Except.pure] using hex
        subst hout
        have hlen' : entries.length = arr.size := by simpa using hlen
        refine ⟨arr, entries, hparse, hlen', fun i hi => ?_, hnodup, hmap⟩
        have hk : i < entries.length := by omega
        rcases hvalid i hk (by simp [hi]) with ⟨_, hv⟩
        have hgi : (List.range' 0 arr.size 1)[i]'(by simp [hi]) = i :=
          Refinement.Config.range'_zero_getElem arr.size i (by simp [hi])
        refine ⟨hk, ?_⟩
        simpa [hgi] using hv
    | _ =>
      simp only [Lean.Json.getArr?, throw, throwThe, MonadExceptOf.throw, except_bind_err] at hok
      cases hok

theorem parseRatchetJson_err (text msg : String)
    (herr : NoComments.RatchetCore.parseRatchetJson text = .error msg) :
    RatchetRefusal text := by
  unfold NoComments.RatchetCore.parseRatchetJson at herr
  dsimp only at herr
  cases hparse : Json.parse text with
  | error e =>
    exact RatchetRefusal.badJson fun j hj => by rw [hparse] at hj; cases hj
  | ok j =>
    rw [hparse, except_bind_ok] at herr
    cases j with
    | arr arr =>
      rw [show (Json.arr arr).getArr? = .ok arr from rfl, except_bind_ok] at herr
      have hex := parseRatchet_extract arr _ _ (.error msg) herr (fun _ _ _ => rfl)
      have hspec := parseRatchetLoop_ok_or_err arr (List.range' 0 arr.size 1)
        (List.nodup_range') (fun _ h => Refinement.Config.range'_zero_mem h)
        [] [] (fun _ h => nomatch h) (fun _ h => nomatch h) rfl
        (fun k hk _ => nomatch hk) List.nodup_nil {} (fun k => Std.HashMap.getElem?_empty)
      cases hloop :
          (forIn' (List.range' 0 arr.size 1)
            ({} : Std.HashMap String NoComments.RatchetCore.RatchetEntry) fun idx h m0 => do
            let entry ← NoComments.RatchetCore.parseRatchetEntry idx
              (arr[idx]'(Refinement.Config.range'_zero_mem h))
            if m0.contains entry.file then
              throw s!"duplicate ratchet entry for '{entry.file}'"
            let m0 := m0.insert entry.file entry
            return ForInStep.yield m0) with
      | ok outMap =>
        rw [hloop, except_bind_ok] at hex
        dsimp only [pure, Except.pure] at hex
        cases hex
      | error e =>
        rw [hloop] at hspec
        rcases hspec with ⟨idx, hi, hbad⟩ | ⟨i, j, e1, e2, hi, hj, hne, hv1, hv2, heq⟩
        · exact RatchetRefusal.invalidEntry hi hparse hbad
        · exact RatchetRefusal.duplicateFile hi hj hparse hne hv1 hv2 heq
    | _ =>
      exact RatchetRefusal.notArray hparse fun arr h => by cases h

theorem parseRatchetJson_meets :
    parseRatchetRecord.Meets NoComments.RatchetCore.parseRatchetJson := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact parseRatchetJson_ok
  rcases List.mem_cons.mp hp with rfl | hp
  · exact parseRatchetJson_err
  exact nomatch hp

theorem parseRatchetJson_refines :
    Refines parseRatchetRecord (fun f => f) (· = NoComments.RatchetCore.parseRatchetJson) :=
  fun _ hf _ => hf ▸ parseRatchetJson_meets.2

theorem parseRatchetJson_fulfilled :
    parseRatchetRecord.Fulfilled NoComments.RatchetCore.parseRatchetJson :=
  fulfils parseRatchetJson_refines rfl

private theorem validateCurLoop_eval (checkedFiles excludedFiles : Array String)
    (l : List (String × NoComments.RatchetCore.RatchetEntry)) (errs0 : Array String) :
    ∃ errs1 : Array String,
      (forIn (m := Except String) l errs0 fun x errs =>
        if excludedFiles.contains x.1 = true then
          Except.ok (ForInStep.yield (errs.push s!"checked-in ratchet contains excluded file '{x.1}'"))
        else if checkedFiles.contains x.1 = true then
          Except.ok (ForInStep.yield errs)
        else
          Except.ok (ForInStep.yield (errs.push s!"checked-in ratchet contains unknown or untracked file '{x.1}'"))) =
        Except.ok errs1 ∧
      (errs1.isEmpty = true ↔
        errs0.isEmpty = true ∧ ∀ kv ∈ l, kv.1 ∉ excludedFiles.toList ∧ kv.1 ∈ checkedFiles.toList) := by
  induction l generalizing errs0 with
  | nil =>
    refine ⟨errs0, rfl, ?_⟩
    simp
  | cons kv rest ih =>
    rcases kv with ⟨f, e⟩
    by_cases hexcl : f ∈ excludedFiles.toList
    · have hexclB : excludedFiles.contains f = true := by
        simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hexcl
      rcases ih (errs0.push s!"checked-in ratchet contains excluded file '{f}'") with
        ⟨errs1, heq, hiff⟩
      refine ⟨errs1, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [hexclB, ↓reduceIte]
        dsimp only [bind, Except.bind]
        exact heq
      · rw [hiff]
        constructor
        · intro ⟨hb, _⟩
          rw [array_push_isEmpty_false] at hb
          cases hb
        · intro ⟨_, hall⟩
          exact False.elim ((hall (f, e) List.mem_cons_self).1 hexcl)
    · have hexclB : excludedFiles.contains f = false := by
        cases hc : excludedFiles.contains f with
        | false => rfl
        | true =>
          have hm : f ∈ excludedFiles.toList := by
            simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hc
          exact False.elim (hexcl hm)
      by_cases hchk : f ∈ checkedFiles.toList
      · have hchkB : checkedFiles.contains f = true := by
          simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hchk
        rcases ih errs0 with ⟨errs1, heq, hiff⟩
        refine ⟨errs1, ?_, ?_⟩
        · rw [List.forIn_cons]
          simp only [hexclB, hchkB, Bool.false_eq_true, ↓reduceIte]
          dsimp only [bind, Except.bind]
          exact heq
        · rw [hiff]
          simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨fun ⟨h0, hr⟩ => ⟨h0, ⟨hexcl, hchk⟩, hr⟩, fun ⟨h0, _, hr⟩ => ⟨h0, hr⟩⟩
      · have hchkB : checkedFiles.contains f = false := by
          cases hc : checkedFiles.contains f with
          | false => rfl
          | true =>
            have hm : f ∈ checkedFiles.toList := by
              simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hc
            exact False.elim (hchk hm)
        rcases ih (errs0.push s!"checked-in ratchet contains unknown or untracked file '{f}'") with
          ⟨errs1, heq, hiff⟩
        refine ⟨errs1, ?_, ?_⟩
        · rw [List.forIn_cons]
          simp only [hexclB, hchkB, Bool.false_eq_true, ↓reduceIte]
          dsimp only [bind, Except.bind]
          exact heq
        · rw [hiff]
          constructor
          · intro ⟨hb, _⟩
            rw [array_push_isEmpty_false] at hb
            cases hb
          · intro ⟨_, hall⟩
            exact False.elim (hchk (hall (f, e) List.mem_cons_self).2)

private theorem validateBaseLoop_eval (excludedFiles : Array String)
    (l : List (String × NoComments.RatchetCore.RatchetEntry)) (errs0 : Array String) :
    ∃ errs1 : Array String,
      (forIn (m := Except String) l errs0 fun x errs =>
        if excludedFiles.contains x.1 = true then
          Except.ok (ForInStep.yield (errs.push
            s!"cannot exclude '{x.1}' because merge-base ratchet still tracks comments in it"))
        else
          Except.ok (ForInStep.yield errs)) = Except.ok errs1 ∧
      (errs1.isEmpty = true ↔ errs0.isEmpty = true ∧ ∀ kv ∈ l, kv.1 ∉ excludedFiles.toList) := by
  induction l generalizing errs0 with
  | nil =>
    refine ⟨errs0, rfl, ?_⟩
    simp
  | cons kv rest ih =>
    rcases kv with ⟨f, e⟩
    by_cases hexcl : f ∈ excludedFiles.toList
    · have hexclB : excludedFiles.contains f = true := by
        simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hexcl
      rcases ih (errs0.push
          s!"cannot exclude '{f}' because merge-base ratchet still tracks comments in it") with
        ⟨errs1, heq, hiff⟩
      refine ⟨errs1, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [hexclB, ↓reduceIte]
        dsimp only [bind, Except.bind]
        exact heq
      · rw [hiff]
        constructor
        · intro ⟨hb, _⟩
          rw [array_push_isEmpty_false] at hb
          cases hb
        · intro ⟨_, hall⟩
          exact False.elim (hall (f, e) List.mem_cons_self hexcl)
    · have hexclB : excludedFiles.contains f = false := by
        cases hc : excludedFiles.contains f with
        | false => rfl
        | true =>
          have hm : f ∈ excludedFiles.toList := by
            simpa [Array.contains_iff_mem, Array.mem_toList_iff] using hc
          exact False.elim (hexcl hm)
      rcases ih errs0 with ⟨errs1, heq, hiff⟩
      refine ⟨errs1, ?_, ?_⟩
      · rw [List.forIn_cons]
        simp only [hexclB, Bool.false_eq_true, ↓reduceIte]
        dsimp only [bind, Except.bind]
        exact heq
      · rw [hiff]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨fun ⟨h0, hr⟩ => ⟨h0, hexcl, hr⟩, fun ⟨h0, _, hr⟩ => ⟨h0, hr⟩⟩

private theorem validateAnalysesLoop_eval
    (currentRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (l : List NoComments.RatchetCore.FileAnalysis)
    (errs0 : Array String)
    (liveMap0 : Std.HashMap String NoComments.RatchetCore.FileAnalysis) :
    ∃ state1 : Array String × Std.HashMap String NoComments.RatchetCore.FileAnalysis,
      (forIn (m := Except String) l (errs0, liveMap0) fun a s =>
        Except.ok (ForInStep.yield
          (match baseRatchet? with
           | some baseRatchet =>
             (s.1 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?) ++
               NoComments.RatchetCore.checkMonotonicFile a.file a.fingerprints
                 a.comments.size a.lines baseRatchet[a.file]?
           | none => s.1 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?,
           s.2.insert a.file a))) =
        Except.ok state1 ∧
      (state1.1.isEmpty = true ↔
        errs0.isEmpty = true ∧
        ∀ a ∈ l,
          ExactSyncOk a currentRatchet[a.file]? ∧
          match baseRatchet? with
          | some base => MonotonicOk a.fingerprints a.lines base[a.file]?
          | none => True) := by
  cases baseRatchet? with
  | none =>
    induction l generalizing errs0 liveMap0 with
    | nil =>
      refine ⟨(errs0, liveMap0), rfl, ?_⟩
      simp
    | cons a rest ih =>
      dsimp only
      let errsB := errs0 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?
      rcases ih errsB (liveMap0.insert a.file a) with ⟨state1, heq, hiff⟩
      refine ⟨state1, ?_, ?_⟩
      · rw [List.forIn_cons]
        dsimp only [bind, Except.bind]
        exact heq
      · rw [hiff]
        have hstep : errsB.isEmpty = true ↔
            errs0.isEmpty = true ∧ ExactSyncOk a currentRatchet[a.file]? := by
          dsimp only [errsB]
          rw [append_isEmpty, Bool.and_eq_true, checkExactSync_iff]
        rw [hstep]
        simp only [List.mem_cons, forall_eq_or_imp, and_true]
        constructor
        · rintro ⟨⟨h0, ha⟩, hr⟩; exact ⟨h0, ha, hr⟩
        · rintro ⟨h0, ha, hr⟩; exact ⟨⟨h0, ha⟩, hr⟩
  | some base =>
    induction l generalizing errs0 liveMap0 with
    | nil =>
      refine ⟨(errs0, liveMap0), rfl, ?_⟩
      simp
    | cons a rest ih =>
      dsimp only
      let errsB :=
        (errs0 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?) ++
          NoComments.RatchetCore.checkMonotonicFile a.file a.fingerprints
            a.comments.size a.lines base[a.file]?
      rcases ih errsB (liveMap0.insert a.file a) with ⟨state1, heq, hiff⟩
      refine ⟨state1, ?_, ?_⟩
      · rw [List.forIn_cons]
        dsimp only [bind, Except.bind]
        exact heq
      · rw [hiff]
        have hstep : errsB.isEmpty = true ↔
            errs0.isEmpty = true ∧
            ExactSyncOk a currentRatchet[a.file]? ∧
            MonotonicOk a.fingerprints a.lines base[a.file]? := by
          dsimp only [errsB]
          rw [append_isEmpty, append_isEmpty, Bool.and_eq_true, Bool.and_eq_true,
            checkExactSync_iff, checkMonotonicFile_iff, and_assoc]
        rw [hstep]
        simp only [List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨⟨h0, ha⟩, hr⟩; exact ⟨h0, ha, hr⟩
        · rintro ⟨h0, ha, hr⟩; exact ⟨⟨h0, ha⟩, hr⟩

private theorem validateBaseMissingLoop_eval
    (baseRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (liveMap : Std.HashMap String NoComments.RatchetCore.FileAnalysis)
    (l : List (String × NoComments.RatchetCore.RatchetEntry))
    (errs0 : Array String) :
    (forIn (m := Except String) l errs0 fun x errs =>
      if liveMap.contains x.1 = true then
        Except.ok (ForInStep.yield errs)
      else
        Except.ok (ForInStep.yield (errs ++ NoComments.RatchetCore.checkMonotonicFile x.1
          NoComments.Core.SortedFingerprints.empty 0 0 baseRatchet[x.1]?))) = Except.ok errs0 := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨f, _⟩
    rw [List.forIn_cons]
    by_cases hcont : liveMap.contains f = true
    · simp only [hcont, ↓reduceIte]
      dsimp only [bind, Except.bind]
      exact ih
    · have hcontF : liveMap.contains f = false := Bool.eq_false_iff.mpr hcont
      have hmc :
          errs0 ++ NoComments.RatchetCore.checkMonotonicFile f
            NoComments.Core.SortedFingerprints.empty 0 0 baseRatchet[f]? = errs0 := by
        rw [checkMonotonicFile_empty]
        simp
      rw [ite_eq_true_elim, hcontF]
      dsimp only [bind, Except.bind]
      rw [hmc]
      exact ih

private theorem unless_empty_ok_iff (errs : Array String) :
    (if errs.isEmpty = true then pure ()
      else throw (String.intercalate "\n" errs.toList)) =
        (Except.ok () : Except String Unit) ↔
      errs.isEmpty = true := by
  cases errs.isEmpty
  · constructor <;> intro h <;> cases h
  · constructor <;> intro _ <;> rfl

theorem validateCheck_iff
    (analyses : Array NoComments.RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (targetFile? : Option String) :
    NoComments.RatchetCore.validateCheck analyses checkedFiles excludedFiles
      currentRatchet baseRatchet? targetFile? = Except.ok () ↔
      ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := by
  unfold NoComments.RatchetCore.validateCheck ValidateOk
  dsimp only
  rw [forIn_congr_body currentRatchet.toList #[] _
    (fun x errs =>
      if excludedFiles.contains x.1 = true then
        Except.ok (ForInStep.yield (errs.push s!"checked-in ratchet contains excluded file '{x.1}'"))
      else if checkedFiles.contains x.1 = true then
        Except.ok (ForInStep.yield errs)
      else
        Except.ok (ForInStep.yield (errs.push s!"checked-in ratchet contains unknown or untracked file '{x.1}'")))
    fun ⟨f, _⟩ errs => by
      cases excludedFiles.contains f <;> cases checkedFiles.contains f <;> rfl]
  rcases validateCurLoop_eval checkedFiles excludedFiles currentRatchet.toList #[] with
    ⟨errs1, heq1, hiff1⟩
  have hcur_iff :
      (∀ kv ∈ currentRatchet.toList, kv.1 ∉ excludedFiles.toList ∧ kv.1 ∈ checkedFiles.toList) ↔
      (∀ f e, currentRatchet[f]? = some e → f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList) := by
    constructor
    · intro h f e hget
      exact h (f, e) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget)
    · rintro h ⟨f, e⟩ hmem
      exact h f e (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem)
  rw [heq1, except_bind_ok]
  cases baseRatchet? with
  | none =>
    dsimp only
    cases targetFile? with
    | none =>
      dsimp only
      rw [← Array.forIn_toList]
      rw [forIn_congr_body analyses.toList (errs1, (∅ : Std.HashMap String NoComments.RatchetCore.FileAnalysis)) _
        (fun a s =>
          Except.ok (ForInStep.yield
            (s.1 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?,
             s.2.insert a.file a)))]
      · rcases validateAnalysesLoop_eval currentRatchet none analyses.toList errs1 {} with
          ⟨⟨errs3, liveMap1⟩, heq3, hiff3⟩
        rw [heq3, except_bind_ok]
        dsimp only
        rw [unless_empty_ok_iff, hiff3, hiff1, hcur_iff]
        simp
      · intro a s; rfl
    | some target =>
      dsimp only
      cases hfind : analyses.find? (·.file == target) with
      | none =>
        dsimp only [throw, throwThe, MonadExceptOf.throw, except_bind_err]
        constructor
        · intro h; cases h
        · rintro ⟨_, _, live, hnone, _⟩; cases hnone
      | some live =>
        dsimp only
        rw [unless_empty_ok_iff, append_isEmpty, Bool.and_eq_true, checkExactSync_iff, hiff1, hcur_iff]
        simp only [Array.isEmpty_empty, true_and]
        constructor
        · intro ⟨hcur, hsync⟩; exact ⟨hcur, live, rfl, hsync, trivial⟩
        · rintro ⟨hcur, live', heqlive, hsync, _⟩
          injection heqlive with hl
          subst hl
          exact ⟨hcur, hsync⟩
  | some baseRatchet =>
    dsimp only
    rw [forIn_congr_body baseRatchet.toList errs1 _
      (fun x errs =>
        if excludedFiles.contains x.1 = true then
          Except.ok (ForInStep.yield (errs.push
            s!"cannot exclude '{x.1}' because merge-base ratchet still tracks comments in it"))
        else
          Except.ok (ForInStep.yield errs))
      fun ⟨f, _⟩ errs => by cases excludedFiles.contains f <;> rfl]
    rcases validateBaseLoop_eval excludedFiles baseRatchet.toList errs1 with
      ⟨errs2, heq2, hiff2⟩
    have hbase_iff :
        (∀ kv ∈ baseRatchet.toList, kv.1 ∉ excludedFiles.toList) ↔
        (∀ f e, baseRatchet[f]? = some e → f ∉ excludedFiles.toList) := by
      constructor
      · intro h f e hget
        exact h (f, e) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget)
      · rintro h ⟨f, e⟩ hmem
        exact h f e (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem)
    rw [heq2, except_bind_ok]
    cases targetFile? with
    | none =>
      dsimp only
      rw [← Array.forIn_toList]
      rw [forIn_congr_body analyses.toList (errs2, (∅ : Std.HashMap String NoComments.RatchetCore.FileAnalysis)) _
        (fun a s =>
          Except.ok (ForInStep.yield
            ((s.1 ++ NoComments.RatchetCore.checkExactSync a currentRatchet[a.file]?) ++
               NoComments.RatchetCore.checkMonotonicFile a.file a.fingerprints
                 a.comments.size a.lines baseRatchet[a.file]?,
             s.2.insert a.file a)))]
      · rcases validateAnalysesLoop_eval currentRatchet (some baseRatchet) analyses.toList errs2 {} with
          ⟨⟨errs3, liveMap1⟩, heq3, hiff3⟩
        rw [heq3, except_bind_ok]
        dsimp only
        rw [forIn_congr_body baseRatchet.toList errs3 _
          (fun x errs =>
            if liveMap1.contains x.1 = true then
              Except.ok (ForInStep.yield errs)
            else
              Except.ok (ForInStep.yield (errs ++ NoComments.RatchetCore.checkMonotonicFile x.1
                NoComments.Core.SortedFingerprints.empty 0 0 baseRatchet[x.1]?)))
          fun ⟨f, _⟩ errs => by cases liveMap1.contains f <;> rfl]
        rw [validateBaseMissingLoop_eval baseRatchet liveMap1 baseRatchet.toList errs3, except_bind_ok]
        rw [unless_empty_ok_iff, hiff3, hiff2, hiff1, hcur_iff, hbase_iff]
        exact ⟨fun ⟨⟨⟨_, h1⟩, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩⟩
      · intro a s; rfl
    | some target =>
      dsimp only
      cases hfind : analyses.find? (·.file == target) with
      | none =>
        dsimp only [throw, throwThe, MonadExceptOf.throw, except_bind_err]
        constructor
        · intro h; cases h
        · rintro ⟨_, _, live, hnone, _⟩; cases hnone
      | some live =>
        dsimp only
        rw [unless_empty_ok_iff, append_isEmpty, append_isEmpty, Bool.and_eq_true, Bool.and_eq_true,
          checkExactSync_iff, checkMonotonicFile_iff, hiff2, hiff1, hcur_iff, hbase_iff]
        simp only [Array.isEmpty_empty, true_and]
        constructor
        · intro ⟨⟨⟨hcur, hbase⟩, hsync⟩, hmono⟩
          exact ⟨hcur, hbase, live, rfl, hsync, hmono⟩
        · rintro ⟨hcur, hbase, live', heqlive, hsync, hmono⟩
          injection heqlive with hl
          subst hl
          exact ⟨⟨⟨hcur, hbase⟩, hsync⟩, hmono⟩

private theorem validateRefusal_of_not_ok
    (analyses : Array NoComments.RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (targetFile? : Option String)
    (hnot : ¬ ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?) :
    ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := by
  by_cases hcur : ∀ f e, currentRatchet[f]? = some e →
      f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList
  · cases hbase : baseRatchet? with
    | none =>
      cases htarget : targetFile? with
      | some target =>
        cases hfind : analyses.find? (·.file == target) with
        | none => exact ValidateRefusal.missingTargetAnalysis rfl hfind
        | some live =>
          by_cases hsync : ExactSyncOk live currentRatchet[target]?
          · rw [hbase, htarget] at hnot
            exact False.elim (hnot ⟨hcur, trivial, live, hfind, hsync, trivial⟩)
          · exact ValidateRefusal.targetSyncFailed rfl hfind hsync
      | none =>
        have hbad : ∃ a ∈ analyses.toList, ¬ ExactSyncOk a currentRatchet[a.file]? := by
          apply Classical.byContradiction
          intro hne
          rw [hbase, htarget] at hnot
          apply hnot
          refine ⟨hcur, trivial, fun a ha => ⟨?_, trivial⟩⟩
          apply Classical.byContradiction
          intro hns
          exact hne ⟨a, ha, hns⟩
        rcases hbad with ⟨a, hamem, hasync⟩
        exact ValidateRefusal.analysisSyncFailed rfl hamem hasync
    | some base =>
      by_cases hbaseok : ∀ f e, base[f]? = some e → f ∉ excludedFiles.toList
      · cases htarget : targetFile? with
        | some target =>
          cases hfind : analyses.find? (·.file == target) with
          | none => exact ValidateRefusal.missingTargetAnalysis rfl hfind
          | some live =>
            by_cases hsync : ExactSyncOk live currentRatchet[target]?
            · by_cases hmono : MonotonicOk live.fingerprints live.lines base[target]?
              · rw [hbase, htarget] at hnot
                exact False.elim (hnot ⟨hcur, hbaseok, live, hfind, hsync, hmono⟩)
              · exact ValidateRefusal.targetMonotonicFailed rfl rfl hfind hmono
            · exact ValidateRefusal.targetSyncFailed rfl hfind hsync
        | none =>
          have hbad : ∃ a ∈ analyses.toList,
              ¬ (ExactSyncOk a currentRatchet[a.file]? ∧
                MonotonicOk a.fingerprints a.lines base[a.file]?) := by
            apply Classical.byContradiction
            intro hne
            rw [hbase, htarget] at hnot
            apply hnot
            exact ⟨hcur, hbaseok, fun a ha => by
              apply Classical.byContradiction
              intro hn2
              exact hne ⟨a, ha, hn2⟩⟩
          rcases hbad with ⟨a, hamem, hnot2⟩
          by_cases hsync : ExactSyncOk a currentRatchet[a.file]?
          · exact ValidateRefusal.analysisMonotonicFailed rfl rfl hamem
              fun hm => hnot2 ⟨hsync, hm⟩
          · exact ValidateRefusal.analysisSyncFailed rfl hamem hsync
      · have hbadBase : ∃ f e, base[f]? = some e ∧ f ∈ excludedFiles.toList := by
          apply Classical.byContradiction
          intro hne
          apply hbaseok
          intro f e hget
          intro hexcl
          exact hne ⟨f, e, hget, hexcl⟩
        rcases hbadBase with ⟨f, e, hget, hexcl⟩
        exact ValidateRefusal.baseRatchetExcluded rfl hget hexcl
  · have hbadCur : ∃ f e, currentRatchet[f]? = some e ∧
        ¬ (f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList) := by
      apply Classical.byContradiction
      intro hne
      apply hcur
      intro f e hget
      apply Classical.byContradiction
      intro hb
      exact hne ⟨f, e, hget, hb⟩
    rcases hbadCur with ⟨f, e, hget, hbad⟩
    by_cases hexcl : f ∈ excludedFiles.toList
    · exact ValidateRefusal.currentRatchetExcluded hget hexcl
    · exact ValidateRefusal.currentRatchetUnknown hget fun hmem => hbad ⟨hexcl, hmem⟩

theorem validateCheck_ok
    (analyses : Array NoComments.RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (targetFile? : Option String)
    (hok : NoComments.RatchetCore.validateCheck analyses checkedFiles excludedFiles
      currentRatchet baseRatchet? targetFile? = .ok ()) :
    ValidateOk analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? :=
  (validateCheck_iff analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?).mp hok

theorem validateCheck_err
    (analyses : Array NoComments.RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String NoComments.RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String NoComments.RatchetCore.RatchetEntry))
    (targetFile? : Option String) (msg : String)
    (herr : NoComments.RatchetCore.validateCheck analyses checkedFiles excludedFiles
      currentRatchet baseRatchet? targetFile? = .error msg) :
    ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile? := by
  apply validateRefusal_of_not_ok
  intro hok
  have heq :=
    (validateCheck_iff analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?).mpr hok
  rw [herr] at heq
  cases heq

theorem validateCheck_meets :
    validateCheckRecord.Meets NoComments.RatchetCore.validateCheck := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact validateCheck_ok
  rcases List.mem_cons.mp hp with rfl | hp
  · exact validateCheck_err
  exact nomatch hp

theorem validateCheck_refines :
    Refines validateCheckRecord (fun f => f) (· = NoComments.RatchetCore.validateCheck) :=
  fun _ hf _ => hf ▸ validateCheck_meets.2

theorem validateCheck_fulfilled :
    validateCheckRecord.Fulfilled NoComments.RatchetCore.validateCheck :=
  fulfils validateCheck_refines rfl

end NoCommentsSpecification.Refinement.Ratchet
