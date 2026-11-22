module

import all Init.Data.String.Search
import all Init.Data.String.Basic
import all Init.Data.String.Subslice
import all Init.Data.Nat.ToString
import all Init.Data.ByteArray.Basic
import all Init.Meta.Defs
public import LeanIntent.Refinement
public import Std.Data.HashMap.Lemmas
public import NoComments.Core
public import NoCommentsSpecification.CoreRecords

@[expose] public section

namespace NoCommentsSpecification.Refinement.Core

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreSpec
open NoCommentsSpecification.CoreRecords

theorem isHexLowerChar_eq_isDigit (c : Char) :
    CoreSpec.isHexLowerChar c = (c.isDigit || ('a' ≤ c && c ≤ 'f')) := by
  simp only [CoreSpec.isHexLowerChar, Char.isDigit, ge_iff_le]
  rfl

theorem isFingerprint_meets : isFingerprintRecord.Meets NoComments.Core.isFingerprint := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro s
    simp only [NoComments.Core.isFingerprint, CoreSpec.IsFingerprint, isHexLowerChar_eq_isDigit,
      Bool.and_eq_true, beq_iff_eq, String.all_bool_eq, List.all_eq_true]
  exact nomatch hp

theorem isFingerprint_refines :
    Refines isFingerprintRecord (fun f => f) (· = NoComments.Core.isFingerprint) :=
  fun _ hf _ => hf ▸ isFingerprint_meets.2

theorem isFingerprint_fulfilled : isFingerprintRecord.Fulfilled NoComments.Core.isFingerprint :=
  fulfils isFingerprint_refines rfl

theorem digitChar_hex {d : Nat} (hd : d < 16) :
    CoreSpec.isHexLowerChar d.digitChar = true := by
  match d, hd with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    simp only [CoreSpec.isHexLowerChar, Nat.digitChar, ↓reduceIte]
    decide
  | _ + 16, hd => omega

theorem toDigits_16_hex (n : Nat) :
    ∀ c ∈ Nat.toDigits 16 n, CoreSpec.isHexLowerChar c = true := by
  intro c hc
  rw [Nat.toDigits_eq_ite (by omega : 1 < 16)] at hc
  split at hc
  · simp only [List.mem_singleton] at hc
    subst hc
    exact digitChar_hex ‹_›
  · simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact toDigits_16_hex (n / 16) c hc
    · exact digitChar_hex (Nat.mod_lt n (by omega))
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

theorem fingerprint_isFingerprint (text : String) :
    CoreSpec.IsFingerprint (NoComments.Core.fingerprint text) := by
  simp only [NoComments.Core.fingerprint, CoreSpec.IsFingerprint]
  have hlt :
      (text.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211)
        (14695981039346656037 : UInt64)).toNat < 16 ^ 16 := by
    have hsz := UInt64.toNat_lt_size
      (text.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211)
        (14695981039346656037 : UInt64))
    have hpow : UInt64.size = 16 ^ 16 := rfl
    omega
  have hlen :
      (Nat.toDigits 16
        (text.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211)
          (14695981039346656037 : UInt64)).toNat).length ≤ 16 :=
    (Nat.length_toDigits_le_iff (by omega : 1 < 16) (by omega : 0 < 16)).mpr hlt
  refine ⟨?_, ?_⟩
  · simp only [String.length_ofList, List.length_append, List.length_replicate]
    omega
  · intro c hc
    simp only [String.toList_ofList, List.mem_append, List.mem_replicate] at hc
    rcases hc with ⟨_, rfl⟩ | hc
    · decide
    · exact toDigits_16_hex _ c hc

theorem fingerprint_nonconstant : ∃ a b : String,
    NoComments.Core.fingerprint a ≠ NoComments.Core.fingerprint b :=
  ⟨"a", "b", by decide⟩

theorem fingerprint_meets : fingerprintRecord.Meets NoComments.Core.fingerprint := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fingerprint_isFingerprint
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fingerprint_nonconstant
  exact nomatch hp

theorem fingerprint_refines :
    Refines fingerprintRecord (fun f => f) (· = NoComments.Core.fingerprint) :=
  fun _ hf _ => hf ▸ fingerprint_meets.2

theorem fingerprint_fulfilled : fingerprintRecord.Fulfilled NoComments.Core.fingerprint :=
  fulfils fingerprint_refines rfl

theorem hasCharPair_eq_infix (a b : Char) (cs : List Char) :
    CoreSpec.hasCharPair a b cs = true ↔ [a, b] <:+: cs := by
  induction cs with
  | nil =>
    simp only [CoreSpec.hasCharPair, Bool.false_eq_true, false_iff]
    rintro ⟨p, s, h⟩
    have hlen := congrArg List.length h
    simp at hlen
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [CoreSpec.hasCharPair, Bool.false_eq_true, false_iff]
      rintro ⟨p, s, h⟩
      have hlen := congrArg List.length h
      simp at hlen
      omega
    | cons y ys =>
      simp only [CoreSpec.hasCharPair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro (⟨rfl, rfl⟩ | h)
        · exact ⟨[], ys, by simp⟩
        · rcases ih.mp h with ⟨p, s, hp⟩
          exact ⟨x :: p, s, by simp [hp]⟩
      · rintro ⟨p, s, hp⟩
        cases p with
        | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at hp
          exact Or.inl ⟨hp.1.symm, hp.2.1.symm⟩
        | cons z pz =>
          simp only [List.cons_append, List.cons.injEq] at hp
          exact Or.inr (ih.mpr ⟨pz, s, hp.2⟩)

theorem containsOpener_eq (raw : String) :
    NoComments.Core.containsOpener raw = CoreSpec.containsOpener raw := by
  apply Bool.eq_iff_iff.mpr
  simp only [NoComments.Core.containsOpener, CoreSpec.containsOpener, Bool.or_eq_true,
    String.contains_string_iff, hasCharPair_eq_infix]
  have h1 : "--".toList = ['-', '-'] := rfl
  have h2 : "/-".toList = ['/', '-'] := rfl
  rw [h1, h2]

theorem singleton_suffix_iff_getLast? (c : Char) (cs : List Char) :
    [c] <:+ cs ↔ cs.getLast? = some c := by
  induction cs with
  | nil =>
    simp [List.suffix_nil]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq]
      constructor
      · rintro ⟨p, hp⟩
        cases p with
        | nil => simp at hp; exact hp.symm
        | cons _ _ =>
          have hlen := congrArg List.length hp
          simp at hlen
      · rintro rfl
        exact ⟨[], rfl⟩
    | cons y ys =>
      simp only [List.getLast?_cons_cons]
      constructor
      · rintro ⟨p, hp⟩
        apply ih.mp
        cases p with
        | nil =>
          have hlen := congrArg List.length hp
          simp at hlen
        | cons _ pz =>
          simp only [List.cons_append, List.cons.injEq] at hp
          exact ⟨pz, hp.2⟩
      · intro h
        rcases ih.mpr h with ⟨p, hp⟩
        exact ⟨x :: p, by simp [hp]⟩

theorem crossesBoundary_eq (raw : String) (next : Char) :
    NoComments.Core.crossesBoundary raw next = CoreSpec.crossesBoundary raw next := by
  apply Bool.eq_iff_iff.mpr
  simp only [NoComments.Core.crossesBoundary, CoreSpec.crossesBoundary, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, String.endsWith_eq_endsWith_toSlice,
    String.Slice.endsWith_string_iff, String.copy_toSlice]
  have h1 : "-".toList = ['-'] := rfl
  have h2 : "/".toList = ['/'] := rfl
  rw [h1, h2, singleton_suffix_iff_getLast?, singleton_suffix_iff_getLast?]

theorem isLit_getArg_eq (s : Syntax) (k : SyntaxNodeKind) :
    Syntax.isLit? k s[0] = (s[0]?).bind (Syntax.isLit? k) := by
  cases s <;> simp [Syntax.isLit?]

theorem matchesLiteralToken_eq (env : Environment) (tok : Syntax) (raw : String) :
    NoComments.Core.matchesLiteralToken env tok raw = CoreSpec.literalToken env tok raw := by
  dsimp [NoComments.Core.matchesLiteralToken, CoreSpec.literalToken, CoreSpec.parseWith, Id.run]
  cases tok with
  | ident info spelling val pre =>
    dsimp [bind, Option.bind, pure, guard, Alternative.failure]
    by_cases herr :
        (Parser.tokenFn.run (Parser.InputContext.mk raw "<token>") { env := env, options := ∅ } ∅
          (Parser.mkParserState raw)).hasError = false
    · by_cases hsz :
          (Parser.tokenFn.run (Parser.InputContext.mk raw "<token>") { env := env, options := ∅ } ∅
            (Parser.mkParserState raw)).stackSize = 1
      · simp [herr, hsz]; rfl
      · simp [herr, hsz]
    · simp [herr]
  | node info k args =>
    dsimp [bind, Option.bind, pure, guard, Alternative.failure]
    by_cases hlit : Syntax.isLit? k (.node info k args) == some raw
    · simp only [hlit, ↓reduceIte]
      by_cases hk : k == interpolatedStrLitKind
      · simp only [hk, ↓reduceIte]
        by_cases hc :
            (let chunk := if raw.startsWith "}" then "\"" ++ (raw.drop 1).toString else raw
             let emptyHole : Parser.ParserFn := fun _ s => s.pushSyntax .missing
             let st := (Parser.interpolatedStrFn emptyHole).run
               (Parser.InputContext.mk (chunk ++ "}\"") "<token>")
               { env := env, options := ∅ } ∅ (Parser.mkParserState (chunk ++ "}\""))
             !st.hasError && st.stackSize == 1) = true
        · simp only [hc, ↓reduceIte]
          rw [isLit_getArg_eq]
          rfl
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        by_cases herr :
            (Parser.tokenFn.run (Parser.InputContext.mk raw "<token>") { env := env, options := ∅ } ∅
              (Parser.mkParserState raw)).hasError = false
        · by_cases hsz :
              (Parser.tokenFn.run (Parser.InputContext.mk raw "<token>") { env := env, options := ∅ } ∅
                (Parser.mkParserState raw)).stackSize = 1
          · simp [herr, hsz]
          · simp [herr, hsz]
        · simp [herr]
    · simp [hlit]
  | missing => rfl
  | atom _ _ => rfl

theorem matchesRegisteredSymbol_eq (ctx : Parser.ParserContextCore) (tok : Syntax) :
    NoComments.Core.matchesRegisteredSymbol ctx tok = CoreSpec.registeredSymbol ctx tok :=
  rfl

theorem checkToken_ok_spec {ctx : Parser.ParserContextCore} {tok : Syntax} {raw : String}
    {next : Char} {start : String.Pos.Raw}
    (h : NoComments.Core.checkToken ctx tok raw next start = .ok ()) :
    CoreSpec.TokenSafe ctx tok raw next := by
  have hiff := (NoComments.Core.checkToken_ok_iff ctx tok raw next start).mp h
  rw [matchesLiteralToken_eq, matchesRegisteredSymbol_eq, containsOpener_eq, crossesBoundary_eq] at hiff
  exact hiff

theorem checkToken_error_spec {ctx : Parser.ParserContextCore} {tok : Syntax} {raw : String}
    {next : Char} {start : String.Pos.Raw} {msg : String}
    (h : NoComments.Core.checkToken ctx tok raw next start = .error msg) :
    CoreSpec.TokenRefusal ctx tok raw next := by
  simp only [NoComments.Core.checkToken] at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hcond
    rcases hcond with ⟨⟨hopen | hcross, hlit⟩, hsym⟩
    · rw [matchesLiteralToken_eq] at hlit
      rw [matchesRegisteredSymbol_eq] at hsym
      rw [containsOpener_eq] at hopen
      exact TokenRefusal.openerInRaw hlit hsym hopen
    · rw [matchesLiteralToken_eq] at hlit
      rw [matchesRegisteredSymbol_eq] at hsym
      rw [crossesBoundary_eq] at hcross
      exact TokenRefusal.boundaryCross hlit hsym hcross
  · cases h

theorem checkToken_meets : checkTokenRecord.Meets NoComments.Core.checkToken := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fun _ _ _ _ _ h => checkToken_ok_spec h
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fun _ _ _ _ _ _ h => checkToken_error_spec h
  exact nomatch hp

theorem checkToken_refines :
    Refines checkTokenRecord (fun f => f) (· = NoComments.Core.checkToken) :=
  fun _ hf _ => hf ▸ checkToken_meets.2

theorem checkToken_fulfilled : checkTokenRecord.Fulfilled NoComments.Core.checkToken :=
  fulfils checkToken_refines rfl

theorem originalLeafIn_toSpec {s leaf : Syntax} {start stop : String.Pos.Raw}
    (h : NoComments.Core.OriginalLeafIn s leaf start stop) :
    CoreSpec.OriginalLeafIn s leaf start stop := by
  induction h with
  | atom info val leading trail start stop hinfo =>
    exact CoreSpec.OriginalLeafIn.atom info val leading trail start stop hinfo
  | ident info rawVal val pre leading trail start stop hinfo =>
    exact CoreSpec.OriginalLeafIn.ident info rawVal val pre leading trail start stop hinfo
  | singletonAtomNode info k atomInfo val leading trail start stop hnotDoc hnotChoice hinfo =>
    exact CoreSpec.OriginalLeafIn.singletonAtomNode info k atomInfo val leading trail start stop
      hnotDoc hnotChoice hinfo
  | child info k args arg leaf start stop hmem _ ih =>
    exact CoreSpec.OriginalLeafIn.child info k args arg leaf start stop hmem ih

theorem triviaByteCovered_toSpec {str : String} {acc : NoComments.Core.CommentAcc} {lo hi b : Nat}
    (h : NoComments.Core.TriviaByteCovered str acc lo hi b) :
    CoreSpec.TriviaByteCovered str acc lo hi b :=
  h

theorem byteAccounted_toSpec {ctx : Parser.ParserContextCore} {stx : Syntax}
    {acc : NoComments.Core.CommentAcc} {lo hi b : Nat}
    (h : NoComments.Core.ByteAccounted ctx stx acc lo hi b) :
    CoreSpec.ByteAccounted ctx stx acc lo hi b := by
  rcases h with htriv | ⟨leaf, start, stop, hleaf, h1, h2, h3, h4, htok⟩
  · exact Or.inl (triviaByteCovered_toSpec htriv)
  · exact Or.inr ⟨leaf, start, stop, originalLeafIn_toSpec hleaf, h1, h2, h3, h4,
      checkToken_ok_spec htok⟩

theorem contiguousFrom_toCore {s e : String.Pos.Raw} {ranges : List NoComments.Core.CommandRange}
    (h : CoreSpec.ContiguousFrom s e ranges) :
    NoComments.Core.ContiguousFrom s e ranges := by
  induction ranges generalizing s with
  | nil => exact h
  | cons r rest ih =>
    rcases h with ⟨hprev, _, hrest⟩
    exact ⟨hprev, ih hrest⟩

theorem collectRanges_range_coverage (ranges : List NoComments.Core.CommandRange)
    (acc acc' : NoComments.Core.CommentAcc)
    (h : NoComments.Core.collectRanges ranges acc = .ok acc') :
    ∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
      CoreSpec.ByteAccounted r.ctx r.stx acc' r.prevPos.byteIdx r.nextPos.byteIdx b := by
  induction ranges generalizing acc with
  | nil =>
    intro r hr
    cases hr
  | cons r0 rest ih =>
    simp only [NoComments.Core.collectRanges, bind, Except.bind] at h
    cases h1 : NoComments.Core.collectSyntax r0.ctx r0.prevPos r0.nextPos r0.stx acc with
    | error e => rw [h1] at h; cases h
    | ok acc1 =>
      rw [h1] at h
      intro r hr b hb1 hb2
      rcases List.mem_cons.mp hr with rfl | hmem
      · have hcov := NoComments.Core.collectSyntax_coverage r.ctx r.prevPos r.nextPos r.stx acc acc1 h1
        have hpres := NoComments.Core.collectRanges_preserves rest acc1 acc' h
        exact byteAccounted_toSpec
          (NoComments.Core.byteAccounted_mono hpres (fun _ _ _ hi => hi)
            (Nat.le_refl _) (Nat.le_refl _) (hcov.2.2 b hb1 hb2))
      · exact ih acc1 h r hmem b hb1 hb2

theorem recordSpan_ok_props {fileMap : FileMap} {kind : String}
    {startPos stopPos : String.Pos.Raw} {acc acc' : NoComments.Core.CommentAcc}
    (hkind : validCommentKind kind)
    (h : NoComments.Core.recordSpan fileMap kind startPos stopPos acc = .ok acc') :
    startPos.byteIdx < stopPos.byteIdx ∧
      (∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (sb = startPos.byteIdx ∧ eb = stopPos.byteIdx ∧ c.kind = kind ∧
            CoreSpec.IsFingerprint c.fingerprint ∧
            c.startLine = (fileMap.toPosition startPos).line ∧
            c.endLine = (fileMap.toPosition (String.Pos.Raw.prev fileMap.source stopPos)).line ∧
            c.fingerprint = NoComments.Core.fingerprint
              (CoreSpec.commentText fileMap startPos.byteIdx stopPos.byteIdx))) ∧
      ¬ CoreSpec.SpanConflict (CoreSpec.stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx ∧
      CoreSpec.stateOfAcc acc' =
        CoreSpec.insertSpan (CoreSpec.stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx := by
  have _ := hkind
  simp only [NoComments.Core.recordSpan] at h
  split at h
  · cases h
  · rename_i hnotle
    have hlt : startPos.byteIdx < stopPos.byteIdx := Nat.lt_of_not_le hnotle
    split at h
    · rename_i prevStop prev hsome
      split at h
      · rename_i heq
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        rcases heq with ⟨hpst, hpk⟩
        refine ⟨hlt, fun sb eb c hs => Or.inl hs, ?_, ?_⟩
        · rintro (hle | ⟨peb, pk, hst, hne⟩)
          · omega
          · simp only [CoreSpec.stateOfAcc, hsome, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hst
            rcases hst with ⟨rfl, rfl⟩
            rcases hne with hne | hne
            · exact hne hpst
            · exact hne hpk
        · funext x
          by_cases hx : x = startPos.byteIdx
          · subst hx
            simp only [CoreSpec.insertSpan, beq_self_eq_true, ↓reduceIte, CoreSpec.stateOfAcc, hsome,
              Option.map_some, hpst, hpk]
          · have hne2 : (x == startPos.byteIdx) = false := beq_false_of_ne hx
            simp only [CoreSpec.insertSpan, hne2, Bool.false_eq_true, ↓reduceIte]
      · cases h
    · rename_i hnone
      cases h
      refine ⟨hlt, ?_, ?_, ?_⟩
      · intro sb eb c hs
        by_cases hsb : sb = startPos.byteIdx
        · subst hsb
          rw [Std.HashMap.getElem?_insert_self] at hs
          cases hs
          have hfp := fingerprint_isFingerprint
            (⟨fileMap.source, startPos, stopPos⟩ : Substring.Raw).toString
          cases startPos
          cases stopPos
          exact Or.inr ⟨rfl, rfl, rfl, hfp, rfl, rfl, rfl⟩
        · have hne : (startPos.byteIdx == sb) = false := beq_false_of_ne (fun heq => hsb heq.symm)
          simp only [Std.HashMap.getElem?_insert, hne, Bool.false_eq_true, ↓reduceIte] at hs
          exact Or.inl hs
      · rintro (hle | ⟨peb, pk, hst, _⟩)
        · omega
        · simp only [CoreSpec.stateOfAcc, hnone, Option.map_none] at hst
          cases hst
      · funext x
        by_cases hx : x = startPos.byteIdx
        · subst hx
          simp only [CoreSpec.insertSpan, beq_self_eq_true, ↓reduceIte, CoreSpec.stateOfAcc,
            Std.HashMap.getElem?_insert_self, Option.map_some]
        · have hne : (startPos.byteIdx == x) = false := beq_false_of_ne (fun heq => hx heq.symm)
          have hne2 : (x == startPos.byteIdx) = false := beq_false_of_ne hx
          simp only [CoreSpec.insertSpan, hne2, Bool.false_eq_true, ↓reduceIte,
            CoreSpec.stateOfAcc, Std.HashMap.getElem?_insert, hne]

theorem recordSpan_error_conflict {fileMap : FileMap} {kind : String}
    {startPos stopPos : String.Pos.Raw} {acc : NoComments.Core.CommentAcc} {msg : String}
    (h : NoComments.Core.recordSpan fileMap kind startPos stopPos acc = .error msg) :
    CoreSpec.SpanConflict (CoreSpec.stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx := by
  simp only [NoComments.Core.recordSpan] at h
  split at h
  · rename_i hle
    exact Or.inl hle
  · split at h
    · rename_i prevStop prev hsome
      split at h
      · cases h
      · rename_i hne
        refine Or.inr ⟨prevStop, prev.kind, ?_, ?_⟩
        · simp [CoreSpec.stateOfAcc, hsome]
        · simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hne
          by_cases h1 : prevStop = stopPos.byteIdx
          · exact Or.inr (hne h1)
          · exact Or.inl h1
    · cases h

theorem toEol_lineEnd (str : String) (stopPos p : String.Pos.Raw) (hp : p ≤ stopPos) :
    CoreSpec.LineEnd str stopPos p (NoComments.Core.toEol str stopPos p) := by
  have _ := hp
  unfold NoComments.Core.toEol
  split
  · rename_i hlt
    split
    · rename_i heq
      exact CoreSpec.LineEnd.nl hlt (beq_iff_eq.mp heq)
    · rename_i hne
      have hne' : String.Pos.Raw.get str p ≠ '\n' := fun h => hne (beq_iff_eq.mpr h)
      have hstep : p.byteIdx < (String.Pos.Raw.next str p).byteIdx :=
        String.Pos.Raw.byteIdx_lt_byteIdx_next str p
      by_cases hnext : String.Pos.Raw.next str p ≤ stopPos
      · exact CoreSpec.LineEnd.step hlt hne'
          (toEol_lineEnd str stopPos (String.Pos.Raw.next str p) hnext)
      · have hge : ¬ String.Pos.Raw.next str p < stopPos := fun h =>
          hnext (String.Pos.Raw.le_iff.mpr (Nat.le_of_lt (String.Pos.Raw.lt_iff.mp h)))
        have heq : NoComments.Core.toEol str stopPos (String.Pos.Raw.next str p) = stopPos := by
          unfold NoComments.Core.toEol
          simp [hge]
        rw [heq]
        exact CoreSpec.LineEnd.step hlt hne' (CoreSpec.LineEnd.done hge)
  · rename_i hge
    exact CoreSpec.LineEnd.done hge
termination_by stopPos.byteIdx - p.byteIdx
decreasing_by
  have hle : p.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  omega

theorem finishBlock_step_and_closes (str : String) (stopPos : String.Pos.Raw) (nesting : Nat)
    (pos endPos : String.Pos.Raw) (hnest : nesting ≥ 1)
    (h : NoComments.Core.finishBlock str stopPos nesting pos = .ok endPos) :
    CoreSpec.BlockStep str stopPos nesting pos endPos ∧
      ∃ pm ps : String.Pos.Raw,
        ps = String.Pos.Raw.next str pm ∧ endPos = String.Pos.Raw.next str ps ∧
          String.Pos.Raw.get str pm = '-' ∧ String.Pos.Raw.get str ps = '/' := by
  unfold NoComments.Core.finishBlock at h
  dsimp only at h
  split at h
  · rename_i hlt
    split at h
    · rename_i hcl
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
      split at h
      · rename_i hafter
        split at h
        · rename_i hn1
          have hn1' : nesting = 1 := beq_iff_eq.mp hn1
          cases h
          exact ⟨CoreSpec.BlockStep.closeTop hn1' hlt hcl.1.1 hcl.1.2 hcl.2 hafter,
            pos, String.Pos.Raw.next str pos, rfl, rfl, hcl.1.1, hcl.2⟩
        · rename_i hnn1
          have hnn1' : nesting ≠ 1 := fun heq => hnn1 (beq_iff_eq.mpr heq)
          have hnest' : nesting - 1 ≥ 1 := by omega
          rcases finishBlock_step_and_closes str stopPos (nesting - 1)
            (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos hnest' h with
            ⟨hstep, hclose⟩
          exact ⟨CoreSpec.BlockStep.closeNested hnn1' hnest hlt hcl.1.1 hcl.1.2 hcl.2 hafter hstep,
            hclose⟩
      · cases h
    · rename_i hnotcl
      split at h
      · rename_i hop
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hop
        split at h
        · rename_i hafter
          rcases finishBlock_step_and_closes str stopPos (nesting + 1)
            (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos (by omega) h with
            ⟨hstep, hclose⟩
          exact ⟨CoreSpec.BlockStep.openNested hnest hlt hop.1.1 hop.1.2 hop.2 hafter hstep,
            hclose⟩
        · cases h
      · rename_i hnotop
        have h1 : ¬ (String.Pos.Raw.get str pos = '-' ∧
            String.Pos.Raw.next str pos < stopPos ∧
            String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/') :=
          fun hc => hnotcl (by simp [hc.1, hc.2.1, hc.2.2])
        have h2 : ¬ (String.Pos.Raw.get str pos = '/' ∧
            String.Pos.Raw.next str pos < stopPos ∧
            String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-') :=
          fun hc => hnotop (by simp [hc.1, hc.2.1, hc.2.2])
        rcases finishBlock_step_and_closes str stopPos nesting (String.Pos.Raw.next str pos) endPos
          hnest h with ⟨hstep, hclose⟩
        exact ⟨CoreSpec.BlockStep.other hnest hlt h1 h2 hstep, hclose⟩
  · cases h
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next str pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · change stopPos.byteIdx - (String.Pos.Raw.next str pos).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega

theorem finishBlock_fails (str : String) (stopPos : String.Pos.Raw) (nesting : Nat)
    (pos : String.Pos.Raw) {msg : String}
    (h : NoComments.Core.finishBlock str stopPos nesting pos = .error msg) :
    CoreSpec.BlockFails str stopPos nesting pos := by
  unfold NoComments.Core.finishBlock at h
  dsimp only at h
  split at h
  · rename_i hlt
    split at h
    · rename_i hcl
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
      split at h
      · rename_i hafter
        split at h
        · cases h
        · rename_i hnn1
          have hnn1' : nesting ≠ 1 := fun heq => hnn1 (beq_iff_eq.mpr heq)
          exact CoreSpec.BlockFails.closeNested hnn1' hlt hcl.1.1 hcl.1.2 hcl.2 hafter
            (finishBlock_fails str stopPos (nesting - 1)
              (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) h)
      · rename_i hnotafter
        exact CoreSpec.BlockFails.closeBoundary hlt hcl.1.1 hcl.1.2 hcl.2 hnotafter
    · rename_i hnotcl
      split at h
      · rename_i hop
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hop
        split at h
        · rename_i hafter
          exact CoreSpec.BlockFails.openNested hlt hop.1.1 hop.1.2 hop.2 hafter
            (finishBlock_fails str stopPos (nesting + 1)
              (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) h)
        · rename_i hnotafter
          exact CoreSpec.BlockFails.openBoundary hlt hop.1.1 hop.1.2 hop.2 hnotafter
      · rename_i hnotop
        have h1 : ¬ (String.Pos.Raw.get str pos = '-' ∧
            String.Pos.Raw.next str pos < stopPos ∧
            String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/') :=
          fun hc => hnotcl (by simp [hc.1, hc.2.1, hc.2.2])
        have h2 : ¬ (String.Pos.Raw.get str pos = '/' ∧
            String.Pos.Raw.next str pos < stopPos ∧
            String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-') :=
          fun hc => hnotop (by simp [hc.1, hc.2.1, hc.2.2])
        exact CoreSpec.BlockFails.other hlt h1 h2
          (finishBlock_fails str stopPos nesting (String.Pos.Raw.next str pos) h)
  · rename_i hge
    exact CoreSpec.BlockFails.atEof hge
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next str pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · change stopPos.byteIdx - (String.Pos.Raw.next str pos).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega

theorem scanTriviaGo_ok_props (ctx : Parser.ParserContextCore) (stx : Syntax)
    (stopPos pos : String.Pos.Raw) (acc acc' : NoComments.Core.CommentAcc)
    (hstop : stopPos ≤ ctx.endPos)
    (h : NoComments.Core.scanTriviaGo ctx.fileMap stopPos pos acc = .ok acc') :
    CoreSpec.TriviaStep ctx.fileMap stopPos pos (CoreSpec.stateOfAcc acc) (CoreSpec.stateOfAcc acc') ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (pos.byteIdx ≤ sb ∧ eb ≤ stopPos.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx stx sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb)) := by
  unfold NoComments.Core.scanTriviaGo at h
  dsimp only at h
  split at h
  · rename_i hlt
    split at h
    · rename_i hws
      split at h
      · rename_i hnext
        have hstep1 : pos.byteIdx < (String.Pos.Raw.next ctx.fileMap.source pos).byteIdx :=
          String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source pos
        rcases scanTriviaGo_ok_props ctx stx stopPos (String.Pos.Raw.next ctx.fileMap.source pos)
          acc acc' hstop h with ⟨htstep, hgen⟩
        refine ⟨CoreSpec.TriviaStep.ws hlt hws hnext htstep, ?_⟩
        intro sb eb c hs
        rcases hgen sb eb c hs with hsame | ⟨h1, h2, hg⟩
        · exact Or.inl hsame
        · exact Or.inr ⟨by omega, h2, hg⟩
      · cases h
    · rename_i hnotws
      split at h
      · rename_i hline
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hline
        split at h
        · rename_i hafter
          cases hrec : NoComments.Core.recordSpan ctx.fileMap "line" pos
              (NoComments.Core.toEol ctx.fileMap.source stopPos
                (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
              acc with
          | error e => rw [hrec] at h; cases h
          | ok acc1 =>
            rw [hrec] at h
            have heolB := NoComments.Core.toEol_bounds ctx.fileMap.source stopPos
              (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)) hafter
            have hlineEnd := toEol_lineEnd ctx.fileMap.source stopPos
              (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)) hafter
            rcases recordSpan_ok_props (by simp [CoreSpec.validCommentKind]) hrec with
              ⟨hltSpan, hrecNew, hnoc, hstate1⟩
            rcases scanTriviaGo_ok_props ctx stx stopPos
              (NoComments.Core.toEol ctx.fileMap.source stopPos
                (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
              acc1 acc' hstop h with ⟨htstep, hgen⟩
            refine ⟨?_, ?_⟩
            · rw [hstate1] at htstep
              exact CoreSpec.TriviaStep.line hlt hline.1.1 hline.1.2 hline.2 hafter hlineEnd hnoc htstep
            · intro sb eb c hs
              rcases hgen sb eb c hs with hacc1 | ⟨h1, h2, hg, hfeq⟩
              · rcases hrecNew sb eb c hacc1 with hacc | ⟨rfl, rfl, hk, hfp, hsl, hel, hfeq⟩
                · exact Or.inl hacc
                · refine Or.inr ⟨Nat.le_refl _, String.Pos.Raw.le_iff.mp heolB.2,
                    ⟨hltSpan, Nat.le_trans (String.Pos.Raw.le_iff.mp heolB.2) (String.Pos.Raw.le_iff.mp hstop),
                      by simp [CoreSpec.validCommentKind, hk], hfp, hsl, hel, Or.inl ⟨hk, ?_⟩⟩, hfeq⟩
                  exact ⟨hline.1.1, hline.2, String.Pos.Raw.le_iff.mp heolB.1,
                    CoreSpec.lineEnd_self hafter hlineEnd⟩
              · have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source pos
                have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)
                have hleEol := String.Pos.Raw.le_iff.mp heolB.1
                exact Or.inr ⟨by omega, h2, hg, hfeq⟩
        · cases h
      · rename_i hnotline
        split at h
        · rename_i hblk
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hblk
          split at h
          · rename_i hafterOpen
            split at h
            · cases h
            · rename_i hnotdoc
              simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnotdoc
              split at h
              · rename_i hbodyStart
                cases hfb : NoComments.Core.finishBlock ctx.fileMap.source stopPos 1
                    (String.Pos.Raw.next ctx.fileMap.source
                      (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))) with
                | error e => rw [hfb] at h; cases h
                | ok endPos =>
                  rw [hfb] at h
                  dsimp only at h
                  cases hrec : NoComments.Core.recordSpan ctx.fileMap "block" pos endPos acc with
                  | error e => rw [hrec] at h; cases h
                  | ok acc1 =>
                    rw [hrec] at h
                    dsimp only at h
                    have hfbB := NoComments.Core.finishBlock_bounds ctx.fileMap.source stopPos 1
                      (String.Pos.Raw.next ctx.fileMap.source
                        (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
                      endPos hfb
                    rcases finishBlock_step_and_closes ctx.fileMap.source stopPos 1
                      (String.Pos.Raw.next ctx.fileMap.source
                        (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
                      endPos (by omega) hfb with ⟨hbstep, pm, ps, hps, hend, hpm, hpsC⟩
                    rcases recordSpan_ok_props (by simp [CoreSpec.validCommentKind]) hrec with
                      ⟨hltSpan, hrecNew, hnoc, hstate1⟩
                    rcases scanTriviaGo_ok_props ctx stx stopPos endPos acc1 acc' hstop h with
                      ⟨htstep, hgen⟩
                    refine ⟨?_, ?_⟩
                    · rw [hstate1] at htstep
                      exact CoreSpec.TriviaStep.block hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen
                        hnotdoc.1 hnotdoc.2 hbodyStart hbstep hnoc htstep
                    · intro sb eb c hs
                      rcases hgen sb eb c hs with hacc1 | ⟨h1, h2, hg, hfeq⟩
                      · rcases hrecNew sb eb c hacc1 with hacc | ⟨rfl, rfl, hk, hfp, hsl, hel, hfeq⟩
                        · exact Or.inl hacc
                        · refine Or.inr ⟨Nat.le_refl _, String.Pos.Raw.le_iff.mp hfbB.2,
                            ⟨hltSpan, Nat.le_trans (String.Pos.Raw.le_iff.mp hfbB.2) (String.Pos.Raw.le_iff.mp hstop),
                              by simp [CoreSpec.validCommentKind, hk], hfp, hsl, hel, Or.inr (Or.inl ⟨hk, ?_⟩)⟩, hfeq⟩
                          have hlt3 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source
                            (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))
                          have hltEnd := String.Pos.Raw.lt_iff.mp hfbB.1
                          have hblkSelf := CoreSpec.blockStep_self hbstep
                          cases pos
                          exact ⟨hblk.1.1, hblk.2, by dsimp only; omega, hnotdoc.1, hnotdoc.2,
                            by dsimp only; omega, hblkSelf, pm, ps, hps, congrArg String.Pos.Raw.byteIdx hend,
                            hpm, hpsC⟩
                      · have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source pos
                        have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)
                        have hlt3 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source
                          (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))
                        have hltEnd := String.Pos.Raw.lt_iff.mp hfbB.1
                        exact Or.inr ⟨by omega, h2, hg, hfeq⟩
              · cases h
          · cases h
        · cases h
  · rename_i hge
    cases h
    exact ⟨CoreSpec.TriviaStep.done hge, fun _ _ _ hs => Or.inl hs⟩
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have _hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  · change stopPos.byteIdx - (String.Pos.Raw.next ctx.fileMap.source pos).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have _hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)
    have _hleEol := String.Pos.Raw.le_iff.mp (NoComments.Core.toEol_bounds ctx.fileMap.source stopPos
      (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)) (by assumption)).1
    change stopPos.byteIdx -
        (NoComments.Core.toEol ctx.fileMap.source stopPos
          (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have _hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)
    have _hlt3 := String.Pos.Raw.byteIdx_lt_byteIdx_next ctx.fileMap.source
      (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))
    have _hltEnd := String.Pos.Raw.lt_iff.mp (NoComments.Core.finishBlock_bounds ctx.fileMap.source stopPos 1
      (String.Pos.Raw.next ctx.fileMap.source
        (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
      endPos (by assumption)).1
    change stopPos.byteIdx - endPos.byteIdx < stopPos.byteIdx - pos.byteIdx
    omega

theorem scanTriviaGo_fails (fileMap : FileMap) (stopPos pos : String.Pos.Raw)
    (acc : NoComments.Core.CommentAcc) {msg : String}
    (h : NoComments.Core.scanTriviaGo fileMap stopPos pos acc = .error msg) :
    CoreSpec.TriviaFails fileMap stopPos pos (CoreSpec.stateOfAcc acc) := by
  unfold NoComments.Core.scanTriviaGo at h
  dsimp only at h
  split at h
  · rename_i hlt
    split at h
    · rename_i hws
      split at h
      · rename_i hnext
        exact CoreSpec.TriviaFails.wsStep hlt hws hnext
          (scanTriviaGo_fails fileMap stopPos (String.Pos.Raw.next fileMap.source pos) acc h)
      · rename_i hnotnext
        exact CoreSpec.TriviaFails.wsBoundary hlt hws hnotnext
    · rename_i hnotws
      have hnotwsF : (String.Pos.Raw.get fileMap.source pos).isWhitespace = false :=
        Bool.eq_false_iff.mpr hnotws
      split at h
      · rename_i hline
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hline
        split at h
        · rename_i hafter
          have heolB := NoComments.Core.toEol_bounds fileMap.source stopPos
            (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) hafter
          have hlineEnd := toEol_lineEnd fileMap.source stopPos
            (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) hafter
          have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source pos
          have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source pos)
          have hleEol := String.Pos.Raw.le_iff.mp heolB.1
          have hltEol : pos.byteIdx <
              (NoComments.Core.toEol fileMap.source stopPos
                (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx := by
            omega
          cases hrec : NoComments.Core.recordSpan fileMap "line" pos
              (NoComments.Core.toEol fileMap.source stopPos
                (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
              acc with
          | error e =>
            exact CoreSpec.TriviaFails.lineSpanConflict hlt hline.1.1 hline.1.2 hline.2 hafter
              hlineEnd (recordSpan_error_conflict hrec)
          | ok acc1 =>
            rw [hrec] at h
            rcases recordSpan_ok_props (by simp [CoreSpec.validCommentKind]) hrec with
              ⟨_, _, hnoc, hstate1⟩
            have hf := scanTriviaGo_fails fileMap stopPos
              (NoComments.Core.toEol fileMap.source stopPos
                (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
              acc1 h
            rw [hstate1] at hf
            exact CoreSpec.TriviaFails.lineStep hlt hline.1.1 hline.1.2 hline.2 hafter
              hlineEnd hltEol hnoc hf
        · rename_i hnotafter
          exact CoreSpec.TriviaFails.lineBoundary hlt hline.1.1 hline.1.2 hline.2 hnotafter
      · rename_i hnotline
        split at h
        · rename_i hblk
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hblk
          split at h
          · rename_i hafterOpen
            split at h
            · rename_i hdoc
              simp only [Bool.or_eq_true, beq_iff_eq] at hdoc
              exact CoreSpec.TriviaFails.docOpenerInTrivia hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen hdoc
            · rename_i hnotdoc
              simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnotdoc
              split at h
              · rename_i hbodyStart
                cases hfb : NoComments.Core.finishBlock fileMap.source stopPos 1
                    (String.Pos.Raw.next fileMap.source
                      (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))) with
                | error e =>
                  exact CoreSpec.TriviaFails.blockBodyFails hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen
                    hnotdoc.1 hnotdoc.2 hbodyStart (finishBlock_fails fileMap.source stopPos 1 _ hfb)
                | ok endPos =>
                  rw [hfb] at h
                  dsimp only at h
                  rcases finishBlock_step_and_closes fileMap.source stopPos 1 _ endPos (by omega) hfb with
                    ⟨hbstep, _⟩
                  cases hrec : NoComments.Core.recordSpan fileMap "block" pos endPos acc with
                  | error e =>
                    exact CoreSpec.TriviaFails.blockSpanConflict hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen
                      hnotdoc.1 hnotdoc.2 hbodyStart hbstep (recordSpan_error_conflict hrec)
                  | ok acc1 =>
                    rw [hrec] at h
                    dsimp only at h
                    rcases recordSpan_ok_props (by simp [CoreSpec.validCommentKind]) hrec with
                      ⟨_, _, hnoc, hstate1⟩
                    have hf := scanTriviaGo_fails fileMap stopPos endPos acc1 h
                    rw [hstate1] at hf
                    exact CoreSpec.TriviaFails.blockStep hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen
                      hnotdoc.1 hnotdoc.2 hbodyStart hbstep hnoc hf
              · rename_i hnotbody
                exact CoreSpec.TriviaFails.blockUnterminated2 hlt hblk.1.1 hblk.1.2 hblk.2 hafterOpen
                  hnotdoc.1 hnotdoc.2 hnotbody
          · rename_i hnotafterOpen
            exact CoreSpec.TriviaFails.blockUnterminated1 hlt hblk.1.1 hblk.1.2 hblk.2 hnotafterOpen
        · rename_i hnotblk
          have h1 : ¬ (String.Pos.Raw.get fileMap.source pos = '-' ∧
              String.Pos.Raw.next fileMap.source pos < stopPos ∧
              String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-') :=
            fun hc => hnotline (by simp [hc.1, hc.2.1, hc.2.2])
          have h2 : ¬ (String.Pos.Raw.get fileMap.source pos = '/' ∧
              String.Pos.Raw.next fileMap.source pos < stopPos ∧
              String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-') :=
            fun hc => hnotblk (by simp [hc.1, hc.2.1, hc.2.2])
          exact CoreSpec.TriviaFails.unexpectedChar hlt hnotwsF h1 h2
  · cases h
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have _hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  · change stopPos.byteIdx - (String.Pos.Raw.next fileMap.source pos).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have _hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source pos)
    have _hleEol := String.Pos.Raw.le_iff.mp (NoComments.Core.toEol_bounds fileMap.source stopPos
      (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) (by assumption)).1
    change stopPos.byteIdx -
        (NoComments.Core.toEol fileMap.source stopPos
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have _hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source pos)
    have _hlt3 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source
      (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))
    have _hltEnd := String.Pos.Raw.lt_iff.mp (NoComments.Core.finishBlock_bounds fileMap.source stopPos 1
      (String.Pos.Raw.next fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
      endPos (by assumption)).1
    change stopPos.byteIdx - endPos.byteIdx < stopPos.byteIdx - pos.byteIdx
    omega

theorem checkSlice_ok_props (ctx : Parser.ParserContextCore) (stx : Syntax)
    (startPos stopPos : String.Pos.Raw) (acc acc' : NoComments.Core.CommentAcc)
    (hstop : stopPos ≤ ctx.endPos)
    (h : NoComments.Core.checkSlice ctx.fileMap startPos stopPos acc = .ok acc') :
    CoreSpec.TriviaStep ctx.fileMap stopPos startPos (CoreSpec.stateOfAcc acc) (CoreSpec.stateOfAcc acc') ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (startPos.byteIdx ≤ sb ∧ eb ≤ stopPos.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx stx sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb)) := by
  simp only [NoComments.Core.checkSlice] at h
  split at h
  · exact scanTriviaGo_ok_props ctx stx stopPos startPos acc acc' hstop h
  · rename_i hge
    cases h
    exact ⟨CoreSpec.TriviaStep.done hge, fun _ _ _ hs => Or.inl hs⟩

theorem checkSlice_fails (fileMap : FileMap) (startPos stopPos : String.Pos.Raw)
    (acc : NoComments.Core.CommentAcc) {msg : String}
    (h : NoComments.Core.checkSlice fileMap startPos stopPos acc = .error msg) :
    CoreSpec.TriviaFails fileMap stopPos startPos (CoreSpec.stateOfAcc acc) := by
  simp only [NoComments.Core.checkSlice] at h
  split at h
  · exact scanTriviaGo_fails fileMap stopPos startPos acc h
  · cases h

theorem genuineSpan_docNode_mono {ctx : Parser.ParserContextCore} {arg root : Syntax}
    {sb eb : Nat} {c : NoComments.Core.Comment}
    (hmono : ∀ kind s e, CoreSpec.DocNodeIn arg kind s e → CoreSpec.DocNodeIn root kind s e)
    (hg : CoreSpec.GenuineCommentSpan ctx arg sb eb c) :
    CoreSpec.GenuineCommentSpan ctx root sb eb c := by
  rcases hg with ⟨h1, h2, h3, h4, h5, h6, h7 | h7 | ⟨hk, hdoc⟩⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, Or.inl h7⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, Or.inr (Or.inl h7)⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, Or.inr (Or.inr ⟨hk, hmono _ _ _ hdoc⟩)⟩

mutual

theorem walkSyntax_ok_props (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos stop : String.Pos.Raw) (acc acc' : NoComments.Core.CommentAcc)
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.walkSyntax ctx nextPos s pos acc = .ok (stop, acc')) :
    pos ≤ stop ∧ stop ≤ nextPos ∧
      CoreSpec.SyntaxStep ctx nextPos s pos (CoreSpec.stateOfAcc acc) stop (CoreSpec.stateOfAcc acc') ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (pos.byteIdx ≤ sb ∧ eb ≤ stop.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx s sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb)) := by
  cases s with
  | missing =>
    simp only [NoComments.Core.walkSyntax] at h
    cases h
    refine ⟨Std.le_refl _, hpos,
      CoreSpec.SyntaxStep.other (fun _ _ _ _ _ he => by cases he)
        (fun _ _ _ _ _ _ _ he => by cases he) (fun _ _ _ he => by cases he),
      fun _ _ _ hs => Or.inl hs⟩
  | atom info val =>
    cases info with
    | original leading start trail stop0 =>
      simp only [NoComments.Core.walkSyntax] at h
      rcases NoComments.Core.consumeRange_spec ctx.fileMap nextPos pos start stop0 stop _ acc acc' h with
        ⟨acc1, h1, h2, h3, rfl, hslice, htok⟩
      split at htok
      · cases htok
      · rename_i hok
        cases htok
        rcases checkSlice_ok_props ctx (.atom (.original leading start trail stop) val)
          pos start acc acc' (Std.le_trans (Std.le_trans h2 h3) hnext) hslice with ⟨htstep, hgen⟩
        refine ⟨String.Pos.Raw.le_iff.mpr
            (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
          h3, CoreSpec.SyntaxStep.atomOrig h1 h2 h3 htstep (checkToken_ok_spec hok), ?_⟩
        intro sb eb c hs
        rcases hgen sb eb c hs with hacc | ⟨hsb, heb, hg, hfeq⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨hsb, Nat.le_trans heb (String.Pos.Raw.le_iff.mp h2), hg, hfeq⟩
    | synthetic _ _ =>
      simp only [NoComments.Core.walkSyntax] at h
      cases h
      refine ⟨Std.le_refl _, hpos,
        CoreSpec.SyntaxStep.other (fun _ _ _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ _ he => by cases he) (fun _ _ _ he => by cases he),
        fun _ _ _ hs => Or.inl hs⟩
    | none =>
      simp only [NoComments.Core.walkSyntax] at h
      cases h
      refine ⟨Std.le_refl _, hpos,
        CoreSpec.SyntaxStep.other (fun _ _ _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ _ he => by cases he) (fun _ _ _ he => by cases he),
        fun _ _ _ hs => Or.inl hs⟩
  | ident info rawVal val pre =>
    cases info with
    | original leading start trail stop0 =>
      simp only [NoComments.Core.walkSyntax] at h
      rcases NoComments.Core.consumeRange_spec ctx.fileMap nextPos pos start stop0 stop _ acc acc' h with
        ⟨acc1, h1, h2, h3, rfl, hslice, htok⟩
      split at htok
      · cases htok
      · rename_i hok
        cases htok
        rcases checkSlice_ok_props ctx (.ident (.original leading start trail stop) rawVal val pre)
          pos start acc acc' (Std.le_trans (Std.le_trans h2 h3) hnext) hslice with ⟨htstep, hgen⟩
        refine ⟨String.Pos.Raw.le_iff.mpr
            (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
          h3, CoreSpec.SyntaxStep.identOrig h1 h2 h3 htstep (checkToken_ok_spec hok), ?_⟩
        intro sb eb c hs
        rcases hgen sb eb c hs with hacc | ⟨hsb, heb, hg, hfeq⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨hsb, Nat.le_trans heb (String.Pos.Raw.le_iff.mp h2), hg, hfeq⟩
    | synthetic _ _ =>
      simp only [NoComments.Core.walkSyntax] at h
      cases h
      refine ⟨Std.le_refl _, hpos,
        CoreSpec.SyntaxStep.other (fun _ _ _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ _ he => by cases he) (fun _ _ _ he => by cases he),
        fun _ _ _ hs => Or.inl hs⟩
    | none =>
      simp only [NoComments.Core.walkSyntax] at h
      cases h
      refine ⟨Std.le_refl _, hpos,
        CoreSpec.SyntaxStep.other (fun _ _ _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ _ he => by cases he) (fun _ _ _ he => by cases he),
        fun _ _ _ hs => Or.inl hs⟩
  | node info k args =>
    unfold NoComments.Core.walkSyntax at h
    by_cases hdoc : NoComments.Core.isDocCommentKind k = true
    · simp only [hdoc, ↓reduceIte] at h
      cases hhead : Syntax.getHeadInfo? (.node info k args) with
      | none => rw [hhead] at h; cases h
      | some hi =>
        cases hi with
        | synthetic _ _ => rw [hhead] at h; cases h
        | none => rw [hhead] at h; cases h
        | original l0 start t0 s0 =>
          cases htail : Syntax.getTailInfo? (.node info k args) with
          | none => rw [hhead, htail] at h; cases h
          | some ti =>
            cases ti with
            | synthetic _ _ => rw [hhead, htail] at h; cases h
            | none => rw [hhead, htail] at h; cases h
            | original l1 s1 t1 stop0 =>
              rw [hhead, htail] at h
              rcases NoComments.Core.consumeRange_spec ctx.fileMap nextPos pos start stop0 stop _ acc acc' h with
                ⟨acc1, h1, h2, h3, rfl, hslice, hrec⟩
              rcases checkSlice_ok_props ctx (.node info k args) pos start acc acc1
                (Std.le_trans (Std.le_trans h2 h3) hnext) hslice with ⟨htstep, hgen1⟩
              have hkMod : (if (k == ``Parser.Command.moduleDoc) = true then "moddoc" else "doc") = "doc" ∨
                  (if (k == ``Parser.Command.moduleDoc) = true then "moddoc" else "doc") = "moddoc" := by
                split <;> simp
              have hvk : validCommentKind (if (k == ``Parser.Command.moduleDoc) = true then "moddoc" else "doc") := by
                split <;> simp [CoreSpec.validCommentKind]
              rcases recordSpan_ok_props hvk hrec with ⟨hltSpan, hrecNew, hnoc, hstate'⟩
              refine ⟨String.Pos.Raw.le_iff.mpr
                  (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
                h3, ?_, ?_⟩
              · rw [hstate']
                exact CoreSpec.SyntaxStep.doc hdoc hhead htail h1 h2 h3 htstep rfl hnoc
              · intro sb eb c hs
                rcases hrecNew sb eb c hs with hacc1 | ⟨rfl, rfl, hk, hfp, hsl, hel, hfeq⟩
                · rcases hgen1 sb eb c hacc1 with hacc | ⟨hsb, heb, hg, hfeq⟩
                  · exact Or.inl hacc
                  · exact Or.inr ⟨hsb, Nat.le_trans heb (String.Pos.Raw.le_iff.mp h2), hg, hfeq⟩
                · refine Or.inr ⟨String.Pos.Raw.le_iff.mp h1, Nat.le_refl _,
                    ⟨hltSpan, Nat.le_trans (String.Pos.Raw.le_iff.mp h3) (String.Pos.Raw.le_iff.mp hnext),
                      ?_, hfp, hsl, hel, Or.inr (Or.inr ⟨?_, ?_⟩)⟩, hfeq⟩
                  · rw [hk]
                    exact hvk
                  · rw [hk]
                    exact hkMod
                  · exact CoreSpec.DocNodeIn.here hdoc hhead htail hk
    · have hdocF : NoComments.Core.isDocCommentKind k = false := Bool.eq_false_iff.mpr hdoc
      by_cases hch : k = choiceKind
      · have hchT : (k == choiceKind) = true := beq_iff_eq.mpr hch
        simp only [hdocF, hchT, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil => cases h
          | cons first alts =>
            simp only [bind, Except.bind] at h
            cases hfirst : NoComments.Core.walkSyntax ctx nextPos first pos acc with
            | error e => rw [hfirst] at h; cases h
            | ok res1 =>
              rcases res1 with ⟨stop1, acc1⟩
              rw [hfirst] at h
              dsimp only at h
              cases halts : NoComments.Core.checkAlts ctx nextPos pos stop1 alts acc1 with
              | error e => rw [halts] at h; cases h
              | ok acc2 =>
                rw [halts] at h
                dsimp only at h
                cases h
                rcases walkSyntax_ok_props ctx nextPos first pos stop acc acc1 hpos hnext hfirst with
                  ⟨hpos1, hstop1, hsfirst, hgf⟩
                rcases checkAlts_ok_props ctx nextPos pos stop alts acc1 acc' hpos hnext halts with
                  ⟨hsalts, hga⟩
                subst hch
                refine ⟨hpos1, hstop1, CoreSpec.SyntaxStep.choice hsfirst hsalts, ?_⟩
                intro sb eb c hs
                rcases hga sb eb c hs with hacc1 | ⟨alt, hal, hsb, heb, hg, hfeq⟩
                · rcases hgf sb eb c hacc1 with hacc | ⟨hsb, heb, hg, hfeq⟩
                  · exact Or.inl hacc
                  · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                      (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF List.mem_cons_self hd) hg, hfeq⟩
                · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                    (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF (List.mem_cons_of_mem _ hal) hd) hg, hfeq⟩
      · have hchB : (k == choiceKind) = false := beq_false_of_ne hch
        simp only [hdocF, hchB, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil =>
            dsimp only at h
            rcases walkList_ok_props ctx nextPos [] pos stop acc acc' hpos hnext h with
              ⟨hl1, hl2, hslist, hgl⟩
            refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
              (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
            intro sb eb c hs
            rcases hgl sb eb c hs with hacc | ⟨_, hmem, _, _, _⟩
            · exact Or.inl hacc
            · cases hmem
          | cons a1 l1 =>
            cases l1 with
            | cons a2 l2 =>
              dsimp only at h
              rcases walkList_ok_props ctx nextPos (a1 :: a2 :: l2) pos stop acc acc' hpos hnext h with
                ⟨hl1, hl2, hslist, hgl⟩
              refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
              intro sb eb c hs
              rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
              · exact Or.inl hacc
              · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                  (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
            | nil =>
              cases a1 with
              | atom infoA valA =>
                cases infoA with
                | original leading start trail stop0 =>
                  dsimp only at h
                  rcases NoComments.Core.consumeRange_spec ctx.fileMap nextPos pos start stop0 stop _ acc acc' h with
                    ⟨acc1, h1, h2, h3, rfl, hslice, htok⟩
                  split at htok
                  · cases htok
                  · rename_i hok
                    cases htok
                    rcases checkSlice_ok_props ctx
                      (.node info k (.mk [.atom (.original leading start trail stop) valA]))
                      pos start acc acc' (Std.le_trans (Std.le_trans h2 h3) hnext) hslice with
                      ⟨htstep, hgen⟩
                    refine ⟨String.Pos.Raw.le_iff.mpr
                        (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
                      h3, CoreSpec.SyntaxStep.singletonAtomNode hdocF hch rfl h1 h2 h3 htstep
                        (checkToken_ok_spec hok), ?_⟩
                    intro sb eb c hs
                    rcases hgen sb eb c hs with hacc | ⟨hsb, heb, hg, hfeq⟩
                    · exact Or.inl hacc
                    · exact Or.inr ⟨hsb, Nat.le_trans heb (String.Pos.Raw.le_iff.mp h2), hg, hfeq⟩
                | synthetic posA endPosA canonicalA =>
                  dsimp only at h
                  rcases walkList_ok_props ctx nextPos [.atom (.synthetic posA endPosA canonicalA) valA]
                      pos stop acc acc' hpos hnext h with
                    ⟨hl1, hl2, hslist, hgl⟩
                  refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                    (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
                  intro sb eb c hs
                  rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
                  · exact Or.inl hacc
                  · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                      (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
                | none =>
                  dsimp only at h
                  rcases walkList_ok_props ctx nextPos [.atom .none valA] pos stop acc acc' hpos hnext h with
                    ⟨hl1, hl2, hslist, hgl⟩
                  refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                    (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
                  intro sb eb c hs
                  rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
                  · exact Or.inl hacc
                  · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                      (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
              | ident infoI rawI valI preI =>
                dsimp only at h
                rcases walkList_ok_props ctx nextPos [.ident infoI rawI valI preI] pos stop acc acc' hpos hnext h with
                  ⟨hl1, hl2, hslist, hgl⟩
                refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
                intro sb eb c hs
                rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
                · exact Or.inl hacc
                · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                    (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
              | node infoN kN argsN =>
                dsimp only at h
                rcases walkList_ok_props ctx nextPos [.node infoN kN argsN] pos stop acc acc' hpos hnext h with
                  ⟨hl1, hl2, hslist, hgl⟩
                refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
                intro sb eb c hs
                rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
                · exact Or.inl hacc
                · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                    (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
              | missing =>
                dsimp only at h
                rcases walkList_ok_props ctx nextPos [.missing] pos stop acc acc' hpos hnext h with
                  ⟨hl1, hl2, hslist, hgl⟩
                refine ⟨hl1, hl2, CoreSpec.SyntaxStep.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he) hslist, ?_⟩
                intro sb eb c hs
                rcases hgl sb eb c hs with hacc | ⟨arg, ha, hsb, heb, hg, hfeq⟩
                · exact Or.inl hacc
                · exact Or.inr ⟨hsb, heb, genuineSpan_docNode_mono
                    (fun kind s e hd => CoreSpec.DocNodeIn.child hdocF ha hd) hg, hfeq⟩
termination_by (sizeOf s, 1)

theorem checkAlts_ok_props (ctx : Parser.ParserContextCore) (nextPos pos stop : String.Pos.Raw)
    (alts : List Syntax) (acc acc' : NoComments.Core.CommentAcc)
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.checkAlts ctx nextPos pos stop alts acc = .ok acc') :
    CoreSpec.AltsStep ctx nextPos pos stop alts (CoreSpec.stateOfAcc acc) (CoreSpec.stateOfAcc acc') ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          ∃ alt ∈ alts, pos.byteIdx ≤ sb ∧ eb ≤ stop.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx alt sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb) := by
  cases alts with
  | nil =>
    simp only [NoComments.Core.checkAlts] at h
    cases h
    exact ⟨CoreSpec.AltsStep.nil, fun _ _ _ hs => Or.inl hs⟩
  | cons alt rest =>
    simp only [NoComments.Core.checkAlts, bind, Except.bind] at h
    cases halt : NoComments.Core.walkSyntax ctx nextPos alt pos acc with
    | error e => rw [halt] at h; cases h
    | ok res =>
      rcases res with ⟨altStop, altAcc⟩
      rw [halt] at h
      by_cases heq : (altStop == stop) = true
      · simp only [heq, ↓reduceIte] at h
        have heq' : altStop = stop := beq_iff_eq.mp heq
        subst heq'
        rcases walkSyntax_ok_props ctx nextPos alt pos altStop acc altAcc hpos hnext halt with
          ⟨_, _, hs1, hg1⟩
        rcases checkAlts_ok_props ctx nextPos pos altStop rest altAcc acc' hpos hnext h with ⟨hs2, hg2⟩
        refine ⟨CoreSpec.AltsStep.cons hs1 hs2, ?_⟩
        intro sb eb c hs
        rcases hg2 sb eb c hs with haltAcc | ⟨a, ha, hsb, heb, hg, hfeq⟩
        · rcases hg1 sb eb c haltAcc with hacc | ⟨hsb, heb, hg, hfeq⟩
          · exact Or.inl hacc
          · exact Or.inr ⟨alt, List.mem_cons_self, hsb, heb, hg, hfeq⟩
        · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hsb, heb, hg, hfeq⟩
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
        cases h
termination_by (sizeOf alts, 0)

theorem walkList_ok_props (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (args : List Syntax) (pos stop : String.Pos.Raw) (acc acc' : NoComments.Core.CommentAcc)
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.walkList ctx nextPos args pos acc = .ok (stop, acc')) :
    pos ≤ stop ∧ stop ≤ nextPos ∧
      CoreSpec.ListStep ctx nextPos args pos (CoreSpec.stateOfAcc acc) stop (CoreSpec.stateOfAcc acc') ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          ∃ arg ∈ args, pos.byteIdx ≤ sb ∧ eb ≤ stop.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx arg sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb) := by
  cases args with
  | nil =>
    simp only [NoComments.Core.walkList] at h
    cases h
    exact ⟨Std.le_refl _, hpos, CoreSpec.ListStep.nil, fun _ _ _ hs => Or.inl hs⟩
  | cons arg rest =>
    simp only [NoComments.Core.walkList, bind, Except.bind] at h
    cases h1 : NoComments.Core.walkSyntax ctx nextPos arg pos acc with
    | error e => rw [h1] at h; cases h
    | ok res =>
      rcases res with ⟨mid, acc1⟩
      rw [h1] at h
      dsimp only at h
      rcases walkSyntax_ok_props ctx nextPos arg pos mid acc acc1 hpos hnext h1 with
        ⟨hpos1, hnext1, hs1, hg1⟩
      rcases walkList_ok_props ctx nextPos rest mid stop acc1 acc' hnext1 hnext h with
        ⟨hpos2, hnext2, hs2, hg2⟩
      refine ⟨String.Pos.Raw.le_iff.mpr
          (Nat.le_trans (String.Pos.Raw.le_iff.mp hpos1) (String.Pos.Raw.le_iff.mp hpos2)),
        hnext2, CoreSpec.ListStep.cons hs1 hs2, ?_⟩
      intro sb eb c hs
      rcases hg2 sb eb c hs with hacc1 | ⟨a, ha, hsb, heb, hg, hfeq⟩
      · rcases hg1 sb eb c hacc1 with hacc | ⟨hsb, heb, hg, hfeq⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨arg, List.mem_cons_self, hsb,
            Nat.le_trans heb (String.Pos.Raw.le_iff.mp hpos2), hg, hfeq⟩
      · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha,
          Nat.le_trans (String.Pos.Raw.le_iff.mp hpos1) hsb, heb, hg, hfeq⟩
termination_by (sizeOf args, 0)

theorem walkSyntax_fails (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos : String.Pos.Raw) (acc : NoComments.Core.CommentAcc) {msg : String}
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.walkSyntax ctx nextPos s pos acc = .error msg) :
    CoreSpec.SyntaxFails ctx nextPos s pos (CoreSpec.stateOfAcc acc) := by
  cases s with
  | missing => simp [NoComments.Core.walkSyntax] at h
  | atom info val =>
    cases info with
    | synthetic _ _ => simp [NoComments.Core.walkSyntax] at h
    | none => simp [NoComments.Core.walkSyntax] at h
    | original leading start trail stop0 =>
      simp only [NoComments.Core.walkSyntax, NoComments.Core.consumeToken, NoComments.Core.consumeRange] at h
      split at h
      · rename_i hrng
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrng
        cases hslice : NoComments.Core.checkSlice ctx.fileMap pos start acc with
        | error e =>
          exact CoreSpec.SyntaxFails.atomTrivia hrng.1.1 hrng.1.2 hrng.2
            (checkSlice_fails ctx.fileMap pos start acc hslice)
        | ok acc1 =>
          rw [hslice] at h
          dsimp only at h
          rcases checkSlice_ok_props ctx (.atom (.original leading start trail stop0) val)
            pos start acc acc1 (Std.le_trans (Std.le_trans hrng.1.2 hrng.2) hnext) hslice with
            ⟨htstep, _⟩
          cases htok : NoComments.Core.checkToken ctx (.atom (.original leading start trail stop0) val)
              (ctx.extract start stop0) (ctx.get stop0) start with
          | ok _ => rw [htok] at h; cases h
          | error e =>
            exact CoreSpec.SyntaxFails.atomToken hrng.1.1 hrng.1.2 hrng.2 htstep
              (checkToken_error_spec htok)
      · rename_i hnotrng
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnotrng
        exact CoreSpec.SyntaxFails.atomRange (fun ⟨h1, h2, h3⟩ => hnotrng ⟨h1, h2⟩ h3)
  | ident info rawVal val pre =>
    cases info with
    | synthetic _ _ => simp [NoComments.Core.walkSyntax] at h
    | none => simp [NoComments.Core.walkSyntax] at h
    | original leading start trail stop0 =>
      simp only [NoComments.Core.walkSyntax, NoComments.Core.consumeToken, NoComments.Core.consumeRange] at h
      split at h
      · rename_i hrng
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hrng
        cases hslice : NoComments.Core.checkSlice ctx.fileMap pos start acc with
        | error e =>
          exact CoreSpec.SyntaxFails.identTrivia hrng.1.1 hrng.1.2 hrng.2
            (checkSlice_fails ctx.fileMap pos start acc hslice)
        | ok acc1 =>
          rw [hslice] at h
          dsimp only at h
          rcases checkSlice_ok_props ctx (.ident (.original leading start trail stop0) rawVal val pre)
            pos start acc acc1 (Std.le_trans (Std.le_trans hrng.1.2 hrng.2) hnext) hslice with
            ⟨htstep, _⟩
          cases htok : NoComments.Core.checkToken ctx
              (.ident (.original leading start trail stop0) rawVal val pre)
              (ctx.extract start stop0) (ctx.get stop0) start with
          | ok _ => rw [htok] at h; cases h
          | error e =>
            exact CoreSpec.SyntaxFails.identToken hrng.1.1 hrng.1.2 hrng.2 htstep
              (checkToken_error_spec htok)
      · rename_i hnotrng
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnotrng
        exact CoreSpec.SyntaxFails.identRange (fun ⟨h1, h2, h3⟩ => hnotrng ⟨h1, h2⟩ h3)
  | node info k args =>
    unfold NoComments.Core.walkSyntax at h
    by_cases hdoc : NoComments.Core.isDocCommentKind k = true
    · simp only [hdoc, ↓reduceIte] at h
      cases hhead : Syntax.getHeadInfo? (.node info k args) with
      | none =>
        refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨hh, _⟩ => ?_
        rw [hhead] at hh; cases hh
      | some hi =>
        cases hi with
        | synthetic _ _ =>
          refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨hh, _⟩ => ?_
          rw [hhead] at hh; cases hh
        | none =>
          refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨hh, _⟩ => ?_
          rw [hhead] at hh; cases hh
        | original l0 start t0 s0 =>
          cases htail : Syntax.getTailInfo? (.node info k args) with
          | none =>
            refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨_, ht⟩ => ?_
            rw [htail] at ht; cases ht
          | some ti =>
            cases ti with
            | synthetic _ _ =>
              refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨_, ht⟩ => ?_
              rw [htail] at ht; cases ht
            | none =>
              refine CoreSpec.SyntaxFails.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨_, ht⟩ => ?_
              rw [htail] at ht; cases ht
            | original l1 s1 t1 stop0 =>
              rw [hhead, htail] at h
              simp only [NoComments.Core.consumeRange] at h
              split at h
              · rename_i hrng
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hrng
                cases hslice : NoComments.Core.checkSlice ctx.fileMap pos start acc with
                | error e =>
                  exact CoreSpec.SyntaxFails.docTrivia hdoc hhead htail hrng.1.1 hrng.1.2 hrng.2
                    (checkSlice_fails ctx.fileMap pos start acc hslice)
                | ok acc1 =>
                  rw [hslice] at h
                  dsimp only at h
                  rcases checkSlice_ok_props ctx (.node info k args) pos start acc acc1
                    (Std.le_trans (Std.le_trans hrng.1.2 hrng.2) hnext) hslice with ⟨htstep, _⟩
                  cases hrec : NoComments.Core.recordSpan ctx.fileMap
                      (if (k == ``Parser.Command.moduleDoc) = true then "moddoc" else "doc")
                      start stop0 acc1 with
                  | ok acc2 => rw [hrec] at h; cases h
                  | error e =>
                    exact CoreSpec.SyntaxFails.docSpanConflict hdoc hhead htail hrng.1.1 hrng.1.2 hrng.2
                      htstep rfl (recordSpan_error_conflict hrec)
              · rename_i hnotrng
                simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnotrng
                exact CoreSpec.SyntaxFails.docRange hdoc hhead htail
                  (fun ⟨h1, h2, h3⟩ => hnotrng ⟨h1, h2⟩ h3)
    · have hdocF : NoComments.Core.isDocCommentKind k = false := Bool.eq_false_iff.mpr hdoc
      by_cases hch : k = choiceKind
      · have hchT : (k == choiceKind) = true := beq_iff_eq.mpr hch
        simp only [hdocF, hchT, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil =>
            subst hch
            exact CoreSpec.SyntaxFails.emptyChoice
          | cons first alts =>
            simp only [bind, Except.bind] at h
            cases hfirst : NoComments.Core.walkSyntax ctx nextPos first pos acc with
            | error e =>
              subst hch
              exact CoreSpec.SyntaxFails.choiceFirst
                (walkSyntax_fails ctx nextPos first pos acc hpos hnext hfirst)
            | ok res1 =>
              rcases res1 with ⟨stop1, acc1⟩
              rw [hfirst] at h
              dsimp only at h
              rcases walkSyntax_ok_props ctx nextPos first pos stop1 acc acc1 hpos hnext hfirst with
                ⟨_, _, hsfirst, _⟩
              subst hch
              cases hca : NoComments.Core.checkAlts ctx nextPos pos stop1 alts acc1 with
              | ok acc2 => rw [hca] at h; cases h
              | error e =>
                exact CoreSpec.SyntaxFails.choiceAlts hsfirst
                  (checkAlts_fails ctx nextPos pos stop1 alts acc1 hpos hnext hca)
      · have hchB : (k == choiceKind) = false := beq_false_of_ne hch
        simp only [hdocF, hchB, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil =>
            exact CoreSpec.SyntaxFails.nodeList hdocF hch
              (fun _ _ _ _ _ he => by cases he)
              (walkList_fails ctx nextPos [] pos acc hpos hnext h)
          | cons a1 l1 =>
            cases l1 with
            | cons a2 l2 =>
              exact CoreSpec.SyntaxFails.nodeList hdocF hch
                (fun _ _ _ _ _ he => by cases he)
                (walkList_fails ctx nextPos (a1 :: a2 :: l2) pos acc hpos hnext h)
            | nil =>
              cases a1 with
              | atom infoA valA =>
                cases infoA with
                | synthetic posA endPosA canonicalA =>
                  exact CoreSpec.SyntaxFails.nodeList hdocF hch
                    (fun _ _ _ _ _ he => by cases he)
                    (walkList_fails ctx nextPos [.atom (.synthetic posA endPosA canonicalA) valA] pos acc hpos hnext h)
                | none =>
                  exact CoreSpec.SyntaxFails.nodeList hdocF hch
                    (fun _ _ _ _ _ he => by cases he)
                    (walkList_fails ctx nextPos [.atom .none valA] pos acc hpos hnext h)
                | original leading start trail stop0 =>
                  dsimp only at h
                  simp only [NoComments.Core.consumeToken, NoComments.Core.consumeRange] at h
                  split at h
                  · rename_i hrng
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrng
                    cases hslice : NoComments.Core.checkSlice ctx.fileMap pos start acc with
                    | error e =>
                      exact CoreSpec.SyntaxFails.singletonAtomTrivia hdocF hch rfl hrng.1.1 hrng.1.2
                        hrng.2 (checkSlice_fails ctx.fileMap pos start acc hslice)
                    | ok acc1 =>
                      rw [hslice] at h
                      dsimp only at h
                      rcases checkSlice_ok_props ctx
                        (.node info k (.mk [.atom (.original leading start trail stop0) valA]))
                        pos start acc acc1 (Std.le_trans (Std.le_trans hrng.1.2 hrng.2) hnext) hslice with
                        ⟨htstep, _⟩
                      cases htok : NoComments.Core.checkToken ctx
                          (.node info k #[.atom (.original leading start trail stop0) valA])
                          (ctx.extract start stop0) (ctx.get stop0) start with
                      | ok _ => rw [htok] at h; cases h
                      | error e =>
                        exact CoreSpec.SyntaxFails.singletonAtomToken hdocF hch rfl hrng.1.1
                          hrng.1.2 hrng.2 htstep (checkToken_error_spec htok)
                  · rename_i hnotrng
                    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hnotrng
                    exact CoreSpec.SyntaxFails.singletonAtomRange hdocF hch rfl
                      (fun ⟨h1, h2, h3⟩ => hnotrng ⟨h1, h2⟩ h3)
              | ident infoI rawI valI preI =>
                exact CoreSpec.SyntaxFails.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he)
                  (walkList_fails ctx nextPos [.ident infoI rawI valI preI] pos acc hpos hnext h)
              | node infoN kN argsN =>
                exact CoreSpec.SyntaxFails.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he)
                  (walkList_fails ctx nextPos [.node infoN kN argsN] pos acc hpos hnext h)
              | missing =>
                exact CoreSpec.SyntaxFails.nodeList hdocF hch
                  (fun _ _ _ _ _ he => by cases he)
                  (walkList_fails ctx nextPos [.missing] pos acc hpos hnext h)
termination_by (sizeOf s, 1)

theorem checkAlts_fails (ctx : Parser.ParserContextCore) (nextPos pos stop : String.Pos.Raw)
    (alts : List Syntax) (acc : NoComments.Core.CommentAcc) {msg : String}
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.checkAlts ctx nextPos pos stop alts acc = .error msg) :
    CoreSpec.AltsFails ctx nextPos pos stop alts (CoreSpec.stateOfAcc acc) := by
  cases alts with
  | nil => simp [NoComments.Core.checkAlts] at h
  | cons alt rest =>
    simp only [NoComments.Core.checkAlts, bind, Except.bind] at h
    cases halt : NoComments.Core.walkSyntax ctx nextPos alt pos acc with
    | error e =>
      exact CoreSpec.AltsFails.head
        (walkSyntax_fails ctx nextPos alt pos acc hpos hnext halt)
    | ok res =>
      rcases res with ⟨altStop, altAcc⟩
      rw [halt] at h
      rcases walkSyntax_ok_props ctx nextPos alt pos altStop acc altAcc hpos hnext halt with
        ⟨_, _, hs1, _⟩
      by_cases heq : (altStop == stop) = true
      · simp only [heq, ↓reduceIte] at h
        have heq' : altStop = stop := beq_iff_eq.mp heq
        subst heq'
        exact CoreSpec.AltsFails.tail hs1 (checkAlts_fails ctx nextPos pos altStop rest altAcc hpos hnext h)
      · exact CoreSpec.AltsFails.mismatch hs1 (fun hst => heq (beq_iff_eq.mpr hst))
termination_by (sizeOf alts, 0)

theorem walkList_fails (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (args : List Syntax) (pos : String.Pos.Raw) (acc : NoComments.Core.CommentAcc) {msg : String}
    (hpos : pos ≤ nextPos) (hnext : nextPos ≤ ctx.endPos)
    (h : NoComments.Core.walkList ctx nextPos args pos acc = .error msg) :
    CoreSpec.ListFails ctx nextPos args pos (CoreSpec.stateOfAcc acc) := by
  cases args with
  | nil => simp [NoComments.Core.walkList] at h
  | cons arg rest =>
    simp only [NoComments.Core.walkList, bind, Except.bind] at h
    cases h1 : NoComments.Core.walkSyntax ctx nextPos arg pos acc with
    | error e =>
      exact CoreSpec.ListFails.head
        (walkSyntax_fails ctx nextPos arg pos acc hpos hnext h1)
    | ok res =>
      rcases res with ⟨mid, acc1⟩
      rw [h1] at h
      dsimp only at h
      rcases walkSyntax_ok_props ctx nextPos arg pos mid acc acc1 hpos hnext h1 with
        ⟨_, hnext1, hs1, _⟩
      exact CoreSpec.ListFails.tail hs1 (walkList_fails ctx nextPos rest mid acc1 hnext1 hnext h)
termination_by (sizeOf args, 0)

end

theorem collectSyntax_ok_props (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw)
    (stx : Syntax) (acc acc' : NoComments.Core.CommentAcc)
    (h : NoComments.Core.collectSyntax ctx prevPos nextPos stx acc = .ok acc') :
    prevPos ≤ nextPos ∧ nextPos ≤ ctx.endPos ∧
      (∃ mid state1,
        CoreSpec.SyntaxStep ctx nextPos stx prevPos (CoreSpec.stateOfAcc acc) mid state1 ∧
        CoreSpec.TriviaStep ctx.fileMap nextPos mid state1 (CoreSpec.stateOfAcc acc')) ∧
      ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
        acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (prevPos.byteIdx ≤ sb ∧ eb ≤ nextPos.byteIdx ∧
            CoreSpec.GenuineCommentSpan ctx stx sb eb c ∧
            c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText ctx.fileMap sb eb)) := by
  simp only [NoComments.Core.collectSyntax] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    cases hw : NoComments.Core.walkSyntax ctx nextPos stx prevPos acc with
    | error e => rw [hw] at h; cases h
    | ok res =>
      rcases res with ⟨mid, acc1⟩
      rw [hw] at h
      rcases walkSyntax_ok_props ctx nextPos stx prevPos mid acc acc1 hok.1 hok.2 hw with
        ⟨hpos1, hnext1, hstx, hgw⟩
      rcases checkSlice_ok_props ctx stx mid nextPos acc1 acc' hok.2 h with ⟨htriv, hgs⟩
      refine ⟨hok.1, hok.2, ⟨mid, CoreSpec.stateOfAcc acc1, hstx, htriv⟩, ?_⟩
      intro sb eb c hs
      rcases hgs sb eb c hs with hacc1 | ⟨hsb, heb, hg, hfeq⟩
      · rcases hgw sb eb c hacc1 with hacc | ⟨hsb, heb, hg, hfeq⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨hsb, Nat.le_trans heb (String.Pos.Raw.le_iff.mp hnext1), hg, hfeq⟩
      · exact Or.inr ⟨Nat.le_trans (String.Pos.Raw.le_iff.mp hpos1) hsb, heb, hg, hfeq⟩
  · cases h

theorem collectSyntax_fails (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw)
    (stx : Syntax) (acc : NoComments.Core.CommentAcc) {msg : String}
    (h : NoComments.Core.collectSyntax ctx prevPos nextPos stx acc = .error msg) :
    ¬ (prevPos ≤ nextPos ∧ nextPos ≤ ctx.endPos) ∨
      (prevPos ≤ nextPos ∧ nextPos ≤ ctx.endPos ∧
        CoreSpec.SyntaxFails ctx nextPos stx prevPos (CoreSpec.stateOfAcc acc)) ∨
      (∃ mid state1, prevPos ≤ nextPos ∧ nextPos ≤ ctx.endPos ∧
        CoreSpec.SyntaxStep ctx nextPos stx prevPos (CoreSpec.stateOfAcc acc) mid state1 ∧
        CoreSpec.TriviaFails ctx.fileMap nextPos mid state1) := by
  simp only [NoComments.Core.collectSyntax] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    cases hw : NoComments.Core.walkSyntax ctx nextPos stx prevPos acc with
    | error e =>
      exact Or.inr (Or.inl ⟨hok.1, hok.2,
        walkSyntax_fails ctx nextPos stx prevPos acc hok.1 hok.2 hw⟩)
    | ok res =>
      rcases res with ⟨mid, acc1⟩
      rw [hw] at h
      rcases walkSyntax_ok_props ctx nextPos stx prevPos mid acc acc1 hok.1 hok.2 hw with
        ⟨_, _, hstx, _⟩
      exact Or.inr (Or.inr ⟨mid, CoreSpec.stateOfAcc acc1, hok.1, hok.2, hstx,
        checkSlice_fails ctx.fileMap mid nextPos acc1 h⟩)
  · rename_i hbad
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    exact Or.inl hbad

theorem collectRanges_genuine_new_spans (ranges : List NoComments.Core.CommandRange)
    (acc acc' : NoComments.Core.CommentAcc)
    (h : NoComments.Core.collectRanges ranges acc = .ok acc') :
    ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
      acc'.spans[sb]? = some (eb, c) →
      acc.spans[sb]? = some (eb, c) ∨
        ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
          CoreSpec.GenuineCommentSpan r.ctx r.stx sb eb c ∧
          c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText r.ctx.fileMap sb eb) := by
  induction ranges generalizing acc with
  | nil =>
    simp only [NoComments.Core.collectRanges] at h
    cases h
    exact fun _ _ _ hs => Or.inl hs
  | cons r rest ih =>
    simp only [NoComments.Core.collectRanges, bind, Except.bind] at h
    cases h1 : NoComments.Core.collectSyntax r.ctx r.prevPos r.nextPos r.stx acc with
    | error e => rw [h1] at h; cases h
    | ok acc1 =>
      rw [h1] at h
      rcases collectSyntax_ok_props r.ctx r.prevPos r.nextPos r.stx acc acc1 h1 with
        ⟨_, _, _, hgr⟩
      intro sb eb c hs
      rcases ih acc1 h sb eb c hs with hacc1 | ⟨r', hr', hsb, heb, hg, hfeq⟩
      · rcases hgr sb eb c hacc1 with hacc | ⟨hsb, heb, hg, hfeq⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨r, List.mem_cons_self, hsb, heb, hg, hfeq⟩
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hsb, heb, hg, hfeq⟩

theorem collectRanges_new_span_fingerprint (ranges : List NoComments.Core.CommandRange)
    (acc acc' : NoComments.Core.CommentAcc)
    (h : NoComments.Core.collectRanges ranges acc = .ok acc') :
    ∀ (sb eb : Nat) (c : NoComments.Core.Comment),
      acc'.spans[sb]? = some (eb, c) →
      acc.spans[sb]? = some (eb, c) ∨
        ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
          c.fingerprint = NoComments.Core.fingerprint (CoreSpec.commentText r.ctx.fileMap sb eb) := by
  intro sb eb c hs
  exact (collectRanges_genuine_new_spans ranges acc acc' h sb eb c hs).imp id
    fun ⟨r, hr, h1, h2, _, hfeq⟩ => ⟨r, hr, h1, h2, hfeq⟩

theorem collectRanges_rangesStep (ranges : List NoComments.Core.CommandRange)
    (acc acc' : NoComments.Core.CommentAcc)
    (h : NoComments.Core.collectRanges ranges acc = .ok acc') :
    CoreSpec.RangesStep ranges (CoreSpec.stateOfAcc acc) (CoreSpec.stateOfAcc acc') := by
  induction ranges generalizing acc with
  | nil =>
    simp only [NoComments.Core.collectRanges] at h
    cases h
    exact CoreSpec.RangesStep.nil
  | cons r rest ih =>
    simp only [NoComments.Core.collectRanges, bind, Except.bind] at h
    cases h1 : NoComments.Core.collectSyntax r.ctx r.prevPos r.nextPos r.stx acc with
    | error e => rw [h1] at h; cases h
    | ok acc1 =>
      rw [h1] at h
      rcases collectSyntax_ok_props r.ctx r.prevPos r.nextPos r.stx acc acc1 h1 with
        ⟨h1a, h1b, ⟨mid, state1, hstx, htriv⟩, _⟩
      exact CoreSpec.RangesStep.cons h1a h1b hstx htriv (ih acc1 h)

theorem collectRanges_error_spec (ranges : List NoComments.Core.CommandRange)
    (acc : NoComments.Core.CommentAcc) {msg : String}
    (h : NoComments.Core.collectRanges ranges acc = .error msg) :
    CoreSpec.CollectRefusal ranges acc := by
  induction ranges generalizing acc with
  | nil => simp [NoComments.Core.collectRanges] at h
  | cons r rest ih =>
    simp only [NoComments.Core.collectRanges, bind, Except.bind] at h
    cases h1 : NoComments.Core.collectSyntax r.ctx r.prevPos r.nextPos r.stx acc with
    | error e =>
      rcases collectSyntax_fails r.ctx r.prevPos r.nextPos r.stx acc h1 with
        hbad | ⟨h1a, h1b, hstx⟩ | ⟨mid, state1, h1a, h1b, hstx, htriv⟩
      · exact CoreSpec.CollectRefusalAt.badBounds hbad
      · exact CoreSpec.CollectRefusalAt.syntaxFails h1a h1b hstx
      · exact CoreSpec.CollectRefusalAt.trailingTriviaFails h1a h1b hstx htriv
    | ok acc1 =>
      rw [h1] at h
      rcases collectSyntax_ok_props r.ctx r.prevPos r.nextPos r.stx acc acc1 h1 with
        ⟨h1a, h1b, ⟨mid, state1, hstx, htriv⟩, _⟩
      exact CoreSpec.CollectRefusalAt.restFails h1a h1b hstx htriv (ih acc1 h)

theorem collectRanges_meets : collectRangesRecord.Meets NoComments.Core.collectRanges := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact NoComments.Core.collectRanges_preserves
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges start endPos acc acc' hcontig hok b hb1 hb2
    rcases NoComments.Core.collectRanges_coverage ranges start endPos acc acc'
      (contiguousFrom_toCore hcontig) hok b hb1 hb2 with ⟨r, hr, h1, h2, hcov⟩
    exact ⟨r, hr, h1, h2, byteAccounted_toSpec hcov⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact collectRanges_range_coverage
  rcases List.mem_cons.mp hp with rfl | hp
  · exact collectRanges_rangesStep
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc acc' hok sb eb c hs
    exact (collectRanges_genuine_new_spans ranges acc acc' hok sb eb c hs).imp id
      fun ⟨r, hr, h1, h2, hg, _⟩ => ⟨r, hr, h1, h2, hg⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨NoComments.Core.fingerprint, fingerprint_isFingerprint, fingerprint_nonconstant, ?_⟩
    exact collectRanges_new_span_fingerprint
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fun ranges acc msg herr => collectRanges_error_spec ranges acc herr
  exact nomatch hp

theorem collectRanges_refines :
    Refines collectRangesRecord (fun f => f) (· = NoComments.Core.collectRanges) :=
  fun _ hf _ => hf ▸ collectRanges_meets.2

theorem collectRanges_fulfilled : collectRangesRecord.Fulfilled NoComments.Core.collectRanges :=
  fulfils collectRanges_refines rfl

theorem pairwise_strict_of_le_nodup {α : Type} (l : List (Nat × α))
    (hle : l.Pairwise (fun a b => a.1 ≤ b.1)) (hnd : (l.map (·.1)).Nodup) :
    l.Pairwise (fun a b => a.1 < b.1) := by
  induction l with
  | nil => exact .nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨fun b hb => ?_, ih hle.2 hnd.2⟩
    have hleab := hle.1 b hb
    have hne : a.1 ≠ b.1 := fun heq =>
      hnd.1 (heq ▸ List.mem_map_of_mem hb)
    omega

theorem nodup_fst_of_pairwise_bne {α : Type} (l : List (Nat × α))
    (hpw : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (l.map (·.1)).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hpw.2⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, heq⟩
    have hne := hpw.1 b hb
    simp [heq] at hne

theorem sourceOrder_meets : sourceOrderRecord.Meets NoComments.Core.sourceOrder := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro acc
    let entries := acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))
    have hperm : entries.Perm acc.spans.toList :=
      List.mergeSort_perm acc.spans.toList (fun a b => decide (a.1 ≤ b.1))
    have hle : entries.Pairwise (fun a b => a.1 ≤ b.1) := by
      simpa only [decide_eq_true_eq] using
        List.pairwise_mergeSort
          (le := fun a b : Nat × (Nat × NoComments.Core.Comment) => decide (a.1 ≤ b.1))
          (fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
          (fun a b => by
            by_cases h : a.1 ≤ b.1 <;> simp [h] <;> omega)
          acc.spans.toList
    have hnd : (entries.map (·.1)).Nodup :=
      (hperm.map (·.1)).nodup_iff.mpr (nodup_fst_of_pairwise_bne _ acc.spans.distinct_keys_toList)
    refine ⟨entries, pairwise_strict_of_le_nodup entries hle hnd, ?_, rfl⟩
    intro sb eb c
    rw [hperm.mem_iff, Std.HashMap.mem_toList_iff_getElem?_eq_some]
  exact nomatch hp

theorem sourceOrder_refines :
    Refines sourceOrderRecord (fun f => f) (· = NoComments.Core.sourceOrder) :=
  fun _ hf _ => hf ▸ sourceOrder_meets.2

theorem sourceOrder_fulfilled : sourceOrderRecord.Fulfilled NoComments.Core.sourceOrder :=
  fulfils sourceOrder_refines rfl

theorem distinctCommentLines_meets :
    distinctCommentLinesRecord.Meets NoComments.Core.distinctCommentLines := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro comments
    rcases NoComments.Core.distinctCommentLines_exact comments with ⟨ls, hpw, hiff, hlen⟩
    have hnd : ls.Nodup := List.Pairwise.imp (fun {a b} hlt => by omega) hpw
    exact ⟨ls, hnd, hiff, hlen⟩
  exact nomatch hp

theorem distinctCommentLines_refines :
    Refines distinctCommentLinesRecord (fun f => f) (· = NoComments.Core.distinctCommentLines) :=
  fun _ hf _ => hf ▸ distinctCommentLines_meets.2

theorem distinctCommentLines_fulfilled :
    distinctCommentLinesRecord.Fulfilled NoComments.Core.distinctCommentLines :=
  fulfils distinctCommentLines_refines rfl

theorem firstOutOfOrder_some_witness :
    ∀ (l : List String) (b : String),
      NoComments.Core.firstOutOfOrder l = some b →
      ∃ pre a rest, l = pre ++ [a, b] ++ rest ∧ (pre ++ [a]).Pairwise (· ≤ ·) ∧ b < a
  | [], _, h => by simp [NoComments.Core.firstOutOfOrder] at h
  | [_], _, h => by simp [NoComments.Core.firstOutOfOrder] at h
  | x :: y :: zs, b, h => by
    unfold NoComments.Core.firstOutOfOrder at h
    split at h
    · rename_i hyx
      cases h
      exact ⟨[], x, zs, rfl, List.pairwise_singleton _ _, hyx⟩
    · rename_i hnot
      have hxy : x ≤ y := Std.not_lt.mp hnot
      rcases firstOutOfOrder_some_witness (y :: zs) b h with ⟨pre, a, rest, heq, hpw, hba⟩
      refine ⟨x :: pre, a, rest, by simp [heq], ?_, hba⟩
      cases pre with
      | nil =>
        simp only [List.nil_append] at heq
        cases heq
        exact List.pairwise_cons.mpr ⟨fun z hz => by
          change z ∈ [y] at hz; simp only [List.mem_singleton] at hz; subst hz; exact hxy,
          List.pairwise_singleton _ _⟩
      | cons p ps =>
        rw [List.append_assoc, List.cons_append] at heq
        cases heq
        rw [List.cons_append, List.pairwise_cons]
        have hpw' := List.pairwise_cons.mp hpw
        refine ⟨fun z hz => ?_, hpw⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact Std.le_trans hxy (hpw'.1 z hz)

theorem firstOutOfOrder_meets :
    firstOutOfOrderRecord.Meets NoComments.Core.firstOutOfOrder := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro l
    exact ⟨NoComments.Core.firstOutOfOrder_eq_none_iff l, firstOutOfOrder_some_witness l⟩
  exact nomatch hp

theorem firstOutOfOrder_refines :
    Refines firstOutOfOrderRecord (fun f => f) (· = NoComments.Core.firstOutOfOrder) :=
  fun _ hf _ => hf ▸ firstOutOfOrder_meets.2

theorem firstOutOfOrder_fulfilled :
    firstOutOfOrderRecord.Fulfilled NoComments.Core.firstOutOfOrder :=
  fulfils firstOutOfOrder_refines rfl

theorem sortFingerprints_meets :
    sortFingerprintsRecord.Meets NoComments.Core.sortFingerprints := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fun xs a => NoComments.Core.sortFingerprints_count xs a
  exact nomatch hp

theorem sortFingerprints_refines :
    Refines sortFingerprintsRecord (fun f => f) (· = NoComments.Core.sortFingerprints) :=
  fun _ hf _ => hf ▸ sortFingerprints_meets.2

theorem sortFingerprints_fulfilled :
    sortFingerprintsRecord.Fulfilled NoComments.Core.sortFingerprints :=
  fulfils sortFingerprints_refines rfl

theorem missingFrom_meets : missingFromRecord.Meets NoComments.Core.missingFrom := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact fun xs ys a => NoComments.Core.missingFrom_count xs ys a
  exact nomatch hp

theorem missingFrom_refines :
    Refines missingFromRecord (fun f => f) (· = NoComments.Core.missingFrom) :=
  fun _ hf _ => hf ▸ missingFrom_meets.2

theorem missingFrom_fulfilled : missingFromRecord.Fulfilled NoComments.Core.missingFrom :=
  fulfils missingFrom_refines rfl

end NoCommentsSpecification.Refinement.Core
