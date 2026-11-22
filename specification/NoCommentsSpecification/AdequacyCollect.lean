module

public import LeanIntent.Degenerate
public import LeanIntent.TrivialWitnesses
public import LeanIntent.Progress
public import Std.Data.HashMap.Lemmas
public import NoCommentsSpecification.AdequacyCore
import all Init.Prelude

@[expose] public section

namespace NoCommentsSpecification.AdequacyCollect

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreSpec
open NoCommentsSpecification.CoreRecords
open NoCommentsSpecification.AdequacyCore

def updateAcc (fp : FingerprintFn) (acc : Core.CommentAcc) (fileMap : FileMap) (kind : String)
    (startPos stopPos : String.Pos.Raw) : Core.CommentAcc :=
  match acc.spans[startPos.byteIdx]? with
  | some _ => acc
  | none =>
    let lastPos := String.Pos.Raw.prev fileMap.source stopPos
    let comment : Core.Comment :=
      { kind := kind
        startLine := (fileMap.toPosition startPos).line
        endLine := (fileMap.toPosition lastPos).line
        fingerprint := fp (commentText fileMap startPos.byteIdx stopPos.byteIdx) }
    { spans := acc.spans.insert startPos.byteIdx (stopPos.byteIdx, comment) }

theorem stateOfAcc_updateAcc {fp : FingerprintFn} {acc : Core.CommentAcc} {fileMap : FileMap}
    {kind : String} {startPos stopPos : String.Pos.Raw}
    (hnc : ¬ SpanConflict (stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx) :
    stateOfAcc (updateAcc fp acc fileMap kind startPos stopPos) =
      insertSpan (stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx := by
  funext k
  simp only [stateOfAcc, insertSpan, updateAcc]
  cases hcur : acc.spans[startPos.byteIdx]? with
  | none =>
    rw [Std.HashMap.getElem?_insert]
    by_cases hk : k = startPos.byteIdx
    · subst hk
      simp
    · have h1 : (startPos.byteIdx == k) = false := Bool.eq_false_iff.mpr (by simpa [beq_iff_eq] using Ne.symm hk)
      have h2 : (k == startPos.byteIdx) = false := Bool.eq_false_iff.mpr (by simpa [beq_iff_eq] using hk)
      simp [h1, h2]
  | some p =>
    rcases p with ⟨prevEb, prevC⟩
    have hconf : prevEb = stopPos.byteIdx ∧ prevC.kind = kind := by
      refine Classical.byContradiction fun hbad => ?_
      apply hnc
      right
      refine ⟨prevEb, prevC.kind, ?_, ?_⟩
      · simp [stateOfAcc, hcur]
      · by_cases he : prevEb = stopPos.byteIdx
        · exact .inr (fun hk => hbad ⟨he, hk⟩)
        · exact .inl he
    rcases hconf with ⟨rfl, rfl⟩
    by_cases hk : k = startPos.byteIdx
    · subst hk
      simp [hcur]
    · have h2 : (k == startPos.byteIdx) = false := Bool.eq_false_iff.mpr (by simpa [beq_iff_eq] using hk)
      simp [h2]

theorem updateAcc_preserves {fp : FingerprintFn} {acc : Core.CommentAcc} {fileMap : FileMap}
    {kind : String} {startPos stopPos : String.Pos.Raw} :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) →
      (updateAcc fp acc fileMap kind startPos stopPos).spans[sb]? = some (eb, c) := by
  intro sb eb c h
  dsimp [updateAcc]
  cases hcur : acc.spans[startPos.byteIdx]? with
  | some _ => exact h
  | none =>
    simp only [Std.HashMap.getElem?_insert]
    split <;> rename_i heq
    · have hsb : startPos.byteIdx = sb := by simpa using heq
      subst hsb
      rw [hcur] at h
      contradiction
    · exact h

theorem updateAcc_new_span {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {acc : Core.CommentAcc} {fileMap : FileMap} {kind : String}
    {startPos stopPos : String.Pos.Raw} :
    ∀ (sb eb : Nat) (c : Core.Comment),
      (updateAcc fp acc fileMap kind startPos stopPos).spans[sb]? = some (eb, c) →
      acc.spans[sb]? = some (eb, c) ∨
        (sb = startPos.byteIdx ∧ eb = stopPos.byteIdx ∧ c.kind = kind ∧
          IsFingerprint c.fingerprint ∧
          c.startLine = (fileMap.toPosition startPos).line ∧
          c.endLine = (fileMap.toPosition (String.Pos.Raw.prev fileMap.source stopPos)).line ∧
          c.fingerprint = fp (commentText fileMap sb eb)) := by
  intro sb eb c h
  dsimp [updateAcc] at h
  cases hcur : acc.spans[startPos.byteIdx]? with
  | some _ =>
    rw [hcur] at h
    exact .inl h
  | none =>
    rw [hcur] at h
    simp only [Std.HashMap.getElem?_insert] at h
    split at h <;> rename_i heq
    · have hsb : startPos.byteIdx = sb := by simpa using heq
      cases h
      subst hsb
      exact .inr ⟨rfl, rfl, rfl, hfp _, rfl, rfl, rfl⟩
    · exact .inl h

theorem lineEnd_total (str : String) (stopPos p : String.Pos.Raw) :
    ∃ eol, LineEnd str stopPos p eol := by
  by_cases hlt : p < stopPos
  · by_cases hnl : String.Pos.Raw.get str p = '\n'
    · exact ⟨p, .nl hlt hnl⟩
    · have _hdec : stopPos.byteIdx - (String.Pos.Raw.next str p).byteIdx < stopPos.byteIdx - p.byteIdx := by
        have h1 := String.Pos.Raw.lt_iff.mp hlt
        have h2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str p)
        omega
      obtain ⟨eol, heol⟩ := lineEnd_total str stopPos (String.Pos.Raw.next str p)
      exact ⟨eol, .step hlt hnl heol⟩
  · exact ⟨stopPos, .done hlt⟩
termination_by stopPos.byteIdx - p.byteIdx

theorem lineEnd_det {str : String} {stopPos p e1 e2 : String.Pos.Raw}
    (h1 : LineEnd str stopPos p e1) (h2 : LineEnd str stopPos p e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | done hnot =>
    cases h2 with
    | done _ => rfl
    | nl h _ => exact absurd h hnot
    | step h _ _ => exact absurd h hnot
  | nl hlt hnl =>
    cases h2 with
    | done h => exact absurd hlt h
    | nl _ _ => rfl
    | step _ hne _ => exact absurd hnl hne
  | step hlt hne _ ih =>
    cases h2 with
    | done h => exact absurd hlt h
    | nl _ hnl => exact absurd hnl hne
    | step _ _ hrest => exact ih hrest

theorem blockStep_ends_slash_minus {str : String} {stopPos : String.Pos.Raw} {n : Nat}
    {pos endPos : String.Pos.Raw} (h : BlockStep str stopPos n pos endPos) :
    ∃ pm ps : String.Pos.Raw,
      ps = String.Pos.Raw.next str pm ∧
      endPos.byteIdx = (String.Pos.Raw.next str ps).byteIdx ∧
      String.Pos.Raw.get str pm = '-' ∧
      String.Pos.Raw.get str ps = '/' := by
  induction h with
  | @closeTop _ pos' _ _ hm _ hs _ => exact ⟨pos', String.Pos.Raw.next str pos', rfl, rfl, hm, hs⟩
  | closeNested _ _ _ _ _ _ _ _ ih => exact ih
  | openNested _ _ _ _ _ _ _ ih => exact ih
  | other _ _ _ _ _ ih => exact ih

theorem blockStep_total (str : String) (stopPos : String.Pos.Raw) (n : Nat) (pos : String.Pos.Raw)
    (hn : n ≥ 1) :
    (∃ endPos, BlockStep str stopPos n pos endPos) ∨ BlockFails str stopPos n pos := by
  by_cases hlt : pos < stopPos
  · let next := String.Pos.Raw.next str pos
    by_cases hclose : String.Pos.Raw.get str pos = '-' ∧ next < stopPos ∧ String.Pos.Raw.get str next = '/'
    · rcases hclose with ⟨h1, h2, h3⟩
      let after := String.Pos.Raw.next str next
      by_cases ha : after ≤ stopPos
      · by_cases hn1 : n = 1
        · exact .inl ⟨after, .closeTop hn1 hlt h1 h2 h3 ha⟩
        · have hdec : stopPos.byteIdx - after.byteIdx < stopPos.byteIdx - pos.byteIdx := by
            have hx1 := String.Pos.Raw.lt_iff.mp hlt
            have hx2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str pos)
            have hx3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str next)
            dsimp only [next, after] at hx2 hx3 ⊢
            omega
          have hn' : n - 1 ≥ 1 := by omega
          rcases blockStep_total str stopPos (n - 1) after hn' with ⟨endPos, hb⟩ | hf
          · exact .inl ⟨endPos, .closeNested hn1 hn hlt h1 h2 h3 ha hb⟩
          · exact .inr (.closeNested hn1 hlt h1 h2 h3 ha hf)
      · exact .inr (.closeBoundary hlt h1 h2 h3 ha)
    · by_cases hopen : String.Pos.Raw.get str pos = '/' ∧ next < stopPos ∧ String.Pos.Raw.get str next = '-'
      · rcases hopen with ⟨h1, h2, h3⟩
        let after := String.Pos.Raw.next str next
        by_cases ha : after ≤ stopPos
        · have hdec : stopPos.byteIdx - after.byteIdx < stopPos.byteIdx - pos.byteIdx := by
            have hx1 := String.Pos.Raw.lt_iff.mp hlt
            have hx2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str pos)
            have hx3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str next)
            dsimp only [next, after] at hx2 hx3 ⊢
            omega
          rcases blockStep_total str stopPos (n + 1) after (by omega) with ⟨endPos, hb⟩ | hf
          · exact .inl ⟨endPos, .openNested hn hlt h1 h2 h3 ha hb⟩
          · exact .inr (.openNested hlt h1 h2 h3 ha hf)
        · exact .inr (.openBoundary hlt h1 h2 h3 ha)
      · have hdec : stopPos.byteIdx - next.byteIdx < stopPos.byteIdx - pos.byteIdx := by
          have hx1 := String.Pos.Raw.lt_iff.mp hlt
          have hx2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next str pos)
          dsimp only [next]
          omega
        rcases blockStep_total str stopPos n next hn with ⟨endPos, hb⟩ | hf
        · exact .inl ⟨endPos, .other hn hlt hclose hopen hb⟩
        · exact .inr (.other hlt hclose hopen hf)
  · exact .inr (.atEof hlt)
termination_by stopPos.byteIdx - pos.byteIdx

theorem blockStep_det {str : String} {stopPos : String.Pos.Raw} {n : Nat} {pos e1 e2 : String.Pos.Raw}
    (h1 : BlockStep str stopPos n pos e1) (h2 : BlockStep str stopPos n pos e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | closeTop hn1 _ hm _ hs _ =>
    cases h2 with
    | closeTop _ _ _ _ _ _ => rfl
    | closeNested hne _ _ _ _ _ _ _ => exact absurd hn1 hne
    | openNested _ _ ho _ _ _ _ => simp_all
    | other _ _ hc _ _ => exact absurd ⟨hm, ‹_›, hs⟩ hc
  | closeNested hne _ _ hm _ hs _ _ ih =>
    cases h2 with
    | closeTop hn1 _ _ _ _ _ => exact absurd hn1 hne
    | closeNested _ _ _ _ _ _ _ hr => exact ih hr
    | openNested _ _ ho _ _ _ _ => simp_all
    | other _ _ hc _ _ => exact absurd ⟨hm, ‹_›, hs⟩ hc
  | openNested _ _ ho _ hm _ _ ih =>
    cases h2 with
    | closeTop _ _ h _ _ _ => simp_all
    | closeNested _ _ _ h _ _ _ _ => simp_all
    | openNested _ _ _ _ _ _ hr => exact ih hr
    | other _ _ _ hop _ => exact absurd ⟨ho, ‹_›, hm⟩ hop
  | other _ _ hc hop _ ih =>
    cases h2 with
    | closeTop _ _ hm _ hs _ => exact absurd ⟨hm, ‹_›, hs⟩ hc
    | closeNested _ _ _ hm _ hs _ _ => exact absurd ⟨hm, ‹_›, hs⟩ hc
    | openNested _ _ ho _ hm _ _ => exact absurd ⟨ho, ‹_›, hm⟩ hop
    | other _ _ _ _ hr => exact ih hr

inductive TriviaAcc (fp : FingerprintFn) (fileMap : FileMap) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → Core.CommentAcc → Core.CommentAcc → Prop where
  | done {pos acc} : ¬ pos < stopPos → TriviaAcc fp fileMap stopPos pos acc acc
  | ws {pos acc acc'} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = true →
      String.Pos.Raw.next fileMap.source pos ≤ stopPos →
      TriviaAcc fp fileMap stopPos (String.Pos.Raw.next fileMap.source pos) acc acc' →
      TriviaAcc fp fileMap stopPos pos acc acc'
  | line {pos eol acc acc'} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      LineEnd fileMap.source stopPos
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) eol →
      ¬ SpanConflict (stateOfAcc acc) "line" pos.byteIdx eol.byteIdx →
      TriviaAcc fp fileMap stopPos eol (updateAcc fp acc fileMap "line" pos eol) acc' →
      TriviaAcc fp fileMap stopPos pos acc acc'
  | block {pos endPos acc acc'} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '/' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) < stopPos →
      String.Pos.Raw.get fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≠ '-' →
      String.Pos.Raw.get fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≠ '!' →
      String.Pos.Raw.next fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≤ stopPos →
      BlockStep fileMap.source stopPos 1
        (String.Pos.Raw.next fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
        endPos →
      ¬ SpanConflict (stateOfAcc acc) "block" pos.byteIdx endPos.byteIdx →
      TriviaAcc fp fileMap stopPos endPos (updateAcc fp acc fileMap "block" pos endPos) acc' →
      TriviaAcc fp fileMap stopPos pos acc acc'

mutual

inductive SyntaxAcc (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    Syntax → String.Pos.Raw → Core.CommentAcc → String.Pos.Raw → Core.CommentAcc → Prop where
  | atomOrig {l start t stop val pos acc acc1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaAcc fp ctx.fileMap start pos acc acc1 →
      TokenSafe ctx (Syntax.atom (.original l start t stop) val)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxAcc fp ctx nextPos (Syntax.atom (.original l start t stop) val) pos acc stop acc1
  | identOrig {l start t stop rawVal val pre pos acc acc1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaAcc fp ctx.fileMap start pos acc acc1 →
      TokenSafe ctx (Syntax.ident (.original l start t stop) rawVal val pre)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxAcc fp ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos acc stop acc1
  | doc {info k args l1 start t1 s1 l2 s2 t2 stop pos acc acc1 kind} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaAcc fp ctx.fileMap start pos acc acc1 →
      kind = (if k == ``Parser.Command.moduleDoc then "moddoc" else "doc") →
      ¬ SpanConflict (stateOfAcc acc1) kind start.byteIdx stop.byteIdx →
      SyntaxAcc fp ctx nextPos (Syntax.node info k args) pos acc stop
        (updateAcc fp acc1 ctx.fileMap kind start stop)
  | choice {info first alts pos acc stop acc1 acc2} :
      SyntaxAcc fp ctx nextPos first pos acc stop acc1 →
      AltsAcc fp ctx nextPos pos stop alts acc1 acc2 →
      SyntaxAcc fp ctx nextPos (Syntax.node info choiceKind ⟨first :: alts⟩) pos acc stop acc2
  | singletonAtomNode {info k atomInfo val l start t stop pos acc acc1} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaAcc fp ctx.fileMap start pos acc acc1 →
      TokenSafe ctx (Syntax.node info k #[.atom atomInfo val])
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxAcc fp ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos acc stop acc1
  | nodeList {info k args pos acc stop acc'} :
      docKind k = false →
      k ≠ choiceKind →
      (∀ l start t stop val, args ≠ #[.atom (.original l start t stop) val]) →
      ListAcc fp ctx nextPos args.toList pos acc stop acc' →
      SyntaxAcc fp ctx nextPos (Syntax.node info k args) pos acc stop acc'
  | other {s pos acc} :
      (∀ l start t stop val, s ≠ .atom (.original l start t stop) val) →
      (∀ l start t stop rawVal val pre, s ≠ .ident (.original l start t stop) rawVal val pre) →
      (∀ info k args, s ≠ .node info k args) →
      SyntaxAcc fp ctx nextPos s pos acc pos acc

inductive AltsAcc (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → List Syntax → Core.CommentAcc → Core.CommentAcc → Prop where
  | nil {pos stop acc} : AltsAcc fp ctx nextPos pos stop [] acc acc
  | cons {pos stop alt rest acc acc1 acc2} :
      SyntaxAcc fp ctx nextPos alt pos acc stop acc1 →
      AltsAcc fp ctx nextPos pos stop rest acc1 acc2 →
      AltsAcc fp ctx nextPos pos stop (alt :: rest) acc acc2

inductive ListAcc (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    List Syntax → String.Pos.Raw → Core.CommentAcc → String.Pos.Raw → Core.CommentAcc → Prop where
  | nil {pos acc} : ListAcc fp ctx nextPos [] pos acc pos acc
  | cons {arg rest pos acc mid acc1 stop acc2} :
      SyntaxAcc fp ctx nextPos arg pos acc mid acc1 →
      ListAcc fp ctx nextPos rest mid acc1 stop acc2 →
      ListAcc fp ctx nextPos (arg :: rest) pos acc stop acc2

end

inductive RangesAccWith (fp : FingerprintFn) : List Core.CommandRange → Core.CommentAcc → Core.CommentAcc → Prop where
  | nil {acc} : RangesAccWith fp [] acc acc
  | cons {r rest acc mid acc1 acc2 acc'} :
      r.prevPos ≤ r.nextPos →
      r.nextPos ≤ r.ctx.endPos →
      SyntaxAcc fp r.ctx r.nextPos r.stx r.prevPos acc mid acc1 →
      TriviaAcc fp r.ctx.fileMap r.nextPos mid acc1 acc2 →
      RangesAccWith fp rest acc2 acc' →
      RangesAccWith fp (r :: rest) acc acc'

abbrev RangesAcc := RangesAccWith fpModel

theorem triviaAcc_step {fp : FingerprintFn} {fileMap : FileMap} {stopPos pos : String.Pos.Raw}
    {acc acc' : Core.CommentAcc} (h : TriviaAcc fp fileMap stopPos pos acc acc') :
    TriviaStep fileMap stopPos pos (stateOfAcc acc) (stateOfAcc acc') := by
  induction h with
  | done hnot => exact .done hnot
  | ws hlt hws hle _ ih => exact .ws hlt hws hle ih
  | line hlt hm hnxt hm2 ha hle hnc _ ih =>
    rw [stateOfAcc_updateAcc hnc] at ih
    exact .line hlt hm hnxt hm2 ha hle hnc ih
  | block hlt hs hnxt hm haop h1 h2 hbs hb hnc _ ih =>
    rw [stateOfAcc_updateAcc hnc] at ih
    exact .block hlt hs hnxt hm haop h1 h2 hbs hb hnc ih

theorem syntaxAcc_step {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw} :
    ∀ {s pos acc stop acc'},
      SyntaxAcc fp ctx nextPos s pos acc stop acc' →
      SyntaxStep ctx nextPos s pos (stateOfAcc acc) stop (stateOfAcc acc')
  | _, _, _, _, _, .atomOrig h1 h2 h3 ht hts => .atomOrig h1 h2 h3 (triviaAcc_step ht) hts
  | _, _, _, _, _, .identOrig h1 h2 h3 ht hts => .identOrig h1 h2 h3 (triviaAcc_step ht) hts
  | _, _, _, _, _, .doc h1 h2 h3 h4 h5 h6 ht hk hnc => by
    have hs := SyntaxStep.doc h1 h2 h3 h4 h5 h6 (triviaAcc_step ht) hk hnc
    rwa [stateOfAcc_updateAcc hnc]
  | _, _, _, _, _, .choice h1 h2 => .choice (syntaxAcc_step h1) (altsAcc_step h2)
  | _, _, _, _, _, .singletonAtomNode h1 h2 h3 h4 h5 h6 ht hts =>
    .singletonAtomNode h1 h2 h3 h4 h5 h6 (triviaAcc_step ht) hts
  | _, _, _, _, _, .nodeList h1 h2 h3 hl => .nodeList h1 h2 h3 (listAcc_step hl)
  | _, _, _, _, _, .other h1 h2 h3 => .other h1 h2 h3
where
  altsAcc_step {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos pos stop : String.Pos.Raw} :
      ∀ {alts acc acc'},
        AltsAcc fp ctx nextPos pos stop alts acc acc' →
        AltsStep ctx nextPos pos stop alts (stateOfAcc acc) (stateOfAcc acc')
    | [], _, _, .nil => .nil
    | _ :: _, _, _, .cons h1 h2 => .cons (syntaxAcc_step h1) (altsAcc_step h2)
  listAcc_step {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw} :
      ∀ {args pos acc stop acc'},
        ListAcc fp ctx nextPos args pos acc stop acc' →
        ListStep ctx nextPos args pos (stateOfAcc acc) stop (stateOfAcc acc')
    | [], _, _, _, _, .nil => .nil
    | _ :: _, _, _, _, _, .cons h1 h2 => .cons (syntaxAcc_step h1) (listAcc_step h2)

theorem rangesAcc_step {fp : FingerprintFn} {ranges : List Core.CommandRange}
    {acc acc' : Core.CommentAcc} (h : RangesAccWith fp ranges acc acc') :
    RangesStep ranges (stateOfAcc acc) (stateOfAcc acc') := by
  induction h with
  | nil => exact .nil
  | cons h1 h2 hsa hta _ ih =>
    exact .cons h1 h2 (syntaxAcc_step hsa) (triviaAcc_step hta) ih

theorem triviaAcc_total (fp : FingerprintFn) (fileMap : FileMap) (stopPos pos : String.Pos.Raw)
    (acc : Core.CommentAcc) :
    (∃ acc', TriviaAcc fp fileMap stopPos pos acc acc') ∨
      TriviaFails fileMap stopPos pos (stateOfAcc acc) := by
  by_cases hlt : pos < stopPos
  · let c := String.Pos.Raw.get fileMap.source pos
    let next := String.Pos.Raw.next fileMap.source pos
    by_cases hws : c.isWhitespace = true
    · by_cases hn : next ≤ stopPos
      · have hdec : stopPos.byteIdx - next.byteIdx < stopPos.byteIdx - pos.byteIdx := by
          have hx1 := String.Pos.Raw.lt_iff.mp hlt
          have hx2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source pos)
          dsimp only [next]
          omega
        rcases triviaAcc_total fp fileMap stopPos next acc with ⟨acc', hta⟩ | htf
        · exact .inl ⟨acc', .ws hlt hws hn hta⟩
        · exact .inr (.wsStep hlt hws hn htf)
      · exact .inr (.wsBoundary hlt hws hn)
    · have hwsf : c.isWhitespace = false := Bool.eq_false_iff.mpr hws
      by_cases hline : c = '-' ∧ next < stopPos ∧ String.Pos.Raw.get fileMap.source next = '-'
      · rcases hline with ⟨hc1, hnxt, hc2⟩
        let after := String.Pos.Raw.next fileMap.source next
        by_cases ha : after ≤ stopPos
        · obtain ⟨eol, heol⟩ := lineEnd_total fileMap.source stopPos after
          by_cases hconf : SpanConflict (stateOfAcc acc) "line" pos.byteIdx eol.byteIdx
          · exact .inr (.lineSpanConflict hlt hc1 hnxt hc2 ha heol hconf)
          · have hpos_lt_eol : pos < eol := by
              have h1 := lineEnd_bounds ha heol |>.1
              have h2 := String.Pos.Raw.lt_next fileMap.source pos
              have h3 := String.Pos.Raw.lt_next fileMap.source next
              have hx1 := String.Pos.Raw.le_iff.mp h1
              have hx2 := String.Pos.Raw.lt_iff.mp h2
              have hx3 := String.Pos.Raw.lt_iff.mp h3
              dsimp only [next, after] at hx1 hx2 hx3
              exact String.Pos.Raw.lt_iff.mpr (by omega)
            have hdec : stopPos.byteIdx - eol.byteIdx < stopPos.byteIdx - pos.byteIdx := by
              have hx1 := String.Pos.Raw.lt_iff.mp hlt
              have hx2 := String.Pos.Raw.lt_iff.mp hpos_lt_eol
              omega
            let acc1 := updateAcc fp acc fileMap "line" pos eol
            rcases triviaAcc_total fp fileMap stopPos eol acc1 with ⟨acc', hta⟩ | htf
            · exact .inl ⟨acc', .line hlt hc1 hnxt hc2 ha heol hconf hta⟩
            · rw [stateOfAcc_updateAcc hconf] at htf
              exact .inr (.lineStep hlt hc1 hnxt hc2 ha heol (String.Pos.Raw.lt_iff.mp hpos_lt_eol) hconf htf)
        · exact .inr (.lineBoundary hlt hc1 hnxt hc2 ha)
      · by_cases hblk : c = '/' ∧ next < stopPos ∧ String.Pos.Raw.get fileMap.source next = '-'
        · rcases hblk with ⟨hc1, hnxt, hc2⟩
          let afterOpen := String.Pos.Raw.next fileMap.source next
          by_cases hao : afterOpen < stopPos
          · let third := String.Pos.Raw.get fileMap.source afterOpen
            by_cases hdoc : third = '-' ∨ third = '!'
            · exact .inr (.docOpenerInTrivia hlt hc1 hnxt hc2 hao hdoc)
            · have hnd1 : third ≠ '-' := fun h => hdoc (.inl h)
              have hnd2 : third ≠ '!' := fun h => hdoc (.inr h)
              let bodyStart := String.Pos.Raw.next fileMap.source afterOpen
              by_cases hbs : bodyStart ≤ stopPos
              · rcases blockStep_total fileMap.source stopPos 1 bodyStart (by omega) with ⟨endPos, hb⟩ | hbf
                · by_cases hconf : SpanConflict (stateOfAcc acc) "block" pos.byteIdx endPos.byteIdx
                  · exact .inr (.blockSpanConflict hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb hconf)
                  · have hpos_lt_end : pos.byteIdx < endPos.byteIdx := by
                      have hx1 := String.Pos.Raw.lt_iff.mp (blockStep_bounds hb).1
                      have hx2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source pos)
                      have hx3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source next)
                      have hx4 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source afterOpen)
                      dsimp only [next, afterOpen, bodyStart] at hx1 hx2 hx3 hx4
                      omega
                    have hdec : stopPos.byteIdx - endPos.byteIdx < stopPos.byteIdx - pos.byteIdx := by
                      have hx1 := String.Pos.Raw.lt_iff.mp hlt
                      omega
                    let acc1 := updateAcc fp acc fileMap "block" pos endPos
                    rcases triviaAcc_total fp fileMap stopPos endPos acc1 with ⟨acc', hta⟩ | htf
                    · exact .inl ⟨acc', .block hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb hconf hta⟩
                    · rw [stateOfAcc_updateAcc hconf] at htf
                      exact .inr (.blockStep hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb hconf htf)
                · exact .inr (.blockBodyFails hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hbf)
              · exact .inr (.blockUnterminated2 hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs)
          · exact .inr (.blockUnterminated1 hlt hc1 hnxt hc2 hao)
        · exact .inr (.unexpectedChar hlt hwsf hline hblk)
  · exact .inl ⟨acc, .done hlt⟩
termination_by stopPos.byteIdx - pos.byteIdx

theorem syntaxAcc_total (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos : String.Pos.Raw) (acc : Core.CommentAcc) :
    (∃ stop acc', SyntaxAcc fp ctx nextPos s pos acc stop acc') ∨
      SyntaxFails ctx nextPos s pos (stateOfAcc acc) := by
  match s with
  | .atom (.original l start t stop) val =>
    by_cases hr : pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos
    · rcases hr with ⟨h1, h2, h3⟩
      rcases triviaAcc_total fp ctx.fileMap start pos acc with ⟨acc1, hta⟩ | htf
      · rcases tokenSafe_dichotomy ctx (.atom (.original l start t stop) val) (ctx.extract start stop) (ctx.get stop) with hts | htr
        · exact .inl ⟨stop, acc1, .atomOrig h1 h2 h3 hta hts⟩
        · exact .inr (.atomToken h1 h2 h3 (triviaAcc_step hta) htr)
      · exact .inr (.atomTrivia h1 h2 h3 htf)
    · exact .inr (.atomRange hr)
  | .ident (.original l start t stop) rawVal val pre =>
    by_cases hr : pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos
    · rcases hr with ⟨h1, h2, h3⟩
      rcases triviaAcc_total fp ctx.fileMap start pos acc with ⟨acc1, hta⟩ | htf
      · rcases tokenSafe_dichotomy ctx (.ident (.original l start t stop) rawVal val pre) (ctx.extract start stop) (ctx.get stop) with hts | htr
        · exact .inl ⟨stop, acc1, .identOrig h1 h2 h3 hta hts⟩
        · exact .inr (.identToken h1 h2 h3 (triviaAcc_step hta) htr)
      · exact .inr (.identTrivia h1 h2 h3 htf)
    · exact .inr (.identRange hr)
  | .node info k args =>
    by_cases hdoc : docKind k = true
    · cases hhead : (Syntax.node info k args).getHeadInfo? with
      | some hi =>
        cases hi with
        | original l1 start t1 s1 =>
          cases htail : (Syntax.node info k args).getTailInfo? with
          | some ti =>
            cases ti with
            | original l2 s2 t2 stop =>
              by_cases hr : pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos
              · rcases hr with ⟨h1, h2, h3⟩
                rcases triviaAcc_total fp ctx.fileMap start pos acc with ⟨acc1, hta⟩ | htf
                · let kind := if k == ``Parser.Command.moduleDoc then "moddoc" else "doc"
                  by_cases hconf : SpanConflict (stateOfAcc acc1) kind start.byteIdx stop.byteIdx
                  · exact .inr (.docSpanConflict hdoc hhead htail h1 h2 h3 (triviaAcc_step hta) rfl hconf)
                  · exact .inl ⟨stop, updateAcc fp acc1 ctx.fileMap kind start stop,
                      .doc hdoc hhead htail h1 h2 h3 hta rfl hconf⟩
                · exact .inr (.docTrivia hdoc hhead htail h1 h2 h3 htf)
              · exact .inr (.docRange hdoc hhead htail hr)
            | _ =>
              refine .inr (.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨_, ht⟩ => ?_)
              rw [htail] at ht; cases ht
          | none =>
            refine .inr (.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨_, ht⟩ => ?_)
            rw [htail] at ht; cases ht
        | _ =>
          refine .inr (.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨hh, _⟩ => ?_)
          rw [hhead] at hh; cases hh
      | none =>
        refine .inr (.docMissingInfo hdoc fun _ _ _ _ _ _ _ _ ⟨hh, _⟩ => ?_)
        rw [hhead] at hh; cases hh
    · have hdocf : docKind k = false := Bool.eq_false_iff.mpr hdoc
      by_cases hch : k = choiceKind
      · subst hch
        cases args with
        | mk alts =>
          cases alts with
          | nil => exact .inr .emptyChoice
          | cons first rest =>
            have _hs1 : sizeOf first < sizeOf (Syntax.node info choiceKind ⟨first :: rest⟩) := by simp; omega
            rcases syntaxAcc_total fp ctx nextPos first pos acc with ⟨stop, acc1, hfirst⟩ | hf
            · have _hs2 : sizeOf rest < sizeOf (Syntax.node info choiceKind ⟨first :: rest⟩) := by simp; omega
              rcases altsAcc_total fp ctx nextPos pos stop rest acc1 with ⟨acc2, halts⟩ | haf
              · exact .inl ⟨stop, acc2, .choice hfirst halts⟩
              · exact .inr (.choiceAlts (syntaxAcc_step hfirst) haf)
            · exact .inr (.choiceFirst hf)
      · cases args with
        | mk argList =>
          have runList (hnot_s : ∀ l start t stop val, (⟨argList⟩ : Array Syntax) ≠ #[.atom (.original l start t stop) val]) :
              (∃ stop acc', SyntaxAcc fp ctx nextPos (Syntax.node info k ⟨argList⟩) pos acc stop acc') ∨
                SyntaxFails ctx nextPos (Syntax.node info k ⟨argList⟩) pos (stateOfAcc acc) := by
            have _hsL : sizeOf argList < sizeOf (Syntax.node info k ⟨argList⟩) := by simp; omega
            rcases listAcc_total fp ctx nextPos argList pos acc with ⟨stop, acc', hl⟩ | hlf
            · exact .inl ⟨stop, acc', .nodeList hdocf hch hnot_s hl⟩
            · exact .inr (.nodeList hdocf hch hnot_s (by simpa using hlf))
          cases argList with
          | nil => exact runList (by intro l st t sp v h; cases congrArg Array.toList h)
          | cons a1 rest1 =>
            cases rest1 with
            | nil =>
              cases a1 with
              | atom ainfo aval =>
                cases ainfo with
                | original l start t stop =>
                  by_cases hr : pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos
                  · rcases hr with ⟨h1, h2, h3⟩
                    rcases triviaAcc_total fp ctx.fileMap start pos acc with ⟨acc1, hta⟩ | htf
                    · rcases tokenSafe_dichotomy ctx (.node info k #[.atom (.original l start t stop) aval])
                          (ctx.extract start stop) (ctx.get stop) with hts | htr
                      · exact .inl ⟨stop, acc1, .singletonAtomNode hdocf hch rfl h1 h2 h3 hta hts⟩
                      · exact .inr (.singletonAtomToken hdocf hch rfl h1 h2 h3 (triviaAcc_step hta) htr)
                    · exact .inr (.singletonAtomTrivia hdocf hch rfl h1 h2 h3 htf)
                  · exact .inr (.singletonAtomRange hdocf hch rfl hr)
                | synthetic _ _ _ => exact runList (by intro l st t sp v h; cases congrArg Array.toList h)
                | none => exact runList (by intro l st t sp v h; cases congrArg Array.toList h)
              | _ => exact runList (by intro l st t sp v h; cases congrArg Array.toList h)
            | cons _ _ => exact runList (by intro l st t sp v h; cases congrArg Array.toList h)
  | .missing =>
    exact .inl ⟨pos, acc, .other
      (fun _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ h => Syntax.noConfusion h)⟩
  | .atom (.synthetic _ _ _) _ =>
    exact .inl ⟨pos, acc, .other
      (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ h => Syntax.noConfusion h)⟩
  | .atom .none _ =>
    exact .inl ⟨pos, acc, .other
      (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ h => Syntax.noConfusion h)⟩
  | .ident (.synthetic _ _ _) _ _ _ =>
    exact .inl ⟨pos, acc, .other
      (fun _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ h => Syntax.noConfusion h)⟩
  | .ident .none _ _ _ =>
    exact .inl ⟨pos, acc, .other
      (fun _ _ _ _ _ h => Syntax.noConfusion h)
      (fun _ _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ h => Syntax.noConfusion h)⟩
termination_by sizeOf s
where
  altsAcc_total (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos pos stop : String.Pos.Raw)
      (alts : List Syntax) (acc : Core.CommentAcc) :
      (∃ acc', AltsAcc fp ctx nextPos pos stop alts acc acc') ∨
        AltsFails ctx nextPos pos stop alts (stateOfAcc acc) := by
    match alts with
    | [] => exact .inl ⟨acc, .nil⟩
    | alt :: rest =>
      rcases syntaxAcc_total fp ctx nextPos alt pos acc with ⟨altStop, acc1, halt⟩ | hf
      · by_cases heq : altStop = stop
        · subst heq
          rcases altsAcc_total fp ctx nextPos pos altStop rest acc1 with ⟨acc2, hrest⟩ | hf2
          · exact .inl ⟨acc2, .cons halt hrest⟩
          · exact .inr (.tail (syntaxAcc_step halt) hf2)
        · exact .inr (.mismatch (syntaxAcc_step halt) heq)
      · exact .inr (.head hf)
  termination_by sizeOf alts

  listAcc_total (fp : FingerprintFn) (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
      (args : List Syntax) (pos : String.Pos.Raw) (acc : Core.CommentAcc) :
      (∃ stop acc', ListAcc fp ctx nextPos args pos acc stop acc') ∨
        ListFails ctx nextPos args pos (stateOfAcc acc) := by
    match args with
    | [] => exact .inl ⟨pos, acc, .nil⟩
    | arg :: rest =>
      rcases syntaxAcc_total fp ctx nextPos arg pos acc with ⟨mid, acc1, harg⟩ | hf
      · rcases listAcc_total fp ctx nextPos rest mid acc1 with ⟨stop, acc2, hrest⟩ | hf2
        · exact .inl ⟨stop, acc2, .cons harg hrest⟩
        · exact .inr (.tail (syntaxAcc_step harg) hf2)
      · exact .inr (.head hf)
  termination_by sizeOf args

theorem rangesAccWith_total (fp : FingerprintFn) (ranges : List Core.CommandRange) (acc : Core.CommentAcc) :
    (∃ acc', RangesAccWith fp ranges acc acc') ∨ CollectRefusal ranges acc := by
  induction ranges generalizing acc with
  | nil => exact .inl ⟨acc, .nil⟩
  | cons r rest ih =>
    by_cases hb : r.prevPos ≤ r.nextPos ∧ r.nextPos ≤ r.ctx.endPos
    · rcases hb with ⟨h1, h2⟩
      rcases syntaxAcc_total fp r.ctx r.nextPos r.stx r.prevPos acc with ⟨mid, acc1, hsa⟩ | hsf
      · rcases triviaAcc_total fp r.ctx.fileMap r.nextPos mid acc1 with ⟨acc2, hta⟩ | htf
        · rcases ih acc2 with ⟨acc', hra⟩ | hrf
          · exact .inl ⟨acc', .cons h1 h2 hsa hta hra⟩
          · exact .inr (.restFails h1 h2 (syntaxAcc_step hsa) (triviaAcc_step hta) hrf)
        · exact .inr (.trailingTriviaFails h1 h2 (syntaxAcc_step hsa) htf)
      · exact .inr (.syntaxFails h1 h2 hsf)
    · exact .inr (.badBounds hb)

theorem triviaAcc_preserves {fp : FingerprintFn} {fileMap : FileMap} {stopPos pos : String.Pos.Raw}
    {acc acc' : Core.CommentAcc} (h : TriviaAcc fp fileMap stopPos pos acc acc') :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  induction h with
  | done _ => exact fun _ _ _ hs => hs
  | ws _ _ _ _ ih => exact ih
  | line _ _ _ _ _ _ _ _ ih =>
    exact fun sb eb c hs => ih sb eb c (updateAcc_preserves sb eb c hs)
  | block _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact fun sb eb c hs => ih sb eb c (updateAcc_preserves sb eb c hs)

mutual

theorem syntaxAcc_preserves {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : SyntaxAcc fp ctx nextPos s pos acc stop acc') :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  match h with
  | .atomOrig _ _ _ ht _ => exact fun sb eb c hs => triviaAcc_preserves ht sb eb c hs
  | .identOrig _ _ _ ht _ => exact fun sb eb c hs => triviaAcc_preserves ht sb eb c hs
  | .doc _ _ _ _ _ _ ht _ _ =>
    exact fun sb eb c hs => updateAcc_preserves sb eb c (triviaAcc_preserves ht sb eb c hs)
  | .choice hf halts =>
    exact fun sb eb c hs => altsAcc_preserves halts sb eb c (syntaxAcc_preserves hf sb eb c hs)
  | .singletonAtomNode _ _ _ _ _ _ ht _ =>
    exact fun sb eb c hs => triviaAcc_preserves ht sb eb c hs
  | .nodeList _ _ _ hlist => exact listAcc_preserves hlist
  | .other _ _ _ => exact fun _ _ _ hs => hs

theorem altsAcc_preserves {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos pos stop : String.Pos.Raw}
    {alts : List Syntax} {acc acc' : Core.CommentAcc}
    (h : AltsAcc fp ctx nextPos pos stop alts acc acc') :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  match h with
  | .nil => exact fun _ _ _ hs => hs
  | .cons halt hrest =>
    exact fun sb eb c hs => altsAcc_preserves hrest sb eb c (syntaxAcc_preserves halt sb eb c hs)

theorem listAcc_preserves {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : ListAcc fp ctx nextPos args pos acc stop acc') :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  match h with
  | .nil => exact fun _ _ _ hs => hs
  | .cons harg hrest =>
    exact fun sb eb c hs => listAcc_preserves hrest sb eb c (syntaxAcc_preserves harg sb eb c hs)

end

theorem rangesAcc_preserves {fp : FingerprintFn} {ranges : List Core.CommandRange}
    {acc acc' : Core.CommentAcc} (h : RangesAccWith fp ranges acc acc') :
    ∀ (sb eb : Nat) (c : Core.Comment),
      acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  induction h with
  | nil => exact fun _ _ _ hs => hs
  | cons _ _ hsa hta _ ih =>
    exact fun sb eb c hs =>
      ih sb eb c (triviaAcc_preserves hta sb eb c (syntaxAcc_preserves hsa sb eb c hs))

theorem healthyToken_iff_tokenSafe {ctx : Parser.ParserContextCore} {tok : Syntax}
    {raw : String} {next : Char} :
    Healthy.Token ctx tok raw next ↔ TokenSafe ctx tok raw next := by
  simp only [Healthy.Token, TokenSafe, healthy_literal_eq, healthy_sym_eq,
    Healthy.noOpener, Healthy.noBoundaryCross, containsOpener, crossesBoundary,
    hasCharPair_healthy_eq_spec, Bool.not_eq_true']
  constructor
  · rintro (h | h | ⟨h1, h2⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨by simp only [Bool.or_eq_false_iff]; simpa using h1, h2⟩)
  · rintro (h | h | ⟨h1, h2⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨by simpa [Bool.or_eq_false_iff] using h1, h2⟩)

theorem spanCompatible_iff_not_conflict {state : SpanState} {kind : String} {sb eb : Nat} :
    Healthy.SpanCompatible state kind sb eb ↔ ¬ SpanConflict state kind sb eb := by
  simp only [Healthy.SpanCompatible, SpanConflict]
  constructor
  · rintro ⟨hlt, hm⟩ hsc
    rcases hsc with hbad | ⟨peb, pk, hst, hneq⟩
    · omega
    · rw [hst] at hm
      rcases hm with ⟨rfl, rfl⟩
      rcases hneq with h1 | h2
      · exact h1 rfl
      · exact h2 rfl
  · intro hnc
    refine ⟨Classical.byContradiction fun h => hnc (.inl (Nat.le_of_not_lt h)), ?_⟩
    cases hst : state sb with
    | none => trivial
    | some p =>
      rcases p with ⟨peb, pk⟩
      refine Classical.byContradiction fun hbad => hnc (.inr ⟨peb, pk, hst, ?_⟩)
      by_cases he : peb = eb
      · exact .inr fun hk => hbad ⟨he, hk⟩
      · exact .inl he

theorem triviaByteCovered_mono {str : String} {acc1 acc2 : Core.CommentAcc} {lo hi b : Nat}
    (h : TriviaByteCovered str acc1 lo hi b)
    (hpres : ∀ (sb eb : Nat) (c : Core.Comment),
      acc1.spans[sb]? = some (eb, c) → acc2.spans[sb]? = some (eb, c)) :
    TriviaByteCovered str acc2 lo hi b := by
  rcases h with ⟨sb, eb, c, hget, hlt, h1, h2⟩ | hws
  · exact .inl ⟨sb, eb, c, hpres sb eb c hget, hlt, h1, h2⟩
  · exact .inr hws

theorem updateAcc_has_span {fp : FingerprintFn} {acc : Core.CommentAcc} {fileMap : FileMap}
    {kind : String} {startPos stopPos : String.Pos.Raw}
    (hnc : ¬ SpanConflict (stateOfAcc acc) kind startPos.byteIdx stopPos.byteIdx) :
    ∃ c, (updateAcc fp acc fileMap kind startPos stopPos).spans[startPos.byteIdx]? =
      some (stopPos.byteIdx, c) := by
  dsimp [updateAcc]
  cases hcur : acc.spans[startPos.byteIdx]? with
  | none =>
    refine ⟨{ kind := kind
              startLine := (fileMap.toPosition startPos).line
              endLine := (fileMap.toPosition (String.Pos.Raw.prev fileMap.source stopPos)).line
              fingerprint := fp (commentText fileMap startPos.byteIdx stopPos.byteIdx) }, by simp⟩
  | some p =>
    rcases p with ⟨peb, pc⟩
    have hpeb : peb = stopPos.byteIdx := by
      refine Classical.byContradiction fun hne => hnc (.inr ⟨peb, pc.kind, ?_, .inl hne⟩)
      simp [stateOfAcc, hcur]
    subst hpeb
    exact ⟨pc, hcur⟩

theorem triviaAcc_covers {fp : FingerprintFn} {fileMap : FileMap} {stopPos pos : String.Pos.Raw}
    {acc acc' : Core.CommentAcc} (h : TriviaAcc fp fileMap stopPos pos acc acc') :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → stopPos.byteIdx ≤ hi →
      ∀ b, pos.byteIdx ≤ b → b < stopPos.byteIdx → TriviaByteCovered fileMap.source acc' lo hi b := by
  induction h with
  | @done pos _ hnot =>
    intro _ _ _ _ b hb1 hb2
    exfalso
    exact hnot (String.Pos.Raw.lt_iff.mpr (by omega))
  | @ws pos _ _ _ hws hn _ ih =>
    intro lo hi hlo hhi b hb1 hb2
    by_cases hlt : b < (String.Pos.Raw.next fileMap.source pos).byteIdx
    · exact .inr ⟨pos, hlo, hb1, hlt, Nat.le_trans (String.Pos.Raw.le_iff.mp hn) hhi, hws⟩
    · have hnx := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source pos)
      exact ih (Nat.le_trans hlo (Nat.le_of_lt hnx)) hhi b (Nat.le_of_not_lt hlt) hb2
  | @line pos eol _ _ hlt _ hnxt _ ha heol hconf hrest ih =>
    intro lo hi hlo hhi b hb1 hb2
    have hbe := lineEnd_bounds ha heol
    have hpos_lt_eol : pos.byteIdx < eol.byteIdx := by
      have h1 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source pos)
      have h2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source (String.Pos.Raw.next fileMap.source pos))
      have h3 := String.Pos.Raw.le_iff.mp hbe.1
      omega
    by_cases hbl : b < eol.byteIdx
    · obtain ⟨c, hc⟩ := updateAcc_has_span hconf
      exact .inl ⟨pos.byteIdx, eol.byteIdx, c,
        triviaAcc_preserves hrest pos.byteIdx eol.byteIdx c hc, hpos_lt_eol, hb1, hbl⟩
    · exact ih (Nat.le_trans hlo (Nat.le_of_lt hpos_lt_eol)) hhi b (Nat.le_of_not_lt hbl) hb2
  | @block pos endPos _ _ hlt _ hnxt _ hao _ _ hbs hb hconf hrest ih =>
    intro lo hi hlo hhi b hb1 hb2
    have hbe := blockStep_bounds hb
    have hpos_lt_end : pos.byteIdx < endPos.byteIdx := by
      have h1 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source pos)
      have h2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source (String.Pos.Raw.next fileMap.source pos))
      have h3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next fileMap.source (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
      have h4 := String.Pos.Raw.lt_iff.mp hbe.1
      omega
    by_cases hbb : b < endPos.byteIdx
    · obtain ⟨c, hc⟩ := updateAcc_has_span hconf
      exact .inl ⟨pos.byteIdx, endPos.byteIdx, c,
        triviaAcc_preserves hrest pos.byteIdx endPos.byteIdx c hc, hpos_lt_end, hb1, hbb⟩
    · exact ih (Nat.le_trans hlo (Nat.le_of_lt hpos_lt_end)) hhi b (Nat.le_of_not_lt hbb) hb2

mutual

theorem syntaxAcc_bounds {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : SyntaxAcc fp ctx nextPos s pos acc stop acc') (hpn : pos ≤ nextPos) :
    pos ≤ stop ∧ stop ≤ nextPos := by
  match h with
  | .atomOrig h1 h2 h3 _ _ =>
    exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)), h3⟩
  | .identOrig h1 h2 h3 _ _ =>
    exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)), h3⟩
  | .doc _ _ _ h1 h2 h3 _ _ _ =>
    exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)), h3⟩
  | .choice hf _ => exact syntaxAcc_bounds hf hpn
  | .singletonAtomNode _ _ _ h1 h2 h3 _ _ =>
    exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)), h3⟩
  | .nodeList _ _ _ hl => exact listAcc_bounds hl hpn
  | .other _ _ _ => exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_refl _), hpn⟩

theorem listAcc_bounds {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : ListAcc fp ctx nextPos args pos acc stop acc') (hpn : pos ≤ nextPos) :
    pos ≤ stop ∧ stop ≤ nextPos := by
  match h with
  | .nil => exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_refl _), hpn⟩
  | .cons harg hrest =>
    have hb1 := syntaxAcc_bounds harg hpn
    have hb2 := listAcc_bounds hrest hb1.2
    exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp hb1.1) (String.Pos.Raw.le_iff.mp hb2.1)), hb2.2⟩

end

theorem byteAccounted_lift {ctx : Parser.ParserContextCore} {arg node : Syntax}
    {acc1 acc2 : Core.CommentAcc} {lo hi b : Nat}
    (hpres : ∀ (sb eb : Nat) (c : Core.Comment),
      acc1.spans[sb]? = some (eb, c) → acc2.spans[sb]? = some (eb, c))
    (hlift : ∀ leaf st sp, OriginalLeafIn arg leaf st sp → OriginalLeafIn node leaf st sp)
    (hba : ByteAccounted ctx arg acc1 lo hi b) :
    ByteAccounted ctx node acc2 lo hi b := by
  rcases hba with ht | ⟨leaf, st, sp, ho, h1, h2, h3, h4, hts⟩
  · exact .inl (triviaByteCovered_mono ht hpres)
  · exact .inr ⟨leaf, st, sp, hlift leaf st sp ho, h1, h2, h3, h4, hts⟩

mutual

theorem syntaxAcc_covers {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : SyntaxAcc fp ctx nextPos s pos acc stop acc') (hpn : pos ≤ nextPos) :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → nextPos.byteIdx ≤ hi →
      ∀ b, pos.byteIdx ≤ b → b < stop.byteIdx → ByteAccounted ctx s acc' lo hi b := by
  match h with
  | .atomOrig (start := start) h1 h2 h3 ht hts =>
    intro lo hi hlo hhi b hb1 hb2
    by_cases hlt : b < start.byteIdx
    · exact .inl (triviaAcc_covers ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) b hb1 hlt)
    · exact .inr ⟨_, _, _, .atom _ _ _ _ _ _ rfl,
        Nat.le_trans hlo (String.Pos.Raw.le_iff.mp h1), Nat.le_of_not_lt hlt, hb2,
        Nat.le_trans (String.Pos.Raw.le_iff.mp h3) hhi, hts⟩
  | .identOrig (start := start) h1 h2 h3 ht hts =>
    intro lo hi hlo hhi b hb1 hb2
    by_cases hlt : b < start.byteIdx
    · exact .inl (triviaAcc_covers ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) b hb1 hlt)
    · exact .inr ⟨_, _, _, .ident _ _ _ _ _ _ _ _ rfl,
        Nat.le_trans hlo (String.Pos.Raw.le_iff.mp h1), Nat.le_of_not_lt hlt, hb2,
        Nat.le_trans (String.Pos.Raw.le_iff.mp h3) hhi, hts⟩
  | .singletonAtomNode (start := start) hdocf hch hatom h1 h2 h3 ht hts =>
    intro lo hi hlo hhi b hb1 hb2
    by_cases hlt : b < start.byteIdx
    · exact .inl (triviaAcc_covers ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) b hb1 hlt)
    · exact .inr ⟨_, _, _, .singletonAtomNode _ _ _ _ _ _ _ _ hdocf hch hatom,
        Nat.le_trans hlo (String.Pos.Raw.le_iff.mp h1), Nat.le_of_not_lt hlt, hb2,
        Nat.le_trans (String.Pos.Raw.le_iff.mp h3) hhi, hts⟩
  | @SyntaxAcc.doc _ _ _ info k args l1 start t1 s1 l2 s2 t2 stop pos acc acc1 kind _ _ _ h1 h2 h3 ht _ hnc =>
    intro lo hi hlo hhi b hb1 hb2
    have hlt_ss : start.byteIdx < stop.byteIdx :=
      Classical.byContradiction fun h => hnc (.inl (Nat.le_of_not_lt h))
    by_cases hlt : b < start.byteIdx
    · have htc := triviaAcc_covers ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) b hb1 hlt
      exact .inl (triviaByteCovered_mono htc updateAcc_preserves)
    · obtain ⟨c, hc⟩ := updateAcc_has_span hnc
      exact .inl (.inl ⟨start.byteIdx, stop.byteIdx, c, hc, hlt_ss, Nat.le_of_not_lt hlt, hb2⟩)
  | @SyntaxAcc.choice _ _ _ info first alts pos acc stop acc1 acc2 hf halts =>
    intro lo hi hlo hhi b hb1 hb2
    have hba := syntaxAcc_covers hf hpn hlo hhi b hb1 hb2
    refine byteAccounted_lift (altsAcc_preserves halts) (fun leaf st sp ho => ?_) hba
    exact .child info choiceKind ⟨first :: alts⟩ first leaf st sp (by simp) ho
  | @SyntaxAcc.nodeList _ _ _ info k args pos acc stop acc' _ _ _ hl =>
    intro lo hi hlo hhi b hb1 hb2
    exact listAcc_covers hl (node := Syntax.node info k args)
      (fun arg hmem leaf st sp ho => .child info k args arg leaf st sp hmem ho)
      hpn hlo hhi b hb1 hb2
  | .other _ _ _ =>
    intro _ _ _ _ b hb1 hb2
    omega

theorem listAcc_covers {fp : FingerprintFn} {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    {node : Syntax}
    (h : ListAcc fp ctx nextPos args pos acc stop acc')
    (hlift : ∀ arg ∈ args, ∀ leaf st sp, OriginalLeafIn arg leaf st sp → OriginalLeafIn node leaf st sp)
    (hpn : pos ≤ nextPos) :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → nextPos.byteIdx ≤ hi →
      ∀ b, pos.byteIdx ≤ b → b < stop.byteIdx → ByteAccounted ctx node acc' lo hi b := by
  match h with
  | .nil =>
    intro _ _ _ _ b hb1 hb2
    omega
  | @ListAcc.cons _ _ _ arg rest pos acc mid acc1 stop acc2 harg hrest =>
    intro lo hi hlo hhi b hb1 hb2
    have hbm := syntaxAcc_bounds harg hpn
    by_cases hlt : b < mid.byteIdx
    · have hba := syntaxAcc_covers harg hpn hlo hhi b hb1 hlt
      exact byteAccounted_lift (listAcc_preserves hrest)
        (hlift arg (by simp)) hba
    · exact listAcc_covers hrest (fun a hm => hlift a (by simp [hm])) hbm.2
        (Nat.le_trans hlo (String.Pos.Raw.le_iff.mp hbm.1)) hhi b (Nat.le_of_not_lt hlt) hb2

end

theorem triviaAcc_new_spans {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {ctx : Parser.ParserContextCore} {stx : Syntax}
    {stopPos pos : String.Pos.Raw} {acc acc' : Core.CommentAcc}
    (h : TriviaAcc fp ctx.fileMap stopPos pos acc acc') :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → stopPos.byteIdx ≤ hi → hi ≤ ctx.endPos.byteIdx →
      ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (lo ≤ sb ∧ eb ≤ hi ∧ GenuineCommentSpan ctx stx sb eb c ∧
            c.fingerprint = fp (commentText ctx.fileMap sb eb)) := by
  induction h with
  | done _ =>
    intro _ _ _ _ _ sb eb c hs
    exact .inl hs
  | @ws pos _ _ _ _ _ _ ih =>
    intro lo hi hlo hhi hend sb eb c hs
    have hnx := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source pos)
    exact ih (Nat.le_trans hlo (Nat.le_of_lt hnx)) hhi hend sb eb c hs
  | @line pos eol acc _ hlt hc1 hnxt hc2 ha heol _ hrest ih =>
    intro lo hi hlo hhi hend sb eb c hs
    have hbe := lineEnd_bounds ha heol
    have hpos_lt_eol : pos.byteIdx < eol.byteIdx := by
      have h1 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source pos)
      have h2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))
      have h3 := String.Pos.Raw.le_iff.mp hbe.1
      omega
    rcases ih (Nat.le_trans hlo (Nat.le_of_lt hpos_lt_eol)) hhi hend sb eb c hs with hold | hnew
    · rcases updateAcc_new_span hfp sb eb c hold with hacc | ⟨rfl, rfl, hkind, hfpC, hsl, hel, hfeq⟩
      · exact .inl hacc
      · refine .inr ⟨hlo, Nat.le_trans (String.Pos.Raw.le_iff.mp hbe.2) hhi, ?_, hfeq⟩
        refine ⟨hpos_lt_eol, Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp hbe.2) hhi) hend,
          ?_, hfpC, hsl, hel, .inl ⟨hkind, hc1, hc2, String.Pos.Raw.le_iff.mp hbe.1,
            lineEnd_self (String.Pos.Raw.le_iff.mp ha) heol⟩⟩
        rw [hkind]
        simp [validCommentKind]
    · exact .inr hnew
  | @block pos endPos acc _ hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb _ hrest ih =>
    intro lo hi hlo hhi hend sb eb c hs
    have hbe := blockStep_bounds hb
    have hpos_lt_end : pos.byteIdx < endPos.byteIdx := by
      have h1 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source pos)
      have h2 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos))
      have h3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
      have h4 := String.Pos.Raw.lt_iff.mp hbe.1
      omega
    rcases ih (Nat.le_trans hlo (Nat.le_of_lt hpos_lt_end)) hhi hend sb eb c hs with hold | hnew
    · rcases updateAcc_new_span hfp sb eb c hold with hacc | ⟨rfl, rfl, hkind, hfpC, hsl, hel, hfeq⟩
      · exact .inl hacc
      · have hp2_lt : (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)).byteIdx < endPos.byteIdx := by
          have h3 := String.Pos.Raw.lt_iff.mp (String.Pos.Raw.lt_next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source (String.Pos.Raw.next ctx.fileMap.source pos)))
          have h4 := String.Pos.Raw.lt_iff.mp hbe.1
          omega
        refine .inr ⟨hlo, Nat.le_trans (String.Pos.Raw.le_iff.mp hbe.2) hhi, ?_, hfeq⟩
        refine ⟨hpos_lt_end, Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp hbe.2) hhi) hend,
          ?_, hfpC, hsl, hel, .inr (.inl ⟨hkind, hc1, hc2, hp2_lt, hnd1, hnd2,
            String.Pos.Raw.le_iff.mp (String.Pos.Raw.le_iff.mpr (Nat.le_of_lt (String.Pos.Raw.lt_iff.mp hbe.1))),
            blockStep_self hb, blockStep_ends_slash_minus hb⟩)⟩
        rw [hkind]
        simp [validCommentKind]
    · exact .inr hnew

theorem genuineCommentSpan_lift {ctx : Parser.ParserContextCore} {arg node : Syntax}
    {sb eb : Nat} {c : Core.Comment}
    (hlift : ∀ kind sb eb, DocNodeIn arg kind sb eb → DocNodeIn node kind sb eb)
    (hg : GenuineCommentSpan ctx arg sb eb c) :
    GenuineCommentSpan ctx node sb eb c := by
  rcases hg with ⟨h1, h2, h3, h4, h5, h6, h7 | h7 | ⟨hkind, hd⟩⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, .inl h7⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, .inr (.inl h7)⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, .inr (.inr ⟨hkind, hlift c.kind sb eb hd⟩)⟩

mutual

theorem syntaxAcc_new_spans {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : SyntaxAcc fp ctx nextPos s pos acc stop acc') (hpn : pos ≤ nextPos) :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → nextPos.byteIdx ≤ hi → hi ≤ ctx.endPos.byteIdx →
      ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          (lo ≤ sb ∧ eb ≤ hi ∧ GenuineCommentSpan ctx s sb eb c ∧
            c.fingerprint = fp (commentText ctx.fileMap sb eb)) := by
  match h with
  | .atomOrig _ h2 h3 ht _ =>
    intro lo hi hlo hhi hend sb eb c hs
    exact triviaAcc_new_spans hfp ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) hend sb eb c hs
  | .identOrig _ h2 h3 ht _ =>
    intro lo hi hlo hhi hend sb eb c hs
    exact triviaAcc_new_spans hfp ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) hend sb eb c hs
  | .singletonAtomNode _ _ _ _ h2 h3 ht _ =>
    intro lo hi hlo hhi hend sb eb c hs
    exact triviaAcc_new_spans hfp ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) hend sb eb c hs
  | @SyntaxAcc.doc _ _ _ info k args l1 start t1 s1 l2 s2 t2 stop pos acc acc1 kind hdoc hh htl h1 h2 h3 ht hk hnc =>
    intro lo hi hlo hhi hend sb eb c hs
    rcases updateAcc_new_span hfp sb eb c hs with hold | ⟨rfl, rfl, hkind, hfpC, hsl, hel, hfeq⟩
    · exact triviaAcc_new_spans hfp ht hlo (Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h2) (String.Pos.Raw.le_iff.mp h3)) hhi) hend sb eb c hold
    · have hlt_ss : start.byteIdx < stop.byteIdx :=
        Classical.byContradiction fun h => hnc (.inl (Nat.le_of_not_lt h))
      have hvalid : validCommentKind c.kind := by
        rw [hkind, hk]
        split <;> simp [validCommentKind]
      have hkd : c.kind = "doc" ∨ c.kind = "moddoc" := by
        rw [hkind, hk]
        split <;> simp
      refine .inr ⟨Nat.le_trans hlo (String.Pos.Raw.le_iff.mp h1),
        Nat.le_trans (String.Pos.Raw.le_iff.mp h3) hhi, ?_, hfeq⟩
      refine ⟨hlt_ss, Nat.le_trans (Nat.le_trans (String.Pos.Raw.le_iff.mp h3) hhi) hend,
        hvalid, hfpC, hsl, hel, .inr (.inr ⟨hkd, ?_⟩)⟩
      exact .here hdoc hh htl (by rw [hkind, hk])
  | @SyntaxAcc.choice _ _ _ info first alts pos acc stop acc1 acc2 hf halts =>
    intro lo hi hlo hhi hend sb eb c hs
    have hch : docKind choiceKind = false := by decide
    rcases altsAcc_new_spans hfp halts hpn hlo hhi hend sb eb c hs with hold | ⟨a, hm, h1, h2, hg, hfeq⟩
    · rcases syntaxAcc_new_spans hfp hf hpn hlo hhi hend sb eb c hold with hacc | ⟨h1, h2, hg, hfeq⟩
      · exact .inl hacc
      · refine .inr ⟨h1, h2, genuineCommentSpan_lift (fun kind sb eb hd => ?_) hg, hfeq⟩
        exact .child hch (by simp) hd
    · refine .inr ⟨h1, h2, genuineCommentSpan_lift (fun kind sb eb hd => ?_) hg, hfeq⟩
      exact .child hch (by simp [hm]) hd
  | @SyntaxAcc.nodeList _ _ _ info k args pos acc stop acc' hdocf _ _ hl =>
    intro lo hi hlo hhi hend sb eb c hs
    rcases listAcc_new_spans hfp hl hpn hlo hhi hend sb eb c hs with hold | ⟨a, hm, h1, h2, hg, hfeq⟩
    · exact .inl hold
    · refine .inr ⟨h1, h2, genuineCommentSpan_lift (fun kind sb eb hd => ?_) hg, hfeq⟩
      exact .child hdocf hm hd
  | .other _ _ _ =>
    intro _ _ _ _ _ sb eb c hs
    exact .inl hs

theorem altsAcc_new_spans {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {ctx : Parser.ParserContextCore} {nextPos pos stop : String.Pos.Raw}
    {alts : List Syntax} {acc acc' : Core.CommentAcc}
    (h : AltsAcc fp ctx nextPos pos stop alts acc acc') (hpn : pos ≤ nextPos) :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → nextPos.byteIdx ≤ hi → hi ≤ ctx.endPos.byteIdx →
      ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          ∃ alt ∈ alts, lo ≤ sb ∧ eb ≤ hi ∧ GenuineCommentSpan ctx alt sb eb c ∧
            c.fingerprint = fp (commentText ctx.fileMap sb eb) := by
  match h with
  | .nil =>
    intro _ _ _ _ _ sb eb c hs
    exact .inl hs
  | @AltsAcc.cons _ _ _ _ _ alt rest _ acc1 _ halt hrest =>
    intro lo hi hlo hhi hend sb eb c hs
    rcases altsAcc_new_spans hfp hrest hpn hlo hhi hend sb eb c hs with hold | ⟨a, hm, h1, h2, hg, hfeq⟩
    · rcases syntaxAcc_new_spans hfp halt hpn hlo hhi hend sb eb c hold with hacc | ⟨h1, h2, hg, hfeq⟩
      · exact .inl hacc
      · exact .inr ⟨alt, by simp, h1, h2, hg, hfeq⟩
    · exact .inr ⟨a, by simp [hm], h1, h2, hg, hfeq⟩

theorem listAcc_new_spans {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {acc : Core.CommentAcc}
    {stop : String.Pos.Raw} {acc' : Core.CommentAcc}
    (h : ListAcc fp ctx nextPos args pos acc stop acc') (hpn : pos ≤ nextPos) :
    ∀ {lo hi : Nat}, lo ≤ pos.byteIdx → nextPos.byteIdx ≤ hi → hi ≤ ctx.endPos.byteIdx →
      ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          ∃ arg ∈ args, lo ≤ sb ∧ eb ≤ hi ∧ GenuineCommentSpan ctx arg sb eb c ∧
            c.fingerprint = fp (commentText ctx.fileMap sb eb) := by
  match h with
  | .nil =>
    intro _ _ _ _ _ sb eb c hs
    exact .inl hs
  | @ListAcc.cons _ _ _ arg rest pos acc mid acc1 stop acc2 harg hrest =>
    intro lo hi hlo hhi hend sb eb c hs
    have hbm := syntaxAcc_bounds harg hpn
    rcases listAcc_new_spans hfp hrest hbm.2 (Nat.le_trans hlo (String.Pos.Raw.le_iff.mp hbm.1)) hhi hend sb eb c hs with hold | ⟨a, hm, h1, h2, hg, hfeq⟩
    · rcases syntaxAcc_new_spans hfp harg hpn hlo hhi hend sb eb c hold with hacc | ⟨h1, h2, hg, hfeq⟩
      · exact .inl hacc
      · exact .inr ⟨arg, by simp, h1, h2, hg, hfeq⟩
    · exact .inr ⟨a, by simp [hm], h1, h2, hg, hfeq⟩

end

theorem rangesAcc_byte_coverage {fp : FingerprintFn} {ranges : List Core.CommandRange}
    {acc acc' : Core.CommentAcc} (h : RangesAccWith fp ranges acc acc') :
    ∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
      ByteAccounted r.ctx r.stx acc' r.prevPos.byteIdx r.nextPos.byteIdx b := by
  induction h with
  | nil => exact fun _ hr => nomatch hr
  | @cons r rest acc mid acc1 acc2 acc' h1 _ hsa hta hra ih =>
    intro r' hr' b hb1 hb2
    rcases List.mem_cons.mp hr' with rfl | hrrest
    · have hbm := syntaxAcc_bounds hsa h1
      by_cases hlt : b < mid.byteIdx
      · have hba := syntaxAcc_covers hsa h1 (Nat.le_refl _) (Nat.le_refl _) b hb1 hlt
        exact byteAccounted_lift
          (fun sb eb c hs => rangesAcc_preserves hra sb eb c (triviaAcc_preserves hta sb eb c hs))
          (fun _ _ _ ho => ho) hba
      · have htc := triviaAcc_covers hta (String.Pos.Raw.le_iff.mp hbm.1) (Nat.le_refl _) b
          (Nat.le_of_not_lt hlt) hb2
        exact .inl (triviaByteCovered_mono htc (rangesAcc_preserves hra))
    · exact ih r' hrrest b hb1 hb2

theorem contiguousFrom_find {start endPos : String.Pos.Raw} {ranges : List Core.CommandRange}
    (hc : ContiguousFrom start endPos ranges) :
    ∀ b, start.byteIdx ≤ b → b < endPos.byteIdx →
      ∃ r ∈ ranges, r.prevPos.byteIdx ≤ b ∧ b < r.nextPos.byteIdx := by
  induction ranges generalizing start with
  | nil =>
    intro b h1 h2
    simp [ContiguousFrom] at hc
    subst hc
    omega
  | cons r rest ih =>
    intro b h1 h2
    rcases hc with ⟨rfl, hle, hrest⟩
    by_cases hlt : b < r.nextPos.byteIdx
    · exact ⟨r, by simp, h1, hlt⟩
    · obtain ⟨r', hm, hb1, hb2⟩ := ih hrest b (Nat.le_of_not_lt hlt) h2
      exact ⟨r', by simp [hm], hb1, hb2⟩

theorem rangesAcc_genuine_new_spans {fp : FingerprintFn} (hfp : ∀ s, IsFingerprint (fp s))
    {ranges : List Core.CommandRange} {acc acc' : Core.CommentAcc}
    (h : RangesAccWith fp ranges acc acc') :
    ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
      acc.spans[sb]? = some (eb, c) ∨
        ∃ r ∈ ranges,
          r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧ GenuineCommentSpan r.ctx r.stx sb eb c ∧
            c.fingerprint = fp (commentText r.ctx.fileMap sb eb) := by
  induction h with
  | nil => exact fun _ _ _ hs => .inl hs
  | @cons r rest acc mid acc1 acc2 acc' h1 h2 hsa hta hra ih =>
    intro sb eb c hs
    rcases ih sb eb c hs with hold2 | ⟨r', hm, hs1, hs2, hg, hfeq⟩
    · have hbm := syntaxAcc_bounds hsa h1
      rcases triviaAcc_new_spans hfp (stx := r.stx) hta (String.Pos.Raw.le_iff.mp hbm.1) (Nat.le_refl _) (String.Pos.Raw.le_iff.mp h2) sb eb c hold2 with hold1 | ⟨hs1, hs2, hg, hfeq⟩
      · rcases syntaxAcc_new_spans hfp hsa h1 (Nat.le_refl _) (Nat.le_refl _) (String.Pos.Raw.le_iff.mp h2) sb eb c hold1 with hold0 | ⟨hs1, hs2, hg, hfeq⟩
        · exact .inl hold0
        · exact .inr ⟨r, by simp, hs1, hs2, hg, hfeq⟩
      · exact .inr ⟨r, by simp, hs1, hs2, hg, hfeq⟩
    · exact .inr ⟨r', by simp [hm], hs1, hs2, hg, hfeq⟩

theorem blockStep_and_fails_disjoint {str : String} {stopPos : String.Pos.Raw}
    {n : Nat} {pos endPos : String.Pos.Raw}
    (hb : BlockStep str stopPos n pos endPos) :
    ¬ BlockFails str stopPos n pos := by
  induction hb with
  | closeTop hn1 hlt h1 h2 h3 ha =>
    intro hf
    cases hf with
    | atEof hnot => exact hnot hlt
    | closeBoundary _ _ _ _ hna => exact hna ha
    | closeNested hne _ _ _ _ _ _ => exact hne hn1
    | openBoundary _ ho _ _ _ => simp_all
    | openNested _ ho _ _ _ _ => simp_all
    | other _ hnc _ _ => exact hnc ⟨h1, h2, h3⟩
  | closeNested hne _ hlt h1 h2 h3 ha _ ih =>
    intro hf
    cases hf with
    | atEof hnot => exact hnot hlt
    | closeBoundary _ _ _ _ hna => exact hna ha
    | closeNested _ _ _ _ _ _ hrest => exact ih hrest
    | openBoundary _ ho _ _ _ => simp_all
    | openNested _ ho _ _ _ _ => simp_all
    | other _ hnc _ _ => exact hnc ⟨h1, h2, h3⟩
  | openNested _ hlt h1 h2 h3 ha _ ih =>
    intro hf
    cases hf with
    | atEof hnot => exact hnot hlt
    | closeBoundary _ hc _ _ _ => simp_all
    | closeNested _ _ hc _ _ _ _ => simp_all
    | openBoundary _ _ _ _ hna => exact hna ha
    | openNested _ _ _ _ _ hrest => exact ih hrest
    | other _ _ hno _ => exact hno ⟨h1, h2, h3⟩
  | other _ hlt hnc hno _ ih =>
    intro hf
    cases hf with
    | atEof hnot => exact hnot hlt
    | closeBoundary _ a b c _ => exact hnc ⟨a, b, c⟩
    | closeNested _ _ a b c _ _ => exact hnc ⟨a, b, c⟩
    | openBoundary _ a b c _ => exact hno ⟨a, b, c⟩
    | openNested _ a b c _ _ => exact hno ⟨a, b, c⟩
    | other _ _ _ hrest => exact ih hrest

theorem triviaStep_det {fileMap : FileMap} {stopPos pos : String.Pos.Raw} {state s1 s2 : SpanState}
    (h1 : TriviaStep fileMap stopPos pos state s1)
    (h2 : TriviaStep fileMap stopPos pos state s2) : s1 = s2 := by
  induction h1 generalizing s2 with
  | done hnot =>
    cases h2 with
    | done _ => rfl
    | ws h _ _ _ => exact absurd h hnot
    | line h _ _ _ _ _ _ _ => exact absurd h hnot
    | block h _ _ _ _ _ _ _ _ _ _ => exact absurd h hnot
  | ws hlt hws _ _ ih =>
    cases h2 with
    | done hnot => exact absurd hlt hnot
    | ws _ _ _ hrest => exact ih hrest
    | line _ hc _ _ _ _ _ _ => simp_all
    | block _ hc _ _ _ _ _ _ _ _ _ => simp_all
  | line hlt hc1 _ hc2 _ heol _ _ ih =>
    cases h2 with
    | done hnot => exact absurd hlt hnot
    | ws _ hws _ _ => simp_all
    | line _ _ _ _ _ heol2 _ hrest =>
      have := lineEnd_det heol heol2
      subst this
      exact ih hrest
    | block _ hc _ _ _ _ _ _ _ _ _ => simp_all
  | block hlt hc1 _ hc2 _ _ _ _ hb _ _ ih =>
    cases h2 with
    | done hnot => exact absurd hlt hnot
    | ws _ hws _ _ => simp_all
    | line _ hc _ _ _ _ _ _ => simp_all
    | block _ _ _ _ _ _ _ _ hb2 _ hrest =>
      have := blockStep_det hb hb2
      subst this
      exact ih hrest

theorem triviaStep_and_fails_disjoint {fileMap : FileMap} {stopPos pos : String.Pos.Raw}
    {state state' : SpanState} (hs : TriviaStep fileMap stopPos pos state state') :
    ¬ TriviaFails fileMap stopPos pos state := by
  induction hs with
  | done hnot =>
    intro hf
    cases hf with
    | wsBoundary h _ _ => exact hnot h
    | wsStep h _ _ _ => exact hnot h
    | lineBoundary h _ _ _ _ => exact hnot h
    | lineSpanConflict h _ _ _ _ _ _ => exact hnot h
    | lineStep h _ _ _ _ _ _ _ => exact hnot h
    | docOpenerInTrivia h _ _ _ _ _ => exact hnot h
    | blockUnterminated1 h _ _ _ _ => exact hnot h
    | blockUnterminated2 h _ _ _ _ _ _ _ => exact hnot h
    | blockBodyFails h _ _ _ _ _ _ _ _ => exact hnot h
    | blockSpanConflict h _ _ _ _ _ _ _ _ _ => exact hnot h
    | blockStep h _ _ _ _ _ _ _ _ _ _ => exact hnot h
    | unexpectedChar h _ _ _ => exact hnot h
  | ws hlt hws hn _ ih =>
    intro hf
    cases hf with
    | wsBoundary _ _ hbad => exact hbad hn
    | wsStep _ _ _ hrest => exact ih hrest
    | lineBoundary _ hc _ _ _ => simp_all
    | lineSpanConflict _ hc _ _ _ _ _ => simp_all
    | lineStep _ hc _ _ _ _ _ _ => simp_all
    | docOpenerInTrivia _ hc _ _ _ _ => simp_all
    | blockUnterminated1 _ hc _ _ _ => simp_all
    | blockUnterminated2 _ hc _ _ _ _ _ _ => simp_all
    | blockBodyFails _ hc _ _ _ _ _ _ _ => simp_all
    | blockSpanConflict _ hc _ _ _ _ _ _ _ _ => simp_all
    | blockStep _ hc _ _ _ _ _ _ _ _ _ => simp_all
    | unexpectedChar _ hf _ _ => simp_all
  | line hlt hc1 hnxt hc2 ha heol hnc _ ih =>
    intro hf
    cases hf with
    | wsBoundary _ hws _ => simp_all
    | wsStep _ hws _ _ => simp_all
    | lineBoundary _ _ _ _ hbad => exact hbad ha
    | lineSpanConflict _ _ _ _ _ heol2 hconf =>
      rw [lineEnd_det heol heol2] at hnc
      exact hnc hconf
    | lineStep _ _ _ _ _ heol2 _ _ hrest =>
      have := lineEnd_det heol heol2
      subst this
      exact ih hrest
    | docOpenerInTrivia _ hc _ _ _ _ => simp_all
    | blockUnterminated1 _ hc _ _ _ => simp_all
    | blockUnterminated2 _ hc _ _ _ _ _ _ => simp_all
    | blockBodyFails _ hc _ _ _ _ _ _ _ => simp_all
    | blockSpanConflict _ hc _ _ _ _ _ _ _ _ => simp_all
    | blockStep _ hc _ _ _ _ _ _ _ _ _ => simp_all
    | unexpectedChar _ _ hnl _ => exact hnl ⟨hc1, hnxt, hc2⟩
  | block hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb hnc _ ih =>
    intro hf
    cases hf with
    | wsBoundary _ hws _ => simp_all
    | wsStep _ hws _ _ => simp_all
    | lineBoundary _ hc _ _ _ => simp_all
    | lineSpanConflict _ hc _ _ _ _ _ => simp_all
    | lineStep _ hc _ _ _ _ _ _ => simp_all
    | docOpenerInTrivia _ _ _ _ _ hdoc =>
      rcases hdoc with h | h
      · exact hnd1 h
      · exact hnd2 h
    | blockUnterminated1 _ _ _ _ hbad => exact hbad hao
    | blockUnterminated2 _ _ _ _ _ _ _ hbad => exact hbad hbs
    | blockBodyFails _ _ _ _ _ _ _ _ hbf => exact blockStep_and_fails_disjoint hb hbf
    | blockSpanConflict _ _ _ _ _ _ _ _ hb2 hconf =>
      rw [blockStep_det hb hb2] at hnc
      exact hnc hconf
    | blockStep _ _ _ _ _ _ _ _ hb2 _ hrest =>
      rw [blockStep_det hb hb2] at ih
      exact ih hrest
    | unexpectedChar _ _ _ hnb => exact hnb ⟨hc1, hnxt, hc2⟩

mutual

theorem syntaxStep_det {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop1 stop2 : String.Pos.Raw} {state1 state2 : SpanState}
    (h1 : SyntaxStep ctx nextPos s pos state stop1 state1)
    (h2 : SyntaxStep ctx nextPos s pos state stop2 state2) :
    stop1 = stop2 ∧ state1 = state2 := by
  match h1 with
  | .atomOrig _ _ _ ht1 _ =>
    cases h2 with
    | atomOrig _ _ _ ht2 _ => exact ⟨rfl, triviaStep_det ht1 ht2⟩
    | other hna _ _ => exact absurd rfl (hna _ _ _ _ _)
  | .identOrig _ _ _ ht1 _ =>
    cases h2 with
    | identOrig _ _ _ ht2 _ => exact ⟨rfl, triviaStep_det ht1 ht2⟩
    | other _ hni _ => exact absurd rfl (hni _ _ _ _ _ _ _)
  | .doc hdoc hh1 ht1 _ _ _ htr1 hk1 _ =>
    cases h2 with
    | doc _ hh2 ht2 _ _ _ htr2 hk2 _ =>
      rw [hh1] at hh2; cases hh2
      rw [ht1] at ht2; cases ht2
      have := triviaStep_det htr1 htr2
      subst this; rw [hk1, hk2]
      exact ⟨rfl, rfl⟩
    | choice _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | singletonAtomNode hdocf _ _ _ _ _ _ _ => rw [hdocf] at hdoc; cases hdoc
    | nodeList hdocf _ _ _ => rw [hdocf] at hdoc; cases hdoc
    | other _ _ hnn => exact absurd rfl (hnn _ _ _)
  | .choice hf1 ha1 =>
    cases h2 with
    | doc hdoc _ _ _ _ _ _ _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | choice hf2 ha2 =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det hf1 hf2
      exact ⟨rfl, altsStep_det ha1 ha2⟩
    | singletonAtomNode _ hch _ _ _ _ _ _ => exact absurd rfl hch
    | nodeList _ hch _ _ => exact absurd rfl hch
    | other _ _ hnn => exact absurd rfl (hnn _ _ _)
  | .singletonAtomNode hdocf hch hatom _ _ _ ht1 _ =>
    cases h2 with
    | doc hdoc _ _ _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | choice _ _ => exact absurd rfl hch
    | singletonAtomNode _ _ hatom2 _ _ _ ht2 _ =>
      rw [hatom] at hatom2; cases hatom2
      exact ⟨rfl, triviaStep_det ht1 ht2⟩
    | nodeList _ _ hnot_s _ =>
      subst hatom
      exact absurd rfl (hnot_s _ _ _ _ _)
    | other _ _ hnn => exact absurd rfl (hnn _ _ _)
  | .nodeList hdocf hch hnot_s hl1 =>
    cases h2 with
    | doc hdoc _ _ _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | choice _ _ => exact absurd rfl hch
    | singletonAtomNode _ _ hatom _ _ _ _ _ =>
      subst hatom
      exact absurd rfl (hnot_s _ _ _ _ _)
    | nodeList _ _ _ hl2 => exact listStep_det hl1 hl2
    | other _ _ hnn => exact absurd rfl (hnn _ _ _)
  | .other hna hni hnn =>
    cases h2 with
    | atomOrig _ _ _ _ _ => exact absurd rfl (hna _ _ _ _ _)
    | identOrig _ _ _ _ _ => exact absurd rfl (hni _ _ _ _ _ _ _)
    | doc _ _ _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | choice _ _ => exact absurd rfl (hnn _ _ _)
    | singletonAtomNode _ _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | nodeList _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | other _ _ _ => exact ⟨rfl, rfl⟩

theorem altsStep_det {ctx : Parser.ParserContextCore} {nextPos pos stop : String.Pos.Raw}
    {alts : List Syntax} {state state1 state2 : SpanState}
    (h1 : AltsStep ctx nextPos pos stop alts state state1)
    (h2 : AltsStep ctx nextPos pos stop alts state state2) : state1 = state2 := by
  match h1, h2 with
  | .nil, .nil => rfl
  | .cons ha1 hr1, .cons ha2 hr2 =>
    obtain ⟨_, rfl⟩ := syntaxStep_det ha1 ha2
    exact altsStep_det hr1 hr2

theorem listStep_det {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop1 stop2 : String.Pos.Raw} {state1 state2 : SpanState}
    (h1 : ListStep ctx nextPos args pos state stop1 state1)
    (h2 : ListStep ctx nextPos args pos state stop2 state2) :
    stop1 = stop2 ∧ state1 = state2 := by
  match h1, h2 with
  | .nil, .nil => exact ⟨rfl, rfl⟩
  | .cons ha1 hr1, .cons ha2 hr2 =>
    obtain ⟨rfl, rfl⟩ := syntaxStep_det ha1 ha2
    exact listStep_det hr1 hr2

end

theorem rangesStep_det {ranges : List Core.CommandRange} {state s1 s2 : SpanState}
    (h1 : RangesStep ranges state s1) (h2 : RangesStep ranges state s2) :
    s1 = s2 := by
  induction h1 generalizing s2 with
  | nil =>
    cases h2
    rfl
  | cons _ _ hs1 ht1 _ ih =>
    cases h2 with
    | cons _ _ hs2 ht2 hr2 =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det hs1 hs2
      rw [triviaStep_det ht1 ht2] at ih
      exact ih hr2

theorem tokenSafe_and_refusal_disjoint {ctx : Parser.ParserContextCore} {tok : Syntax}
    {raw : String} {next : Char}
    (hs : TokenSafe ctx tok raw next) (hr : TokenRefusal ctx tok raw next) : False := by
  cases hr with
  | openerInRaw hl hs' ho =>
    rcases hs with h1 | h1 | ⟨h1, _⟩ <;> simp_all
  | boundaryCross hl hs' hc =>
    rcases hs with h1 | h1 | ⟨_, h1⟩ <;> simp_all

mutual

theorem syntaxStep_and_fails_disjoint {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {s : Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop : String.Pos.Raw} {state' : SpanState}
    (hs : SyntaxStep ctx nextPos s pos state stop state') :
    ¬ SyntaxFails ctx nextPos s pos state := by
  intro hf
  match hs with
  | .atomOrig h1 h2 h3 ht hts =>
    cases hf with
    | atomRange hnr => exact hnr ⟨h1, h2, h3⟩
    | atomTrivia _ _ _ htf => exact triviaStep_and_fails_disjoint ht htf
    | atomToken _ _ _ ht2 htr =>
      have := triviaStep_det ht ht2
      subst this
      exact tokenSafe_and_refusal_disjoint hts htr
  | .identOrig h1 h2 h3 ht hts =>
    cases hf with
    | identRange hnr => exact hnr ⟨h1, h2, h3⟩
    | identTrivia _ _ _ htf => exact triviaStep_and_fails_disjoint ht htf
    | identToken _ _ _ ht2 htr =>
      have := triviaStep_det ht ht2
      subst this
      exact tokenSafe_and_refusal_disjoint hts htr
  | .doc hdoc hh1 ht1 h1 h2 h3 htr1 hk1 hnc =>
    cases hf with
    | docMissingInfo _ hno => exact hno _ _ _ _ _ _ _ _ ⟨hh1, ht1⟩
    | docRange _ hh2 ht2 hnr =>
      rw [hh1] at hh2; cases hh2; rw [ht1] at ht2; cases ht2
      exact hnr ⟨h1, h2, h3⟩
    | docTrivia _ hh2 ht2 _ _ _ htf =>
      rw [hh1] at hh2; cases hh2; rw [ht1] at ht2; cases ht2
      exact triviaStep_and_fails_disjoint htr1 htf
    | docSpanConflict _ hh2 ht2 _ _ _ htr2 hk2 hconf =>
      rw [hh1] at hh2; cases hh2; rw [ht1] at ht2; cases ht2
      have hst := triviaStep_det htr1 htr2
      subst hst
      rw [hk1] at hnc
      rw [hk2] at hconf
      exact hnc hconf
    | emptyChoice =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | choiceFirst _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | choiceAlts _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | singletonAtomRange hdocf _ _ _ => rw [hdocf] at hdoc; cases hdoc
    | singletonAtomTrivia hdocf _ _ _ _ _ _ => rw [hdocf] at hdoc; cases hdoc
    | singletonAtomToken hdocf _ _ _ _ _ _ _ => rw [hdocf] at hdoc; cases hdoc
    | nodeList hdocf _ _ _ => rw [hdocf] at hdoc; cases hdoc
  | .choice hfirst halts =>
    cases hf with
    | docMissingInfo hdoc _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | docRange hdoc _ _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | docTrivia hdoc _ _ _ _ _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | docSpanConflict hdoc _ _ _ _ _ _ _ _ =>
      have : docKind choiceKind = false := by decide
      rw [this] at hdoc; cases hdoc
    | choiceFirst hff => exact syntaxStep_and_fails_disjoint hfirst hff
    | choiceAlts hf2 haf =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det hfirst hf2
      exact altsStep_and_fails_disjoint halts haf
    | singletonAtomRange _ hch _ _ => exact absurd rfl hch
    | singletonAtomTrivia _ hch _ _ _ _ _ => exact absurd rfl hch
    | singletonAtomToken _ hch _ _ _ _ _ _ => exact absurd rfl hch
    | nodeList _ hch _ _ => exact absurd rfl hch
  | .singletonAtomNode hdocf hch hatom h1 h2 h3 ht hts =>
    subst hatom
    cases hf with
    | docMissingInfo hdoc _ => rw [hdoc] at hdocf; cases hdocf
    | docRange hdoc _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | docTrivia hdoc _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | docSpanConflict hdoc _ _ _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | choiceFirst _ => exact absurd rfl hch
    | choiceAlts _ _ => exact absurd rfl hch
    | singletonAtomRange _ _ hatom2 hnr =>
      cases hatom2
      exact hnr ⟨h1, h2, h3⟩
    | singletonAtomTrivia _ _ hatom2 _ _ _ htf =>
      cases hatom2
      exact triviaStep_and_fails_disjoint ht htf
    | singletonAtomToken _ _ hatom2 _ _ _ ht2 htr =>
      cases hatom2
      have hst := triviaStep_det ht ht2
      subst hst
      exact tokenSafe_and_refusal_disjoint hts htr
    | nodeList _ _ hnot_s _ =>
      exact absurd rfl (hnot_s _ _ _ _ _)
  | .nodeList hdocf hch hnot_s hl =>
    cases hf with
    | docMissingInfo hdoc _ => rw [hdoc] at hdocf; cases hdocf
    | docRange hdoc _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | docTrivia hdoc _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | docSpanConflict hdoc _ _ _ _ _ _ _ _ => rw [hdoc] at hdocf; cases hdocf
    | emptyChoice => exact absurd rfl hch
    | choiceFirst _ => exact absurd rfl hch
    | choiceAlts _ _ => exact absurd rfl hch
    | singletonAtomRange _ _ hatom _ =>
      subst hatom
      exact absurd rfl (hnot_s _ _ _ _ _)
    | singletonAtomTrivia _ _ hatom _ _ _ _ =>
      subst hatom
      exact absurd rfl (hnot_s _ _ _ _ _)
    | singletonAtomToken _ _ hatom _ _ _ _ _ =>
      subst hatom
      exact absurd rfl (hnot_s _ _ _ _ _)
    | nodeList _ _ _ hlf => exact listStep_and_fails_disjoint hl hlf
  | .other hna hni hnn =>
    cases hf with
    | atomRange _ => exact absurd rfl (hna _ _ _ _ _)
    | atomTrivia _ _ _ _ => exact absurd rfl (hna _ _ _ _ _)
    | atomToken _ _ _ _ _ => exact absurd rfl (hna _ _ _ _ _)
    | identRange _ => exact absurd rfl (hni _ _ _ _ _ _ _)
    | identTrivia _ _ _ _ => exact absurd rfl (hni _ _ _ _ _ _ _)
    | identToken _ _ _ _ _ => exact absurd rfl (hni _ _ _ _ _ _ _)
    | docMissingInfo _ _ => exact absurd rfl (hnn _ _ _)
    | docRange _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | docTrivia _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | docSpanConflict _ _ _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | emptyChoice => exact absurd rfl (hnn _ _ _)
    | choiceFirst _ => exact absurd rfl (hnn _ _ _)
    | choiceAlts _ _ => exact absurd rfl (hnn _ _ _)
    | singletonAtomRange _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | singletonAtomTrivia _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | singletonAtomToken _ _ _ _ _ _ _ _ => exact absurd rfl (hnn _ _ _)
    | nodeList _ _ _ _ => exact absurd rfl (hnn _ _ _)

theorem altsStep_and_fails_disjoint {ctx : Parser.ParserContextCore} {nextPos pos stop : String.Pos.Raw}
    {alts : List Syntax} {state state' : SpanState}
    (hs : AltsStep ctx nextPos pos stop alts state state') :
    ¬ AltsFails ctx nextPos pos stop alts state := by
  intro hf
  match hs with
  | .nil => cases hf
  | .cons halt hrest =>
    cases hf with
    | head hff => exact syntaxStep_and_fails_disjoint halt hff
    | mismatch ha2 hneq =>
      obtain ⟨rfl, _⟩ := syntaxStep_det halt ha2
      exact hneq rfl
    | tail ha2 hrf =>
      obtain ⟨_, rfl⟩ := syntaxStep_det halt ha2
      exact altsStep_and_fails_disjoint hrest hrf

theorem listStep_and_fails_disjoint {ctx : Parser.ParserContextCore} {nextPos : String.Pos.Raw}
    {args : List Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop : String.Pos.Raw} {state' : SpanState}
    (hs : ListStep ctx nextPos args pos state stop state') :
    ¬ ListFails ctx nextPos args pos state := by
  intro hf
  match hs with
  | .nil => cases hf
  | .cons harg hrest =>
    cases hf with
    | head hff => exact syntaxStep_and_fails_disjoint harg hff
    | tail ha2 hrf =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det harg ha2
      exact listStep_and_fails_disjoint hrest hrf

end

theorem rangesAcc_not_collectRefusal {fp : FingerprintFn} {ranges : List Core.CommandRange}
    {acc acc' : Core.CommentAcc} (h : RangesAccWith fp ranges acc acc') :
    ¬ CollectRefusal ranges acc := by
  dsimp [CollectRefusal]
  induction h with
  | nil => intro hf; cases hf
  | cons h1 h2 hsa hta _ ih =>
    intro hf
    cases hf with
    | badBounds hnb => exact hnb ⟨h1, h2⟩
    | syntaxFails _ _ hsf => exact syntaxStep_and_fails_disjoint (syntaxAcc_step hsa) hsf
    | trailingTriviaFails _ _ hs2 htf =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det (syntaxAcc_step hsa) hs2
      exact triviaStep_and_fails_disjoint (triviaAcc_step hta) htf
    | restFails _ _ hs2 ht2 hrf =>
      obtain ⟨rfl, rfl⟩ := syntaxStep_det (syntaxAcc_step hsa) hs2
      rw [triviaStep_det (triviaAcc_step hta) ht2] at ih
      exact ih hrf

theorem healthy_lineEnd_to_spec {str : String} {stopPos p eol : String.Pos.Raw}
    (h : Healthy.LineEnd str stopPos p eol) : LineEnd str stopPos p eol := by
  induction h with
  | done hnot => exact .done hnot
  | nl hlt hnl => exact .nl hlt hnl
  | step hlt hne _ ih => exact .step hlt hne ih

theorem healthy_blockCloses_to_step {str : String} {stopPos : String.Pos.Raw}
    {n : Nat} {pos endPos : String.Pos.Raw}
    (h : Healthy.BlockCloses str stopPos n pos endPos) : BlockStep str stopPos n pos endPos := by
  induction h with
  | closeTop hn hlt h1 h2 h3 ha => exact .closeTop hn hlt h1 h2 h3 ha
  | closeNested hne hn hlt h1 h2 h3 ha _ ih => exact .closeNested hne hn hlt h1 h2 h3 ha ih
  | openNested hn hlt h1 h2 h3 ha _ ih => exact .openNested hn hlt h1 h2 h3 ha ih
  | other hn hlt hc ho _ ih => exact .other hn hlt hc ho ih

theorem healthy_trivia_to_acc (fp : FingerprintFn) {fileMap : FileMap} {stopPos pos : String.Pos.Raw}
    {state state' : SpanState} (h : Healthy.Trivia fileMap stopPos pos state state') :
    ∀ acc, stateOfAcc acc = state →
      ∃ acc', TriviaAcc fp fileMap stopPos pos acc acc' ∧ stateOfAcc acc' = state' := by
  induction h with
  | done hnot =>
    intro acc hst
    exact ⟨acc, .done hnot, hst⟩
  | ws hlt hws hn _ ih =>
    intro acc hst
    obtain ⟨acc', hta, hst'⟩ := ih acc hst
    exact ⟨acc', .ws hlt hws hn hta, hst'⟩
  | line hlt hc1 hnxt hc2 ha heol hcomp _ ih =>
    intro acc hst
    subst hst
    have hnc := spanCompatible_iff_not_conflict.mp hcomp
    obtain ⟨acc', hta, hst'⟩ := ih (updateAcc fp acc fileMap "line" _ _) (stateOfAcc_updateAcc hnc)
    exact ⟨acc', .line hlt hc1 hnxt hc2 ha (healthy_lineEnd_to_spec heol) hnc hta, hst'⟩
  | block hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs hb hcomp _ ih =>
    intro acc hst
    subst hst
    have hnc := spanCompatible_iff_not_conflict.mp hcomp
    obtain ⟨acc', hta, hst'⟩ := ih (updateAcc fp acc fileMap "block" _ _) (stateOfAcc_updateAcc hnc)
    exact ⟨acc', .block hlt hc1 hnxt hc2 hao hnd1 hnd2 hbs (healthy_blockCloses_to_step hb) hnc hta, hst'⟩

mutual

theorem healthy_syntaxOk_to_acc (fp : FingerprintFn) {ctx : Parser.ParserContextCore}
    {nextPos : String.Pos.Raw} {s : Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop : String.Pos.Raw} {state' : SpanState}
    (h : Healthy.SyntaxOk ctx nextPos s pos state stop state') :
    ∀ acc, stateOfAcc acc = state →
      ∃ acc', SyntaxAcc fp ctx nextPos s pos acc stop acc' ∧ stateOfAcc acc' = state' := by
  match h with
  | .atomOrig h1 h2 h3 ht htok =>
    intro acc hst
    obtain ⟨acc1, hta, hst1⟩ := healthy_trivia_to_acc fp ht acc hst
    exact ⟨acc1, .atomOrig h1 h2 h3 hta (healthyToken_iff_tokenSafe.mp htok), hst1⟩
  | .identOrig h1 h2 h3 ht htok =>
    intro acc hst
    obtain ⟨acc1, hta, hst1⟩ := healthy_trivia_to_acc fp ht acc hst
    exact ⟨acc1, .identOrig h1 h2 h3 hta (healthyToken_iff_tokenSafe.mp htok), hst1⟩
  | .doc hdoc hh htl h1 h2 h3 ht hk hcomp =>
    intro acc hst
    obtain ⟨acc1, hta, hst1⟩ := healthy_trivia_to_acc fp ht acc hst
    subst hst1
    have hnc := spanCompatible_iff_not_conflict.mp hcomp
    exact ⟨updateAcc fp acc1 ctx.fileMap _ _ _,
      .doc hdoc hh htl h1 h2 h3 hta hk hnc, stateOfAcc_updateAcc hnc⟩
  | .choice hf ha =>
    intro acc hst
    obtain ⟨acc1, hfa, hst1⟩ := healthy_syntaxOk_to_acc fp hf acc hst
    obtain ⟨acc2, haa, hst2⟩ := healthy_altsOk_to_acc fp ha acc1 hst1
    exact ⟨acc2, .choice hfa haa, hst2⟩
  | .singletonAtomNode hdocf hch hatom h1 h2 h3 ht htok =>
    intro acc hst
    obtain ⟨acc1, hta, hst1⟩ := healthy_trivia_to_acc fp ht acc hst
    exact ⟨acc1, .singletonAtomNode hdocf hch hatom h1 h2 h3 hta
      (healthyToken_iff_tokenSafe.mp htok), hst1⟩
  | .nodeList hdocf hch hnot_s hl =>
    intro acc hst
    obtain ⟨acc', hla, hst'⟩ := healthy_listOk_to_acc fp hl acc hst
    exact ⟨acc', .nodeList hdocf hch hnot_s hla, hst'⟩
  | .other hna hni hnn =>
    intro acc hst
    exact ⟨acc, .other hna hni hnn, hst⟩

theorem healthy_altsOk_to_acc (fp : FingerprintFn) {ctx : Parser.ParserContextCore}
    {nextPos pos stop : String.Pos.Raw} {alts : List Syntax} {state state' : SpanState}
    (h : Healthy.AltsOk ctx nextPos pos stop alts state state') :
    ∀ acc, stateOfAcc acc = state →
      ∃ acc', AltsAcc fp ctx nextPos pos stop alts acc acc' ∧ stateOfAcc acc' = state' := by
  match h with
  | .nil => intro acc hst; exact ⟨acc, .nil, hst⟩
  | .cons ha hr =>
    intro acc hst
    obtain ⟨acc1, haa, hst1⟩ := healthy_syntaxOk_to_acc fp ha acc hst
    obtain ⟨acc2, hra, hst2⟩ := healthy_altsOk_to_acc fp hr acc1 hst1
    exact ⟨acc2, .cons haa hra, hst2⟩

theorem healthy_listOk_to_acc (fp : FingerprintFn) {ctx : Parser.ParserContextCore}
    {nextPos : String.Pos.Raw} {args : List Syntax} {pos : String.Pos.Raw} {state : SpanState}
    {stop : String.Pos.Raw} {state' : SpanState}
    (h : Healthy.ListOk ctx nextPos args pos state stop state') :
    ∀ acc, stateOfAcc acc = state →
      ∃ acc', ListAcc fp ctx nextPos args pos acc stop acc' ∧ stateOfAcc acc' = state' := by
  match h with
  | .nil => intro acc hst; exact ⟨acc, .nil, hst⟩
  | .cons ha hr =>
    intro acc hst
    obtain ⟨acc1, haa, hst1⟩ := healthy_syntaxOk_to_acc fp ha acc hst
    obtain ⟨acc2, hra, hst2⟩ := healthy_listOk_to_acc fp hr acc1 hst1
    exact ⟨acc2, .cons haa hra, hst2⟩

end

theorem healthy_to_rangesAcc (fp : FingerprintFn) {ranges : List Core.CommandRange}
    {state state' : SpanState} (h : Healthy.RangesOk ranges state state') :
    ∀ acc, stateOfAcc acc = state → ∃ acc', RangesAccWith fp ranges acc acc' := by
  induction h with
  | nil => intro acc _; exact ⟨acc, .nil⟩
  | cons h1 h2 hs ht _ ih =>
    intro acc hst
    obtain ⟨acc1, hsa, hst1⟩ := healthy_syntaxOk_to_acc fp hs acc hst
    obtain ⟨acc2, hta, hst2⟩ := healthy_trivia_to_acc fp ht acc1 hst1
    obtain ⟨acc', hra⟩ := ih acc2 hst2
    exact ⟨acc', .cons h1 h2 hsa hta hra⟩

theorem collectRefusal_contradicts_healthy {ranges : List Core.CommandRange} {acc : Core.CommentAcc}
    (href : CollectRefusal ranges acc) (hh : Healthy.Collect ranges acc) : False := by
  obtain ⟨_, hro⟩ := hh
  obtain ⟨_, hra⟩ := healthy_to_rangesAcc fpModel hro acc rfl
  exact rangesAcc_not_collectRefusal hra href

noncomputable def emptyAcc : Core.CommentAcc := { spans := {} }

def dashFileMap : FileMap :=
  { source := "--", positions := #[0] }

def dashInputCtx : Parser.InputContext where
  inputString := "--"
  fileName := "<spec>"
  fileMap := dashFileMap
  endPos := ⟨2⟩
  endPos_valid := String.Pos.Raw.le_iff.mpr (by decide)

noncomputable def dashCtx : Parser.ParserContextCore where
  toInputContext := dashInputCtx
  env := emptyEnv
  options := ∅
  prec := 0
  tokens := {}

noncomputable def dashRange : Core.CommandRange where
  ctx := dashCtx
  stx := .missing
  prevPos := ⟨0⟩
  nextPos := ⟨2⟩

noncomputable def badBoundsRange : Core.CommandRange where
  ctx := dashCtx
  stx := .missing
  prevPos := ⟨1⟩
  nextPos := ⟨0⟩

noncomputable def collectRangesModelWith (fp : FingerprintFn) (errMsg : String) : CollectRangesFn :=
  open Classical in
  fun ranges acc =>
    if h : ∃ acc', RangesAccWith fp ranges acc acc' then .ok (Classical.choose h)
    else .error errMsg

noncomputable def collectRangesModel : CollectRangesFn :=
  collectRangesModelWith fpModel "collect failed"

theorem collectRangesModelWith_meets (fp : FingerprintFn) (hfp : fingerprintRecord.Meets fp)
    (errMsg : String) :
    collectRangesRecord.Meets (collectRangesModelWith fp errMsg) := by
  have hfpValid : ∀ s, IsFingerprint (fp s) := hfp.2 _ List.mem_cons_self
  have hfpNonConst : ∃ a b, fp a ≠ fp b := hfp.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc acc' hok sb eb c hs
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact rangesAcc_preserves (Classical.choose_spec h) sb eb c hs
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges start endPos acc acc' hcont hok b hb1 hb2
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      obtain ⟨r, hmem, hr1, hr2⟩ := contiguousFrom_find hcont b hb1 hb2
      exact ⟨r, hmem, hr1, hr2, rangesAcc_byte_coverage (Classical.choose_spec h) r hmem b hr1 hr2⟩
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc acc' hok r hr b hb1 hb2
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact rangesAcc_byte_coverage (Classical.choose_spec h) r hr b hb1 hb2
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc acc' hok
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact rangesAcc_step (Classical.choose_spec h)
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc acc' hok sb eb c hs
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact (rangesAcc_genuine_new_spans hfpValid (Classical.choose_spec h) sb eb c hs).imp id
        fun ⟨r, hr, h1, h2, hg, _⟩ => ⟨r, hr, h1, h2, hg⟩
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨fp, hfpValid, hfpNonConst, ?_⟩
    intro ranges acc acc' hok sb eb c hs
    dsimp [collectRangesModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact (rangesAcc_genuine_new_spans hfpValid (Classical.choose_spec h) sb eb c hs).imp id
        fun ⟨r, hr, h1, h2, _, hfeq⟩ => ⟨r, hr, h1, h2, hfeq⟩
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro ranges acc msg herr
    dsimp [collectRangesModelWith] at herr
    split at herr
    · contradiction
    · rename_i hna
      rcases rangesAccWith_total fp ranges acc with hok | href
      · exact absurd hok hna
      · exact href
  exact nomatch hp

theorem collectRangesModel_meets : collectRangesRecord.Meets collectRangesModel :=
  collectRangesModelWith_meets fpModel fpModel_meets "collect failed"

theorem collectRanges_o2 : O2 collectRangesRecord := by
  refine (o2_correct _).mpr ⟨⟨collectRangesModel, (fun _ h => nomatch h)⟩, ?_⟩
  let c0 : Core.Comment :=
    { kind := "line"
      startLine := (dashCtx.fileMap.toPosition ⟨0⟩).line
      endLine := (dashCtx.fileMap.toPosition (String.Pos.Raw.prev dashCtx.fileMap.source ⟨2⟩)).line
      fingerprint := zeroFp }
  let acc0 : Core.CommentAcc :=
    { spans := (Std.HashMap.emptyWithCapacity : Std.HashMap Nat (Nat × Core.Comment)).insert 0 (2, c0) }
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨(dashCtx, .missing, acc0, 0, 2, 0), ?_⟩
    dsimp [ByteAccounted, TriviaByteCovered]
    exact .inl (.inl ⟨0, 2, c0, by simp [acc0], by omega, by omega, by omega⟩)
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨(dashCtx, .missing, 0, 2, c0), ?_⟩
    dsimp [GenuineCommentSpan]
    refine ⟨by omega, ?_, ?_, zeroFp_valid, rfl, rfl, .inl ⟨rfl, by decide, by decide, by decide, .done (by decide)⟩⟩
    · exact Nat.le_refl 2
    · simp [validCommentKind, c0]
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨([], stateOfAcc emptyAcc, stateOfAcc emptyAcc), .nil⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · refine ⟨([badBoundsRange], emptyAcc), ?_⟩
    refine .badBounds ?_
    intro ⟨h1, _⟩
    simp [badBoundsRange, String.Pos.Raw.le_iff] at h1
  exact nomatch hp

theorem collectRanges_o2Run : O2Run collectRangesRecord :=
  o2Run_of_meets collectRangesModel_meets

theorem dashCtx_zero_not_accounted :
    ¬ ByteAccounted dashCtx .missing emptyAcc 0 2 0 := by
  intro hba
  rcases hba with (⟨sb, eb, c, hs, _, _, _⟩ | ⟨p, hp1, hp2, _, _, hws⟩) | ⟨_, _, _, ho, _⟩
  · simp [emptyAcc] at hs
  · have hpb : p.byteIdx = 0 := by omega
    have hp : p = ⟨0⟩ := by cases p; cases hpb; rfl
    subst hp
    have hws0 : (String.Pos.Raw.get "--" ⟨0⟩).isWhitespace = true := hws
    have hfalse : (String.Pos.Raw.get "--" ⟨0⟩).isWhitespace = false := by decide
    rw [hfalse] at hws0
    contradiction
  · cases ho

theorem collectRanges_o3 : O3 collectRangesRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  let acc1 : Core.CommentAcc :=
    { spans := (Std.HashMap.emptyWithCapacity : Std.HashMap Nat (Nat × Core.Comment)).insert 0 (1, sampleComment1) }
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .ok emptyAcc, fun h => ?_⟩
    have hs := h [] acc1 emptyAcc rfl 0 1 sampleComment1 (by simp [acc1])
    simp [emptyAcc] at hs
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ acc => .ok acc, fun h => ?_⟩
    have hcont : ContiguousFrom ⟨0⟩ ⟨2⟩ [dashRange] := by
      dsimp [ContiguousFrom, dashRange]
      exact ⟨rfl, String.Pos.Raw.le_iff.mpr (by decide), rfl⟩
    obtain ⟨r, hr, _, _, hba⟩ := h [dashRange] ⟨0⟩ ⟨2⟩ emptyAcc emptyAcc hcont rfl 0 (Nat.le_refl 0) (by decide)
    simp at hr
    subst hr
    exact dashCtx_zero_not_accounted hba
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ acc => .ok acc, fun h => ?_⟩
    have hba := h [dashRange] emptyAcc emptyAcc rfl dashRange (by simp) 0
      (by dsimp [dashRange]; omega) (by dsimp [dashRange]; omega)
    exact dashCtx_zero_not_accounted hba
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .ok acc1, fun h => ?_⟩
    have hrs := h [] emptyAcc acc1 rfl
    have h0 := congrFun (rangesStep_det .nil hrs) 0
    simp [emptyAcc, acc1, stateOfAcc] at h0
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .ok acc1, fun h => ?_⟩
    rcases h [] emptyAcc acc1 rfl 0 1 sampleComment1 (by simp [acc1]) with hs | ⟨r, hr, _⟩
    · simp [emptyAcc] at hs
    · cases hr
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .ok acc1, fun h => ?_⟩
    rcases h with ⟨_, _, _, hfn⟩
    rcases hfn [] emptyAcc acc1 rfl 0 1 sampleComment1 (by simp [acc1]) with hs | ⟨r, hr, _⟩
    · simp [emptyAcc] at hs
    · cases hr
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .error "always", fun h => ?_⟩
    have href := h [] emptyAcc "always" rfl
    cases href
  exact nomatch hc

theorem collectRanges_o4 : O4 collectRangesRecord := o4_function _ rfl

def CollectRangesFreedom : Freedom CollectRangesFn :=
  .rel fun f g =>
    (∃ fp : FingerprintFn,
      (∀ text, IsFingerprint (fp text)) ∧ (∃ a b, fp a ≠ fp b) ∧
      ∀ ranges acc acc1, f ranges acc = .ok acc1 →
        ∀ (sb eb : Nat) (c : Core.Comment), acc1.spans[sb]? = some (eb, c) →
          acc.spans[sb]? = some (eb, c) ∨
            ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
              c.fingerprint = fp (commentText r.ctx.fileMap sb eb)) ∧
    (∃ fp : FingerprintFn,
      (∀ text, IsFingerprint (fp text)) ∧ (∃ a b, fp a ≠ fp b) ∧
      ∀ ranges acc acc2, g ranges acc = .ok acc2 →
        ∀ (sb eb : Nat) (c : Core.Comment), acc2.spans[sb]? = some (eb, c) →
          acc.spans[sb]? = some (eb, c) ∨
            ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
              c.fingerprint = fp (commentText r.ctx.fileMap sb eb)) ∧
    ∀ ranges acc,
      (Healthy.Collect ranges acc → (f ranges acc).isOk = true ∧ (g ranges acc).isOk = true) ∧
      (¬ CollectRefusal ranges acc → (f ranges acc).isOk = true ∧ (g ranges acc).isOk = true) ∧
      (∀ acc1, f ranges acc = .ok acc1 →
        (∀ (sb eb : Nat) (c : Core.Comment), acc.spans[sb]? = some (eb, c) → acc1.spans[sb]? = some (eb, c)) ∧
        RangesStep ranges (stateOfAcc acc) (stateOfAcc acc1) ∧
        (∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
          ByteAccounted r.ctx r.stx acc1 r.prevPos.byteIdx r.nextPos.byteIdx b) ∧
        (∀ (sb eb : Nat) (c : Core.Comment), acc1.spans[sb]? = some (eb, c) →
          acc.spans[sb]? = some (eb, c) ∨
            ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
              GenuineCommentSpan r.ctx r.stx sb eb c)) ∧
      (∀ acc2, g ranges acc = .ok acc2 →
        (∀ (sb eb : Nat) (c : Core.Comment), acc.spans[sb]? = some (eb, c) → acc2.spans[sb]? = some (eb, c)) ∧
        RangesStep ranges (stateOfAcc acc) (stateOfAcc acc2) ∧
        (∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
          ByteAccounted r.ctx r.stx acc2 r.prevPos.byteIdx r.nextPos.byteIdx b) ∧
        (∀ (sb eb : Nat) (c : Core.Comment), acc2.spans[sb]? = some (eb, c) →
          acc.spans[sb]? = some (eb, c) ∨
            ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
              GenuineCommentSpan r.ctx r.stx sb eb c)) ∧
      (∀ acc1 acc2, f ranges acc = .ok acc1 → g ranges acc = .ok acc2 →
        stateOfAcc acc1 = stateOfAcc acc2)

theorem collectRanges_healthy_owed :
    ∀ f ranges acc, collectRangesRecord.Meets f →
      Healthy.Collect ranges acc → ∃ acc', f ranges acc = .ok acc' := by
  intro f ranges acc hf hh
  cases hfv : f ranges acc with
  | ok acc' => exact ⟨acc', rfl⟩
  | error msg =>
    exfalso
    have href := hf.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      ranges acc msg hfv
    exact collectRefusal_contradicts_healthy href hh

theorem collectRanges_o5 : O5 collectRangesRecord CollectRangesFreedom := by
  refine ⟨fun f g hf hg => ?_, trivial⟩
  have fpProp (fn : CollectRangesFn) (hfn : collectRangesRecord.Meets fn) :=
    hfn.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  refine ⟨fpProp f hf, fpProp g hg, fun ranges acc => ?_⟩
  have isOk_of_no_ref (fn : CollectRangesFn) (hfn : collectRangesRecord.Meets fn)
      (hnr : ¬ CollectRefusal ranges acc) : (fn ranges acc).isOk = true := by
    cases hval : fn ranges acc with
    | ok _ => rfl
    | error msg =>
      exfalso
      exact hnr (hfn.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
        ranges acc msg hval)
  have okProps (fn : CollectRangesFn) (hfn : collectRangesRecord.Meets fn) (acc1 : Core.CommentAcc)
      (hok : fn ranges acc = .ok acc1) :
      (∀ (sb eb : Nat) (c : Core.Comment), acc.spans[sb]? = some (eb, c) → acc1.spans[sb]? = some (eb, c)) ∧
      RangesStep ranges (stateOfAcc acc) (stateOfAcc acc1) ∧
      (∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
        ByteAccounted r.ctx r.stx acc1 r.prevPos.byteIdx r.nextPos.byteIdx b) ∧
      (∀ (sb eb : Nat) (c : Core.Comment), acc1.spans[sb]? = some (eb, c) →
        acc.spans[sb]? = some (eb, c) ∨
          ∃ r ∈ ranges, r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
            GenuineCommentSpan r.ctx r.stx sb eb c) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hfn.2 _ List.mem_cons_self ranges acc acc1 hok
    · exact hfn.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        ranges acc acc1 hok
    · exact hfn.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ranges acc acc1 hok
    · exact hfn.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) ranges acc acc1 hok
  refine ⟨fun hh => ⟨?_, ?_⟩, fun hnr => ⟨isOk_of_no_ref f hf hnr, isOk_of_no_ref g hg hnr⟩,
    fun acc1 hok => okProps f hf acc1 hok, fun acc2 hok => okProps g hg acc2 hok,
    fun acc1 acc2 h1 h2 => ?_⟩
  · obtain ⟨_, h1⟩ := collectRanges_healthy_owed f ranges acc hf hh
    rw [h1]; rfl
  · obtain ⟨_, h2⟩ := collectRanges_healthy_owed g ranges acc hg hh
    rw [h2]; rfl
  · exact rangesStep_det
      (hf.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        ranges acc acc1 h1)
      (hg.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        ranges acc acc2 h2)

theorem collectRanges_not_o5_eq : ¬ O5 collectRangesRecord .eq := by
  refine not_o5_eq collectRangesModel_meets
    (collectRangesModelWith_meets fpModel fpModel_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun heq [badBoundsRange]) emptyAcc
  have hna : ¬ ∃ acc', RangesAcc [badBoundsRange] emptyAcc acc' := by
    intro ⟨acc', h⟩
    exact rangesAcc_not_collectRefusal h (.badBounds (by
      intro ⟨h1, _⟩
      simp [badBoundsRange, String.Pos.Raw.le_iff] at h1))
  dsimp [collectRangesModel, collectRangesModelWith] at hdiff
  simp [hna] at hdiff

theorem collectRanges_oPair_whole :
    ∀ c ∈ collectRangesRecord.props, OPair (Pair.whole collectRangesRecord c) collectRangesRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨collectRangesModel, collectRangesModel_meets, fun _ => collectRangesModel_meets.2 c hc⟩

def collectRangesPerInputPair : Pair CollectRangesFn where
  Input := List Core.CommandRange × Core.CommentAcc
  pre := fun _ => True
  post := fun i f => ∀ acc', f i.1 i.2 = .ok acc' →
    ∀ (sb eb : Nat) (c : Core.Comment), i.2.spans[sb]? = some (eb, c) →
      acc'.spans[sb]? = some (eb, c)

theorem collectRanges_perInput_pairOf :
    ∀ c ∈ collectRangesRecord.props, c.name = "preserves_prior_spans" →
      collectRangesRecord.PairOf c collectRangesPerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, collectRangesRecord, Pair.Met, collectRangesPerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem collectRanges_perInput_table_attack :
    ∀ i : collectRangesPerInputPair.Input, collectRangesPerInputPair.pre i →
      ∃ f : CollectRangesFn, (∀ r a, f r a = f [] emptyAcc) ∧
        collectRangesPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ _ => .error "table", fun _ _ => rfl, ?_⟩
  intro _ h; contradiction

theorem collectRanges_interim_const_fails :
    ∀ c, ¬ collectRangesRecord.Meets (fun _ _ => c) := by
  intro c hm
  cases c with
  | ok cAcc =>
    cases h0 : cAcc.spans[0]? with
    | none =>
      have hba := hm.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        [dashRange] emptyAcc cAcc rfl dashRange (by simp) 0 (by simp [dashRange]) (by simp [dashRange])
      rcases hba with (⟨sb, eb, v, hs, hlt, h1, h2⟩ | ⟨p, _, hp2, _, _, hws⟩) | ⟨_, _, _, ho, _⟩
      · have hsb : sb = 0 := by omega
        subst hsb
        rw [h0] at hs
        contradiction
      · have hpb : p.byteIdx = 0 := by omega
        have hp : p = ⟨0⟩ := by cases p; cases hpb; rfl
        subst hp
        have hws0 : (String.Pos.Raw.get "--" ⟨0⟩).isWhitespace = true := hws
        have hfalse : (String.Pos.Raw.get "--" ⟨0⟩).isWhitespace = false := by decide
        rw [hfalse] at hws0
        contradiction
      · cases ho
    | some p =>
      rcases p with ⟨eb, v⟩
      rcases hm.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))))
          [] emptyAcc cAcc rfl 0 eb v h0 with hbad | ⟨r, hr, _⟩
      · simp [emptyAcc] at hbad
      · cases hr
  | error msg =>
    have href := hm.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      [] emptyAcc msg rfl
    cases href

theorem collectRanges_healthy_nonempty :
    ∃ ranges acc, Healthy.Collect ranges acc :=
  ⟨[], emptyAcc, _, .nil⟩

theorem collectRanges_negative_external_model :
    ∃ (f : CollectRangesFn), ∃ ranges acc,
      (∀ rs a a', f rs a = .ok a' → ∀ r ∈ rs, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
        ByteAccounted r.ctx r.stx a' r.prevPos.byteIdx r.nextPos.byteIdx b) ∧
      Healthy.Collect ranges acc ∧
      ¬ ∃ acc', f ranges acc = .ok acc' := by
  refine ⟨fun _ _ => .error "denied", [], emptyAcc, ?_, ⟨_, .nil⟩, ?_⟩
  · intro _ _ _ h; contradiction
  · intro ⟨_, h⟩; contradiction

theorem collect_reason_classified :
    ∀ f ranges acc msg, collectRangesRecord.Meets f → f ranges acc = .error msg →
      CollectRefusal ranges acc ∧ ¬ Healthy.Collect ranges acc := by
  intro f ranges acc msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    ranges acc msg herr
  exact ⟨href, fun hh => collectRefusal_contradicts_healthy href hh⟩

end NoCommentsSpecification.AdequacyCollect
