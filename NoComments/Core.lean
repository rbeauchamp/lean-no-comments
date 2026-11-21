module

public import Lean.Parser.Command
public import Lean.Parser.StrInterpolation
public import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

open Lean

namespace NoComments.Core

public section

structure Comment where
  kind : String
  startLine : Nat
  endLine : Nat
  fingerprint : String
  deriving @[expose] Repr, @[expose] BEq, @[expose] DecidableEq

structure CommentAcc where
  spans : Std.HashMap Nat (Nat × Comment) := {}

@[expose] def commentKinds : List String := ["line", "block", "doc", "moddoc"]

@[expose] def fingerprint (text : String) : String :=
  let h := text.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211)
    (14695981039346656037 : UInt64)
  let digits := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

@[expose] def isFingerprint (s : String) : Bool :=
  s.length == 16 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

@[expose] def recordSpan (fileMap : FileMap) (kind : String) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  let sb := startPos.byteIdx
  let eb := stopPos.byteIdx
  if eb ≤ sb then
    .error s!"empty comment span at byte {sb}"
  else
    match acc.spans[sb]? with
    | some (prevStop, prev) =>
      if prevStop == eb && prev.kind == kind then .ok acc
      else .error s!"inconsistent overlapping comment span at byte {sb}"
    | none =>
      let lastPos := String.Pos.Raw.prev fileMap.source stopPos
      let text := (⟨fileMap.source, startPos, stopPos⟩ : Substring.Raw).toString
      .ok { spans := acc.spans.insert sb (eb,
        { kind, startLine := (fileMap.toPosition startPos).line,
          endLine := (fileMap.toPosition lastPos).line, fingerprint := fingerprint text }) }

theorem recordSpan_preserves (fileMap : FileMap) (kind : String)
    (startPos stopPos : String.Pos.Raw) (acc acc' : CommentAcc)
    (h : recordSpan fileMap kind startPos stopPos acc = .ok acc') :
    ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c) := by
  intro s e c hs
  simp only [recordSpan] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; exact hs
      · cases h
    · cases h
      rename_i hnone
      have hne : startPos.byteIdx ≠ s := by
        intro heq
        subst heq
        rw [hnone] at hs
        cases hs
      simp [Std.HashMap.getElem?_insert, hne, hs]

theorem recordSpan_recorded (fileMap : FileMap) (kind : String)
    (startPos stopPos : String.Pos.Raw) (acc acc' : CommentAcc)
    (h : recordSpan fileMap kind startPos stopPos acc = .ok acc') :
    startPos.byteIdx < stopPos.byteIdx ∧
      ∃ (c : Comment), acc'.spans[startPos.byteIdx]? = some (stopPos.byteIdx, c) := by
  simp only [recordSpan] at h
  split at h
  · cases h
  · rename_i hnotle
    have hlt : startPos.byteIdx < stopPos.byteIdx := Nat.lt_of_not_le hnotle
    refine ⟨hlt, ?_⟩
    split at h
    · rename_i prevStop prev hsome
      split at h
      · rename_i heq
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        exact ⟨prev, by rw [← heq.1]; exact hsome⟩
      · cases h
    · cases h
      exact ⟨_, Std.HashMap.getElem?_insert_self⟩

@[expose] def toEol (str : String) (stopPos p : String.Pos.Raw) : String.Pos.Raw :=
  if _h : p < stopPos then
    if String.Pos.Raw.get str p == '\n' then p
    else toEol str stopPos (String.Pos.Raw.next str p)
  else stopPos
termination_by stopPos.byteIdx - p.byteIdx
decreasing_by
  have hlt := String.Pos.Raw.byteIdx_lt_byteIdx_next str p
  have hle : p.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp _h
  omega

theorem toEol_bounds (str : String) (stopPos p : String.Pos.Raw) (hp : p ≤ stopPos) :
    p ≤ toEol str stopPos p ∧ toEol str stopPos p ≤ stopPos := by
  unfold toEol
  split
  · rename_i hlt
    split
    · exact ⟨Std.le_refl _, String.Pos.Raw.le_iff.mpr (Nat.le_of_lt (String.Pos.Raw.lt_iff.mp hlt))⟩
    · have hstep : p.byteIdx < (String.Pos.Raw.next str p).byteIdx :=
        String.Pos.Raw.byteIdx_lt_byteIdx_next str p
      by_cases hnext : String.Pos.Raw.next str p ≤ stopPos
      · have ih := toEol_bounds str stopPos (String.Pos.Raw.next str p) hnext
        exact ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (Nat.le_of_lt hstep) (String.Pos.Raw.le_iff.mp ih.1)), ih.2⟩
      · have hge : ¬ (String.Pos.Raw.next str p < stopPos) := fun hlt' =>
          hnext (String.Pos.Raw.le_iff.mpr (Nat.le_of_lt (String.Pos.Raw.lt_iff.mp hlt')))
        have heq : toEol str stopPos (String.Pos.Raw.next str p) = stopPos := by
          unfold toEol; simp [hge]
        rw [heq]
        exact ⟨hp, Std.le_refl _⟩
  · exact ⟨hp, Std.le_refl _⟩
termination_by stopPos.byteIdx - p.byteIdx
decreasing_by
  have hle : p.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
  omega

@[expose] def finishBlock (str : String) (stopPos : String.Pos.Raw) (nesting : Nat)
    (pos : String.Pos.Raw) : Except String String.Pos.Raw :=
  if h : pos < stopPos then
    let c := String.Pos.Raw.get str pos
    let next := String.Pos.Raw.next str pos
    if c == '-' && next < stopPos && String.Pos.Raw.get str next == '/' then
      let after := String.Pos.Raw.next str next
      if after ≤ stopPos then
        if nesting == 1 then .ok after
        else finishBlock str stopPos (nesting - 1) after
      else
        .error "unterminated block comment in Lean parser trivia"
    else if c == '/' && next < stopPos && String.Pos.Raw.get str next == '-' then
      let after := String.Pos.Raw.next str next
      if after ≤ stopPos then
        finishBlock str stopPos (nesting + 1) after
      else
        .error "unterminated block comment in Lean parser trivia"
    else
      finishBlock str stopPos nesting next
  else
    .error "unterminated block comment in Lean parser trivia"
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next str pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp h
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    change stopPos.byteIdx - (String.Pos.Raw.next str (String.Pos.Raw.next str pos)).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega
  · change stopPos.byteIdx - (String.Pos.Raw.next str pos).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega

theorem finishBlock_bounds (str : String) (stopPos : String.Pos.Raw) (nesting : Nat)
    (pos endPos : String.Pos.Raw) (h : finishBlock str stopPos nesting pos = .ok endPos) :
    pos < endPos ∧ endPos ≤ stopPos := by
  unfold finishBlock at h
  dsimp only at h
  split at h
  · rename_i hlt
    have h1 := String.Pos.Raw.byteIdx_lt_byteIdx_next str pos
    have h2 := String.Pos.Raw.byteIdx_lt_byteIdx_next str (String.Pos.Raw.next str pos)
    split at h
    · split at h
      · rename_i hafter
        split at h
        · cases h
          exact ⟨String.Pos.Raw.lt_iff.mpr (Nat.lt_trans h1 h2), hafter⟩
        · have ih := finishBlock_bounds str stopPos (nesting - 1)
            (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos h
          exact ⟨String.Pos.Raw.lt_iff.mpr (Nat.lt_trans (Nat.lt_trans h1 h2) (String.Pos.Raw.lt_iff.mp ih.1)), ih.2⟩
      · cases h
    · split at h
      · split at h
        · have ih := finishBlock_bounds str stopPos (nesting + 1)
            (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos h
          exact ⟨String.Pos.Raw.lt_iff.mpr (Nat.lt_trans (Nat.lt_trans h1 h2) (String.Pos.Raw.lt_iff.mp ih.1)), ih.2⟩
        · cases h
      · have ih := finishBlock_bounds str stopPos nesting (String.Pos.Raw.next str pos) endPos h
        exact ⟨String.Pos.Raw.lt_iff.mpr (Nat.lt_trans h1 (String.Pos.Raw.lt_iff.mp ih.1)), ih.2⟩
  · cases h
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
    omega

@[expose] def scanTriviaGo (fileMap : FileMap) (stopPos pos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  if _h : pos < stopPos then
    let str := fileMap.source
    let c := String.Pos.Raw.get str pos
    let next := String.Pos.Raw.next str pos
    if c.isWhitespace then
      if next ≤ stopPos then
        scanTriviaGo fileMap stopPos next acc
      else
        .error "whitespace character crosses slice boundary"
    else if c == '-' && next < stopPos && String.Pos.Raw.get str next == '-' then
      let after := String.Pos.Raw.next str next
      if _ha : after ≤ stopPos then
        let eol := toEol str stopPos after
        match recordSpan fileMap "line" pos eol acc with
        | .ok acc' => scanTriviaGo fileMap stopPos eol acc'
        | .error e => .error e
      else
        .error "comment opener crosses slice boundary"
    else if c == '/' && next < stopPos && String.Pos.Raw.get str next == '-' then
      let afterOpen := String.Pos.Raw.next str next
      if afterOpen < stopPos then
        let third := String.Pos.Raw.get str afterOpen
        if third == '-' || third == '!' then
          .error "unexpected doc comment opener in Lean parser trivia"
        else
          let bodyStart := String.Pos.Raw.next str afterOpen
          if bodyStart ≤ stopPos then
            match _hfb : finishBlock str stopPos 1 bodyStart with
            | .error e => .error e
            | .ok endPos =>
              match recordSpan fileMap "block" pos endPos acc with
              | .ok acc' => scanTriviaGo fileMap stopPos endPos acc'
              | .error e => .error e
          else
            .error "unterminated block comment in Lean parser trivia"
      else
        .error "unterminated block comment in Lean parser trivia"
    else
      .error s!"unexpected non-whitespace character {repr c} at byte {pos.byteIdx} in Lean parser trivia"
  else
    .ok acc
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hlt1 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source pos
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp _h
  · change stopPos.byteIdx - (String.Pos.Raw.next fileMap.source pos).byteIdx < stopPos.byteIdx - pos.byteIdx
    omega
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source pos)
    have hleEol := (toEol_bounds fileMap.source stopPos (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) _ha).1
    have ha' : (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)).byteIdx ≤
        (toEol fileMap.source stopPos (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx :=
      String.Pos.Raw.le_iff.mp hleEol
    change stopPos.byteIdx -
        (toEol fileMap.source stopPos (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx <
      stopPos.byteIdx - pos.byteIdx
    omega
  · have hlt2 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source pos)
    have hlt3 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))
    have hfbB := (finishBlock_bounds fileMap.source stopPos 1
      (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))) endPos _hfb).1
    have hltEnd : (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx < endPos.byteIdx :=
      String.Pos.Raw.lt_iff.mp hfbB
    omega

@[expose] def scanTrivia (fileMap : FileMap) (sub : Substring.Raw) (acc : CommentAcc) :
    Except String CommentAcc :=
  scanTriviaGo fileMap sub.stopPos sub.startPos acc

@[expose] def TriviaByteCovered (str : String) (acc : CommentAcc) (lo hi b : Nat) : Prop :=
  (∃ (sb eb : Nat) (c : Comment), acc.spans[sb]? = some (eb, c) ∧ sb < eb ∧ sb ≤ b ∧ b < eb) ∨
  (∃ p : String.Pos.Raw, lo ≤ p.byteIdx ∧ p.byteIdx ≤ b ∧
    b < (String.Pos.Raw.next str p).byteIdx ∧ (String.Pos.Raw.next str p).byteIdx ≤ hi ∧
    (String.Pos.Raw.get str p).isWhitespace = true)

theorem triviaByteCovered_mono {str : String} {acc acc' : CommentAcc} {lo lo' hi hi' b : Nat}
    (hmono : ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c))
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (hcov : TriviaByteCovered str acc lo hi b) :
    TriviaByteCovered str acc' lo' hi' b := by
  rcases hcov with ⟨sb, eb, c, hs, hlt, h1, h2⟩ | ⟨p, h1, h2, h3, h4, hws⟩
  · exact Or.inl ⟨sb, eb, c, hmono sb eb c hs, hlt, h1, h2⟩
  · exact Or.inr ⟨p, Nat.le_trans hlo h1, h2, h3, Nat.le_trans h4 hhi, hws⟩

theorem scanTriviaGo_spec (fileMap : FileMap) (stopPos pos : String.Pos.Raw)
    (acc acc' : CommentAcc) (h : scanTriviaGo fileMap stopPos pos acc = .ok acc') :
    (∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c)) ∧
      (∀ b, pos.byteIdx ≤ b → b < stopPos.byteIdx →
        TriviaByteCovered fileMap.source acc' pos.byteIdx stopPos.byteIdx b) := by
  unfold scanTriviaGo at h
  dsimp only at h
  split at h
  · rename_i hlt
    have h1 := String.Pos.Raw.byteIdx_lt_byteIdx_next fileMap.source pos
    split at h
    · rename_i hws
      split at h
      · rename_i hnext
        have ih := scanTriviaGo_spec fileMap stopPos (String.Pos.Raw.next fileMap.source pos) acc acc' h
        refine ⟨ih.1, ?_⟩
        intro b hb1 hb2
        by_cases hb : b < (String.Pos.Raw.next fileMap.source pos).byteIdx
        · exact Or.inr ⟨pos, Nat.le_refl _, hb1, hb, String.Pos.Raw.le_iff.mp hnext, hws⟩
        · exact triviaByteCovered_mono (fun _ _ _ hs => hs) (Nat.le_of_lt h1) (Nat.le_refl _)
            (ih.2 b (Nat.le_of_not_lt hb) hb2)
      · cases h
    · split at h
      · split at h
        · rename_i ha
          split at h
          · rename_i acc1 hrec
            have hpres1 := recordSpan_preserves fileMap "line" pos _ acc acc1 hrec
            have hrecM := recordSpan_recorded fileMap "line" pos _ acc acc1 hrec
            have ih := scanTriviaGo_spec fileMap stopPos _ acc1 acc' h
            refine ⟨fun s e c hs => ih.1 s e c (hpres1 s e c hs), ?_⟩
            intro b hb1 hb2
            by_cases hb : b < (toEol fileMap.source stopPos (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))).byteIdx
            · rcases hrecM with ⟨hltSpan, c', hc'⟩
              exact Or.inl ⟨pos.byteIdx, _, c', ih.1 _ _ c' hc', hltSpan, hb1, hb⟩
            · exact triviaByteCovered_mono (fun _ _ _ hs => hs) (Nat.le_of_lt hrecM.1) (Nat.le_refl _)
                (ih.2 b (Nat.le_of_not_lt hb) hb2)
          · cases h
        · cases h
      · split at h
        · split at h
          · split at h
            · cases h
            · split at h
              · split at h
                · cases h
                · rename_i endPos hfb
                  split at h
                  · rename_i acc1 hrec
                    have hpres1 := recordSpan_preserves fileMap "block" pos endPos acc acc1 hrec
                    have hrecM := recordSpan_recorded fileMap "block" pos endPos acc acc1 hrec
                    have ih := scanTriviaGo_spec fileMap stopPos endPos acc1 acc' h
                    refine ⟨fun s e c hs => ih.1 s e c (hpres1 s e c hs), ?_⟩
                    intro b hb1 hb2
                    by_cases hb : b < endPos.byteIdx
                    · rcases hrecM with ⟨hltSpan, c', hc'⟩
                      exact Or.inl ⟨pos.byteIdx, endPos.byteIdx, c', ih.1 pos.byteIdx endPos.byteIdx c' hc', hltSpan, hb1, hb⟩
                    · exact triviaByteCovered_mono (fun _ _ _ hs => hs) (Nat.le_of_lt hrecM.1) (Nat.le_refl _)
                        (ih.2 b (Nat.le_of_not_lt hb) hb2)
                  · cases h
              · cases h
          · cases h
        · cases h
  · cases h
    refine ⟨fun _ _ _ hs => hs, ?_⟩
    intro b hb1 hb2
    exfalso
    rename_i hge
    have hle : stopPos.byteIdx ≤ pos.byteIdx := Nat.le_of_not_lt fun hlt' => hge (String.Pos.Raw.lt_iff.mpr hlt')
    omega
termination_by stopPos.byteIdx - pos.byteIdx
decreasing_by
  all_goals
    have hle : pos.byteIdx < stopPos.byteIdx := String.Pos.Raw.lt_iff.mp (by assumption)
    omega

theorem scanTrivia_preserves (fileMap : FileMap) (sub : Substring.Raw) (acc acc' : CommentAcc)
    (h : scanTrivia fileMap sub acc = .ok acc') :
    ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c) :=
  (scanTriviaGo_spec fileMap sub.stopPos sub.startPos acc acc' h).1

theorem scanTrivia_coverage (fileMap : FileMap) (sub : Substring.Raw) (acc acc' : CommentAcc)
    (h : scanTrivia fileMap sub acc = .ok acc') :
    ∀ b, sub.startPos.byteIdx ≤ b → b < sub.stopPos.byteIdx →
      TriviaByteCovered fileMap.source acc' sub.startPos.byteIdx sub.stopPos.byteIdx b :=
  (scanTriviaGo_spec fileMap sub.stopPos sub.startPos acc acc' h).2

@[expose] def checkSlice (fileMap : FileMap) (startPos stopPos : String.Pos.Raw)
    (acc : CommentAcc) : Except String CommentAcc :=
  if startPos < stopPos then
    scanTrivia fileMap ⟨fileMap.source, startPos, stopPos⟩ acc
  else
    .ok acc

theorem checkSlice_preserves (fileMap : FileMap) (startPos stopPos : String.Pos.Raw)
    (acc acc' : CommentAcc) (h : checkSlice fileMap startPos stopPos acc = .ok acc') :
    ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c) := by
  simp only [checkSlice] at h
  split at h
  · exact scanTrivia_preserves fileMap ⟨fileMap.source, startPos, stopPos⟩ acc acc' h
  · cases h; exact fun _ _ _ hs => hs

theorem checkSlice_coverage (fileMap : FileMap) (startPos stopPos : String.Pos.Raw)
    (acc acc' : CommentAcc) (h : checkSlice fileMap startPos stopPos acc = .ok acc') :
    ∀ b, startPos.byteIdx ≤ b → b < stopPos.byteIdx →
      TriviaByteCovered fileMap.source acc' startPos.byteIdx stopPos.byteIdx b := by
  intro b hb1 hb2
  simp only [checkSlice] at h
  split at h
  · exact scanTrivia_coverage fileMap ⟨fileMap.source, startPos, stopPos⟩ acc acc' h b hb1 hb2
  · rename_i hnotlt
    exfalso
    exact hnotlt (String.Pos.Raw.lt_iff.mpr (Nat.lt_of_le_of_lt hb1 hb2))

@[expose] def matchesLiteralToken (env : Environment) (token : Syntax) (raw : String) : Bool := Id.run do
  let parse (p : Parser.ParserFn) (input : String) : Option Syntax := do
    let s := p.run (Parser.InputContext.mk input "<token>") { env, options := {} } {}
      (Parser.mkParserState input)
    guard (!s.hasError && s.stackSize == 1)
    return s.stxStack.back
  match token with
  | .ident _ spelling .. =>
    let some (.ident _ parsed ..) := parse (Parser.tokenFn []) raw | return false
    return spelling.toString == raw && parsed.toString == raw
  | .node _ k _ =>
    unless token.isLit? k == some raw do return false
    if k == interpolatedStrLitKind then
      let chunk := if raw.startsWith "}" then "\"" ++ (raw.drop 1).toString else raw
      let emptyHole : Parser.ParserFn := fun _ s => s.pushSyntax .missing
      let some parsed := parse (Parser.interpolatedStrFn emptyHole) (chunk ++ "}\"") | return false
      return parsed[0].isLit? k == some chunk
    return ((parse (Parser.tokenFn []) raw).bind (·.isLit? k)) == some raw
  | _ => return false

@[expose] def containsOpener (raw : String) : Bool :=
  raw.contains "--" || raw.contains "/-"

@[expose] def crossesBoundary (raw : String) (next : Char) : Bool :=
  next == '-' && (raw.endsWith "-" || raw.endsWith "/")

@[expose] def matchesRegisteredSymbol (ctx : Parser.ParserContextCore) (token : Syntax) : Bool := Id.run do
  let leaf := match token with
    | .node _ _ #[arg] => arg
    | _ => token
  let .atom (.original _ start _ stop) spelling := leaf | return false
  let parsed := (Parser.symbolFn spelling).run ctx.toInputContext ctx.toParserModuleContext ctx.tokens
    { pos := start, cache := Parser.initCacheForInput ctx.inputString }
  return !parsed.hasError && parsed.stackSize == 1 && parsed.stxStack.back.getTailPos? == some stop

@[expose] def checkToken (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char)
    (start : String.Pos.Raw) : Except String Unit :=
  if (containsOpener raw || crossesBoundary raw next) &&
      !matchesLiteralToken ctx.env token raw &&
      !matchesRegisteredSymbol ctx token then
    .error s!"cannot account for a possible comment in the parser token at byte {start.byteIdx}"
  else .ok ()

theorem checkToken_ok_iff (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char)
    (start : String.Pos.Raw) :
    checkToken ctx token raw next start = .ok () ↔
      matchesLiteralToken ctx.env token raw = true ∨
      matchesRegisteredSymbol ctx token = true ∨
      (containsOpener raw = false ∧ crossesBoundary raw next = false) := by
  simp only [checkToken]
  split <;> simp_all <;> grind

@[expose] def consumeRange (fileMap : FileMap) (nextPos pos start stop : String.Pos.Raw)
    (account : CommentAcc → Except String CommentAcc) (acc : CommentAcc) :
    Except String (String.Pos.Raw × CommentAcc) :=
  if pos ≤ start && start ≤ stop && stop ≤ nextPos then
    match checkSlice fileMap pos start acc with
    | .error e => .error e
    | .ok acc1 =>
      match account acc1 with
      | .error e => .error e
      | .ok acc2 => .ok (stop, acc2)
  else
    .error s!"source range [{start.byteIdx}, {stop.byteIdx}) outside unread bytes [{pos.byteIdx}, {nextPos.byteIdx})"

theorem consumeRange_spec (fileMap : FileMap) (nextPos pos start stop stop' : String.Pos.Raw)
    (account : CommentAcc → Except String CommentAcc) (acc acc' : CommentAcc)
    (h : consumeRange fileMap nextPos pos start stop account acc = .ok (stop', acc')) :
    ∃ acc1,
      pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos ∧ stop' = stop ∧
      checkSlice fileMap pos start acc = .ok acc1 ∧
      account acc1 = .ok acc' := by
  simp only [consumeRange] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    split at h
    · cases h
    · rename_i acc1 hslice
      split at h
      · cases h
      · rename_i acc2 hacc
        cases h
        exact ⟨acc1, hok.1.1, hok.1.2, hok.2, rfl, hslice, hacc⟩
  · cases h

@[expose] def consumeToken (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos start stop : String.Pos.Raw) (acc : CommentAcc) :
    Except String (String.Pos.Raw × CommentAcc) :=
  consumeRange ctx.fileMap nextPos pos start stop (fun a =>
    match checkToken ctx s (ctx.extract start stop) (ctx.get stop) start with
    | .error e => .error e
    | .ok () => .ok a) acc

@[expose] def isDocCommentKind (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.docComment || k == ``Parser.Command.plainDocComment ||
    k == ``Parser.Command.moduleDoc

mutual

@[expose] def walkSyntax (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos : String.Pos.Raw) (acc : CommentAcc) :
    Except String (String.Pos.Raw × CommentAcc) :=
  match s with
  | .atom (.original _ start _ stop) _ | .ident (.original _ start _ stop) .. =>
    consumeToken ctx nextPos s pos start stop acc
  | .node _ k args =>
    if isDocCommentKind k then
      match s.getHeadInfo?, s.getTailInfo? with
      | some (.original _ start ..), some (.original _ _ _ stop) =>
        let kind := if k == ``Parser.Command.moduleDoc then "moddoc" else "doc"
        consumeRange ctx.fileMap nextPos pos start stop (recordSpan ctx.fileMap kind start stop) acc
      | some (.original _ _start ..), _ => .error "docstring has no original end"
      | _, _ => .error "docstring has no original start"
    else if k == choiceKind then
      match args with
      | .mk [] => .error "empty parser choice"
      | .mk (first :: alts) => do
        let (stop, acc) ← walkSyntax ctx nextPos first pos acc
        let acc ← checkAlts ctx nextPos pos stop alts acc
        return (stop, acc)
    else
      match args with
      | .mk [] => walkList ctx nextPos [] pos acc
      | .mk (a :: b :: rest) => walkList ctx nextPos (a :: b :: rest) pos acc
      | .mk [.atom (.original _ start _ stop) _] =>
        consumeToken ctx nextPos s pos start stop acc
      | .mk [arg] => walkList ctx nextPos [arg] pos acc
  | _ => .ok (pos, acc)
termination_by sizeOf s

@[expose] def checkAlts (ctx : Parser.ParserContextCore) (nextPos pos stop : String.Pos.Raw)
    (alts : List Syntax) (acc : CommentAcc) : Except String CommentAcc :=
  match alts with
  | [] => .ok acc
  | alt :: rest => do
    let (altStop, altAcc) ← walkSyntax ctx nextPos alt pos acc
    if altStop == stop then
      checkAlts ctx nextPos pos stop rest altAcc
    else
      .error "parser alternatives cover different source ranges"
termination_by sizeOf alts

@[expose] def walkList (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (args : List Syntax) (pos : String.Pos.Raw) (acc : CommentAcc) :
    Except String (String.Pos.Raw × CommentAcc) :=
  match args with
  | [] => .ok (pos, acc)
  | arg :: rest => do
    let (pos', acc') ← walkSyntax ctx nextPos arg pos acc
    walkList ctx nextPos rest pos' acc'
termination_by sizeOf args

end

@[expose] def collectSyntax (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw)
    (stx : Syntax) (acc : CommentAcc) : Except String CommentAcc :=
  if prevPos ≤ nextPos && nextPos ≤ ctx.endPos then
    match walkSyntax ctx nextPos stx prevPos acc with
    | .error e => .error e
    | .ok (pos, acc1) => checkSlice ctx.fileMap pos nextPos acc1
  else
    .error "Lean's parser returned an invalid command range"

inductive OriginalLeafIn : Syntax → Syntax → String.Pos.Raw → String.Pos.Raw → Prop where
  | atom (info : SourceInfo) (val : String) (leading trail : Substring.Raw)
      (start stop : String.Pos.Raw)
      (hinfo : info = .original leading start trail stop) :
      OriginalLeafIn (.atom info val) (.atom info val) start stop
  | ident (info : SourceInfo) (rawVal : Substring.Raw) (val : Name)
      (preresolved : List Syntax.Preresolved) (leading trail : Substring.Raw)
      (start stop : String.Pos.Raw)
      (hinfo : info = .original leading start trail stop) :
      OriginalLeafIn (.ident info rawVal val preresolved) (.ident info rawVal val preresolved) start stop
  | singletonAtomNode (info : SourceInfo) (k : SyntaxNodeKind)
      (atomInfo : SourceInfo) (val : String) (leading trail : Substring.Raw)
      (start stop : String.Pos.Raw)
      (hnotDoc : isDocCommentKind k = false) (hnotChoice : k ≠ choiceKind)
      (hinfo : atomInfo = .original leading start trail stop) :
      OriginalLeafIn (.node info k (.mk [.atom atomInfo val])) (.node info k (.mk [.atom atomInfo val])) start stop
  | child (info : SourceInfo) (k : SyntaxNodeKind) (args : Array Syntax)
      (arg leaf : Syntax) (start stop : String.Pos.Raw)
      (hmem : arg ∈ args.toList)
      (hchild : OriginalLeafIn arg leaf start stop) :
      OriginalLeafIn (.node info k args) leaf start stop

@[expose] def ByteAccounted (ctx : Parser.ParserContextCore) (stx : Syntax)
    (acc : CommentAcc) (lo hi b : Nat) : Prop :=
  TriviaByteCovered ctx.fileMap.source acc lo hi b ∨
  (∃ leaf start stop, OriginalLeafIn stx leaf start stop ∧
    lo ≤ start.byteIdx ∧ start.byteIdx ≤ b ∧ b < stop.byteIdx ∧ stop.byteIdx ≤ hi ∧
    checkToken ctx leaf (ctx.extract start stop) (ctx.get stop) start = .ok ())

theorem byteAccounted_mono {ctx : Parser.ParserContextCore} {stx stx' : Syntax}
    {acc acc' : CommentAcc} {lo lo' hi hi' b : Nat}
    (hmono : ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c))
    (hleaf : ∀ leaf start stop, OriginalLeafIn stx leaf start stop → OriginalLeafIn stx' leaf start stop)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (hcov : ByteAccounted ctx stx acc lo hi b) :
    ByteAccounted ctx stx' acc' lo' hi' b := by
  rcases hcov with htriv | ⟨leaf, start, stop, hIn, h1, h2, h3, h4, htok⟩
  · exact Or.inl (triviaByteCovered_mono hmono hlo hhi htriv)
  · exact Or.inr ⟨leaf, start, stop, hleaf leaf start stop hIn,
      Nat.le_trans hlo h1, h2, h3, Nat.le_trans h4 hhi, htok⟩

theorem consumeToken_spec (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos start stop stop' : String.Pos.Raw) (acc acc' : CommentAcc)
    (hleaf : OriginalLeafIn s s start stop)
    (h : consumeToken ctx nextPos s pos start stop acc = .ok (stop', acc')) :
    pos ≤ stop' ∧ stop' ≤ nextPos ∧ stop' = stop ∧
      (∀ (sb eb : Nat) (c : Comment), acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c)) ∧
      (∀ b, pos.byteIdx ≤ b → b < stop'.byteIdx →
        ByteAccounted ctx s acc' pos.byteIdx stop'.byteIdx b) := by
  rcases consumeRange_spec ctx.fileMap nextPos pos start stop stop' _ acc acc' h with
    ⟨acc1, h1, h2, h3, hstop, hslice, hacc⟩
  split at hacc
  · cases hacc
  · rename_i htok
    cases hacc
    subst hstop
    refine ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
      h3, rfl, checkSlice_preserves ctx.fileMap pos start acc acc' hslice, ?_⟩
    intro b hb1 hb2
    by_cases hlt : b < start.byteIdx
    · have htriv := checkSlice_coverage ctx.fileMap pos start acc acc' hslice b hb1 hlt
      exact Or.inl (triviaByteCovered_mono (fun _ _ _ hs => hs) (Nat.le_refl _) (String.Pos.Raw.le_iff.mp h2) htriv)
    · have hb' : start.byteIdx ≤ b := Nat.le_of_not_lt hlt
      exact Or.inr ⟨s, start, stop', hleaf, String.Pos.Raw.le_iff.mp h1, hb', hb2, Nat.le_refl _, htok⟩

mutual

theorem walk_spec (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (s : Syntax) (pos stop : String.Pos.Raw) (acc acc' : CommentAcc)
    (hpos : pos ≤ nextPos)
    (h : walkSyntax ctx nextPos s pos acc = .ok (stop, acc')) :
    pos ≤ stop ∧ stop ≤ nextPos ∧
      (∀ (sb eb : Nat) (c : Comment), acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c)) ∧
      (∀ b, pos.byteIdx ≤ b → b < stop.byteIdx →
        ByteAccounted ctx s acc' pos.byteIdx stop.byteIdx b) := by
  cases s with
  | missing =>
    simp only [walkSyntax] at h
    cases h
    refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
    intro b hb1 hb2; omega
  | atom info val =>
    cases info with
    | original leading start trail stop0 =>
      simp only [walkSyntax] at h
      have hs := consumeToken_spec ctx nextPos (.atom (.original leading start trail stop0) val)
        pos start stop0 stop acc acc' (OriginalLeafIn.atom _ val leading trail start stop0 rfl) h
      exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
    | synthetic _ _ =>
      simp only [walkSyntax] at h; cases h
      refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
      intro b hb1 hb2; omega
    | none =>
      simp only [walkSyntax] at h; cases h
      refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
      intro b hb1 hb2; omega
  | ident info rawVal val pre =>
    cases info with
    | original leading start trail stop0 =>
      simp only [walkSyntax] at h
      have hs := consumeToken_spec ctx nextPos (.ident (.original leading start trail stop0) rawVal val pre)
        pos start stop0 stop acc acc' (OriginalLeafIn.ident _ rawVal val pre leading trail start stop0 rfl) h
      exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
    | synthetic _ _ =>
      simp only [walkSyntax] at h; cases h
      refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
      intro b hb1 hb2; omega
    | none =>
      simp only [walkSyntax] at h; cases h
      refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
      intro b hb1 hb2; omega
  | node info k args =>
    unfold walkSyntax at h
    by_cases hdoc : isDocCommentKind k = true
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
              rcases consumeRange_spec ctx.fileMap nextPos pos start stop0 stop _ acc acc' h with
                ⟨acc1, h1, h2, h3, hstop, hslice, hrec⟩
              subst hstop
              have hpres1 := checkSlice_preserves ctx.fileMap pos start acc acc1 hslice
              have hpres2 := recordSpan_preserves ctx.fileMap _ start stop acc1 acc' hrec
              have hrecM := recordSpan_recorded ctx.fileMap _ start stop acc1 acc' hrec
              refine ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp h1) (String.Pos.Raw.le_iff.mp h2)),
                h3, fun s e c hs => hpres2 s e c (hpres1 s e c hs), ?_⟩
              intro b hb1 hb2
              by_cases hlt : b < start.byteIdx
              · have htriv := checkSlice_coverage ctx.fileMap pos start acc acc1 hslice b hb1 hlt
                exact Or.inl (triviaByteCovered_mono hpres2 (Nat.le_refl _) (String.Pos.Raw.le_iff.mp h2) htriv)
              · have hb' : start.byteIdx ≤ b := Nat.le_of_not_lt hlt
                rcases hrecM with ⟨hltSpan, c', hc'⟩
                exact Or.inl (Or.inl ⟨start.byteIdx, stop.byteIdx, c', hc', hltSpan, hb', hb2⟩)
    · have hdocF : isDocCommentKind k = false := Bool.eq_false_iff.mpr hdoc
      by_cases hch : k = choiceKind
      · have hchT : (k == choiceKind) = true := beq_iff_eq.mpr hch
        simp only [hdocF, hchT, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil => cases h
          | cons first alts =>
            simp only [bind, Except.bind] at h
            cases hfirst : walkSyntax ctx nextPos first pos acc with
            | error e => rw [hfirst] at h; cases h
            | ok res1 =>
              rcases res1 with ⟨stop1, acc1⟩
              rw [hfirst] at h
              dsimp only at h
              cases halts : checkAlts ctx nextPos pos stop1 alts acc1 with
              | error e => rw [halts] at h; cases h
              | ok acc2 =>
                rw [halts] at h
                dsimp only at h
                cases h
                have ihFirst := walk_spec ctx nextPos first pos stop acc acc1 hpos hfirst
                have hpresAlts := checkAlts_preserves ctx nextPos pos stop alts acc1 acc' hpos halts
                have hmemFirst : first ∈ (Array.mk (first :: alts)).toList := List.mem_cons_self
                refine ⟨ihFirst.1, ihFirst.2.1,
                  fun s e c hs => hpresAlts s e c (ihFirst.2.2.1 s e c hs), ?_⟩
                intro b hb1 hb2
                exact byteAccounted_mono hpresAlts
                  (fun leaf start' stop' hIn => OriginalLeafIn.child info k (.mk (first :: alts)) first leaf start' stop' hmemFirst hIn)
                  (Nat.le_refl _) (Nat.le_refl _) (ihFirst.2.2.2 b hb1 hb2)
      · have hchB : (k == choiceKind) = false := beq_false_of_ne hch
        simp only [hdocF, hchB, Bool.false_eq_true, ↓reduceIte] at h
        cases args with
        | mk l =>
          cases l with
          | nil =>
            dsimp only at h
            exact walkList_spec ctx nextPos info k (.mk []) [] pos stop acc acc'
              (fun _ ha => absurd ha List.not_mem_nil) hpos h
          | cons a1 l1 =>
            cases l1 with
            | cons a2 l2 =>
              dsimp only at h
              exact walkList_spec ctx nextPos info k (.mk (a1 :: a2 :: l2)) (a1 :: a2 :: l2) pos stop acc acc'
                (fun _ ha => ha) hpos h
            | nil =>
              cases a1 with
              | atom infoA valA =>
                cases infoA with
                | original leading start trail stop0 =>
                  dsimp only at h
                  have hs := consumeToken_spec ctx nextPos
                    (.node info k (.mk [.atom (.original leading start trail stop0) valA]))
                    pos start stop0 stop acc acc'
                    (OriginalLeafIn.singletonAtomNode info k (.original leading start trail stop0) valA leading trail start stop0 hdocF hch rfl)
                    h
                  exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
                | synthetic posA endPosA canonicalA =>
                  dsimp only at h
                  exact walkList_spec ctx nextPos info k (.mk [.atom (.synthetic posA endPosA canonicalA) valA])
                    [.atom (.synthetic posA endPosA canonicalA) valA] pos stop acc acc' (fun _ ha => ha) hpos h
                | none =>
                  dsimp only at h
                  exact walkList_spec ctx nextPos info k (.mk [.atom .none valA]) [.atom .none valA]
                    pos stop acc acc' (fun _ ha => ha) hpos h
              | ident infoI rawI valI preI =>
                dsimp only at h
                exact walkList_spec ctx nextPos info k (.mk [.ident infoI rawI valI preI]) [.ident infoI rawI valI preI] pos stop acc acc'
                  (fun _ ha => ha) hpos h
              | node infoN kN argsN =>
                dsimp only at h
                exact walkList_spec ctx nextPos info k (.mk [.node infoN kN argsN]) [.node infoN kN argsN] pos stop acc acc'
                  (fun _ ha => ha) hpos h
              | missing =>
                dsimp only at h
                exact walkList_spec ctx nextPos info k (.mk [.missing]) [.missing] pos stop acc acc'
                  (fun _ ha => ha) hpos h
termination_by (sizeOf s, 1)

theorem checkAlts_preserves (ctx : Parser.ParserContextCore) (nextPos pos stop : String.Pos.Raw)
    (alts : List Syntax) (acc acc' : CommentAcc)
    (hpos : pos ≤ nextPos)
    (h : checkAlts ctx nextPos pos stop alts acc = .ok acc') :
    ∀ (sb eb : Nat) (c : Comment), acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c) := by
  cases alts with
  | nil =>
    simp only [checkAlts] at h; cases h; exact fun _ _ _ hs => hs
  | cons alt rest =>
    simp only [checkAlts, bind, Except.bind] at h
    cases halt : walkSyntax ctx nextPos alt pos acc with
    | error e => rw [halt] at h; cases h
    | ok res =>
      rcases res with ⟨altStop, altAcc⟩
      rw [halt] at h
      by_cases heq : (altStop == stop) = true
      · simp only [heq, ↓reduceIte] at h
        have h1 := walk_spec ctx nextPos alt pos altStop acc altAcc hpos halt
        have h2 := checkAlts_preserves ctx nextPos pos stop rest altAcc acc' hpos h
        intro sb eb c hs
        exact h2 sb eb c (h1.2.2.1 sb eb c hs)
      · have hne : (altStop == stop) = false := Bool.eq_false_iff.mpr heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
        cases h
termination_by (sizeOf alts, 0)

theorem walkList_spec (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw)
    (info : SourceInfo) (k : SyntaxNodeKind) (args : Array Syntax)
    (l : List Syntax) (pos stop : String.Pos.Raw) (acc acc' : CommentAcc)
    (hsub : ∀ a, a ∈ l → a ∈ args.toList)
    (hpos : pos ≤ nextPos)
    (h : walkList ctx nextPos l pos acc = .ok (stop, acc')) :
    pos ≤ stop ∧ stop ≤ nextPos ∧
      (∀ (sb eb : Nat) (c : Comment), acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c)) ∧
      (∀ b, pos.byteIdx ≤ b → b < stop.byteIdx →
        ByteAccounted ctx (.node info k args) acc' pos.byteIdx stop.byteIdx b) := by
  cases l with
  | nil =>
    simp only [walkList] at h; cases h
    refine ⟨Std.le_refl _, hpos, fun _ _ _ hs => hs, ?_⟩
    intro b hb1 hb2; omega
  | cons arg rest =>
    simp only [walkList, bind, Except.bind] at h
    cases harg : walkSyntax ctx nextPos arg pos acc with
    | error e => rw [harg] at h; cases h
    | ok res1 =>
      rcases res1 with ⟨pos1, acc1⟩
      rw [harg] at h
      have ih1 := walk_spec ctx nextPos arg pos pos1 acc acc1 hpos harg
      have ih2 := walkList_spec ctx nextPos info k args rest pos1 stop acc1 acc'
        (fun a ha => hsub a (List.mem_cons_of_mem arg ha)) ih1.2.1 h
      refine ⟨String.Pos.Raw.le_iff.mpr (Nat.le_trans (String.Pos.Raw.le_iff.mp ih1.1) (String.Pos.Raw.le_iff.mp ih2.1)),
        ih2.2.1, fun s e c hs => ih2.2.2.1 s e c (ih1.2.2.1 s e c hs), ?_⟩
      intro b hb1 hb2
      by_cases hlt : b < pos1.byteIdx
      · have hIn : arg ∈ args.toList := hsub arg List.mem_cons_self
        exact byteAccounted_mono ih2.2.2.1
          (fun leaf start' stop' hLeaf => OriginalLeafIn.child info k args arg leaf start' stop' hIn hLeaf)
          (Nat.le_refl _) (String.Pos.Raw.le_iff.mp ih2.1) (ih1.2.2.2 b hb1 hlt)
      · have hb' : pos1.byteIdx ≤ b := Nat.le_of_not_lt hlt
        exact byteAccounted_mono (fun _ _ _ hs => hs) (fun _ _ _ hLeaf => hLeaf)
          (String.Pos.Raw.le_iff.mp ih1.1) (Nat.le_refl _) (ih2.2.2.2 b hb' hb2)
termination_by (sizeOf l, 0)

end

theorem collectSyntax_preserves (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw)
    (stx : Syntax) (acc acc' : CommentAcc)
    (h : collectSyntax ctx prevPos nextPos stx acc = .ok acc') :
    ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c) := by
  simp only [collectSyntax] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    cases hw : walkSyntax ctx nextPos stx prevPos acc with
    | error e => rw [hw] at h; cases h
    | ok res =>
      rcases res with ⟨pos, acc1⟩
      rw [hw] at h
      have h1 := walk_spec ctx nextPos stx prevPos pos acc acc1 hok.1 hw
      have h2 := checkSlice_preserves ctx.fileMap pos nextPos acc1 acc' h
      intro s e c hs
      exact h2 s e c (h1.2.2.1 s e c hs)
  · cases h

theorem collectSyntax_coverage (ctx : Parser.ParserContextCore) (prevPos nextPos : String.Pos.Raw)
    (stx : Syntax) (acc acc' : CommentAcc)
    (h : collectSyntax ctx prevPos nextPos stx acc = .ok acc') :
    prevPos ≤ nextPos ∧ nextPos ≤ ctx.endPos ∧
      ∀ b, prevPos.byteIdx ≤ b → b < nextPos.byteIdx →
        ByteAccounted ctx stx acc' prevPos.byteIdx nextPos.byteIdx b := by
  simp only [collectSyntax] at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    cases hw : walkSyntax ctx nextPos stx prevPos acc with
    | error e => rw [hw] at h; cases h
    | ok res =>
      rcases res with ⟨pos, acc1⟩
      rw [hw] at h
      have h1 := walk_spec ctx nextPos stx prevPos pos acc acc1 hok.1 hw
      have h2 := checkSlice_preserves ctx.fileMap pos nextPos acc1 acc' h
      have h3 := checkSlice_coverage ctx.fileMap pos nextPos acc1 acc' h
      refine ⟨hok.1, hok.2, ?_⟩
      intro b hb1 hb2
      by_cases hlt : b < pos.byteIdx
      · exact byteAccounted_mono h2 (fun _ _ _ hIn => hIn)
          (Nat.le_refl _) (String.Pos.Raw.le_iff.mp h1.2.1) (h1.2.2.2 b hb1 hlt)
      · have hb' : pos.byteIdx ≤ b := Nat.le_of_not_lt hlt
        have hcov3 : TriviaByteCovered ctx.fileMap.source acc' pos.byteIdx nextPos.byteIdx b := h3 b hb' hb2
        exact Or.inl (triviaByteCovered_mono (fun _ _ _ hs => hs)
          (String.Pos.Raw.le_iff.mp h1.1) (Nat.le_refl _) hcov3)
  · cases h

structure CommandRange where
  ctx : Parser.ParserContextCore
  prevPos : String.Pos.Raw
  nextPos : String.Pos.Raw
  stx : Syntax

@[expose] def collectRanges (ranges : List CommandRange) (acc : CommentAcc) :
    Except String CommentAcc :=
  match ranges with
  | [] => .ok acc
  | r :: rest => do
    let acc ← collectSyntax r.ctx r.prevPos r.nextPos r.stx acc
    collectRanges rest acc

@[expose] def ContiguousFrom (start endPos : String.Pos.Raw) : List CommandRange → Prop
  | [] => start = endPos
  | r :: rest => r.prevPos = start ∧ ContiguousFrom r.nextPos endPos rest

theorem collectRanges_preserves (ranges : List CommandRange) (acc acc' : CommentAcc)
    (h : collectRanges ranges acc = .ok acc') :
    ∀ (s e : Nat) (c : Comment), acc.spans[s]? = some (e, c) → acc'.spans[s]? = some (e, c) := by
  induction ranges generalizing acc with
  | nil => simp only [collectRanges] at h; cases h; exact fun _ _ _ hs => hs
  | cons r rest ih =>
    simp only [collectRanges, bind, Except.bind] at h
    cases h1 : collectSyntax r.ctx r.prevPos r.nextPos r.stx acc with
    | error e => rw [h1] at h; cases h
    | ok acc1 =>
      rw [h1] at h
      intro s e c hs
      exact ih acc1 h s e c (collectSyntax_preserves r.ctx r.prevPos r.nextPos r.stx acc acc1 h1 s e c hs)

theorem collectRanges_coverage (ranges : List CommandRange) (start endPos : String.Pos.Raw)
    (acc acc' : CommentAcc)
    (hcontig : ContiguousFrom start endPos ranges)
    (h : collectRanges ranges acc = .ok acc') :
    ∀ b, start.byteIdx ≤ b → b < endPos.byteIdx →
      ∃ r ∈ ranges, r.prevPos.byteIdx ≤ b ∧ b < r.nextPos.byteIdx ∧
        ByteAccounted r.ctx r.stx acc' r.prevPos.byteIdx r.nextPos.byteIdx b := by
  induction ranges generalizing start acc with
  | nil =>
    intro b hb1 hb2
    simp only [ContiguousFrom] at hcontig
    subst hcontig
    omega
  | cons r rest ih =>
    intro b hb1 hb2
    simp only [ContiguousFrom] at hcontig
    rcases hcontig with ⟨hprev, hrest⟩
    simp only [collectRanges, bind, Except.bind] at h
    cases h1 : collectSyntax r.ctx r.prevPos r.nextPos r.stx acc with
    | error e => rw [h1] at h; cases h
    | ok acc1 =>
      rw [h1] at h
      have hcov := collectSyntax_coverage r.ctx r.prevPos r.nextPos r.stx acc acc1 h1
      have hpres := collectRanges_preserves rest acc1 acc' h
      by_cases hlt : b < r.nextPos.byteIdx
      · refine ⟨r, List.mem_cons_self, by rw [hprev]; exact hb1, hlt, ?_⟩
        exact byteAccounted_mono hpres (fun _ _ _ hIn => hIn) (Nat.le_refl _) (Nat.le_refl _)
          (hcov.2.2 b (by rw [hprev]; exact hb1) hlt)
      · have hb' : r.nextPos.byteIdx ≤ b := Nat.le_of_not_lt hlt
        rcases ih r.nextPos acc1 hrest h b hb' hb2 with ⟨r', hr'mem, hr'1, hr'2, hr'cov⟩
        exact ⟨r', List.mem_cons_of_mem r hr'mem, hr'1, hr'2, hr'cov⟩

@[expose] def sourceOrder (acc : CommentAcc) : Array Comment :=
  let sorted := acc.spans.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))
  (sorted.map (·.2.2)).toArray

theorem sourceOrder_mem_iff (acc : CommentAcc) (c : Comment) :
    c ∈ (sourceOrder acc).toList ↔ ∃ (sb eb : Nat), acc.spans[sb]? = some (eb, c) := by
  simp only [sourceOrder, List.toList_toArray, List.mem_map]
  constructor
  · rintro ⟨⟨sb, eb, c'⟩, hmem, rfl⟩
    have hmem' := (List.mergeSort_perm acc.spans.toList (fun a b => decide (a.1 ≤ b.1))).mem_iff.mp hmem
    have hget := (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp hmem'
    exact ⟨sb, eb, hget⟩
  · rintro ⟨sb, eb, hget⟩
    have hmem' := (Std.HashMap.mem_toList_iff_getElem?_eq_some).mpr hget
    have hmem := (List.mergeSort_perm acc.spans.toList (fun a b => decide (a.1 ≤ b.1))).mem_iff.mpr hmem'
    exact ⟨(sb, eb, c), hmem, rfl⟩

@[expose] def validIntervals (comments : List Comment) : List (Nat × Nat) :=
  comments.filterMap fun c =>
    if c.startLine ≤ c.endLine then some (c.startLine, c.endLine) else none

@[expose] def leInterval (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

@[expose] def mergeSortedIntervals : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | [x] => [x]
  | (a, b) :: (c, d) :: rest =>
    if c ≤ b + 1 then mergeSortedIntervals ((a, max b d) :: rest)
    else (a, b) :: mergeSortedIntervals ((c, d) :: rest)
termination_by xs => xs.length

@[expose] def expandIntervals : List (Nat × Nat) → List Nat
  | [] => []
  | (a, b) :: rest => List.range' a (b - a + 1) ++ expandIntervals rest

@[expose] def distinctCommentLines (comments : Array Comment) : Nat :=
  let sorted := (validIntervals comments.toList).mergeSort leInterval
  let merged := mergeSortedIntervals sorted
  merged.foldl (fun acc (a, b) => acc + (b - a + 1)) 0

@[expose] def coveredLines (comments : Array Comment) : List Nat :=
  expandIntervals (mergeSortedIntervals ((validIntervals comments.toList).mergeSort leInterval))

theorem foldl_interval_len_eq (xs : List (Nat × Nat)) (init : Nat) :
    xs.foldl (fun acc (a, b) => acc + (b - a + 1)) init = init + (expandIntervals xs).length := by
  induction xs generalizing init with
  | nil => simp [expandIntervals]
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [List.foldl_cons, expandIntervals, List.length_append, List.length_range']
    rw [ih (init + (b - a + 1))]
    omega

theorem distinctCommentLines_eq_length (comments : Array Comment) :
    distinctCommentLines comments = (coveredLines comments).length := by
  simp only [distinctCommentLines, coveredLines]
  rw [foldl_interval_len_eq]
  omega

@[expose] def WellFormedSortedIntervals (xs : List (Nat × Nat)) : Prop :=
  xs.Pairwise (fun p q => p.1 ≤ q.1) ∧ ∀ p ∈ xs, p.1 ≤ p.2

@[expose] def DisjointSortedIntervals (xs : List (Nat × Nat)) : Prop :=
  xs.Pairwise (fun p q => p.2 + 1 < q.1) ∧ ∀ p ∈ xs, p.1 ≤ p.2

theorem fst_mem_expandIntervals {zs : List (Nat × Nat)} {q : Nat × Nat}
    (hq : q ∈ zs) (_hle : q.1 ≤ q.2) :
    q.1 ∈ expandIntervals zs := by
  induction zs with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [expandIntervals, List.mem_append, List.mem_range']
    rcases List.mem_cons.mp hq with rfl | htl
    · left; exact ⟨0, by omega, by omega⟩
    · right; exact ih htl

theorem mergeSortedIntervals_spec (xs : List (Nat × Nat)) (hwf : WellFormedSortedIntervals xs) :
    DisjointSortedIntervals (mergeSortedIntervals xs) ∧
      ∀ l, l ∈ expandIntervals (mergeSortedIntervals xs) ↔ ∃ p ∈ xs, p.1 ≤ l ∧ l ≤ p.2 := by
  match xs with
  | [] =>
    simp [mergeSortedIntervals, DisjointSortedIntervals, expandIntervals]
  | [(a, b)] =>
    have hab : a ≤ b := hwf.2 (a, b) List.mem_cons_self
    refine ⟨⟨by simp [mergeSortedIntervals],
      fun p hp => by simp [mergeSortedIntervals] at hp; subst hp; exact hab⟩, ?_⟩
    intro l
    simp only [mergeSortedIntervals, expandIntervals, List.append_nil, List.mem_range',
      List.mem_singleton, exists_eq_left, Nat.one_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · intro ⟨h1, h2⟩
      exact ⟨l - a, by omega, by omega⟩
  | (a, b) :: (c, d) :: rest =>
    have hpw := List.pairwise_cons.mp hwf.1
    have hac : a ≤ c := hpw.1 (c, d) List.mem_cons_self
    have hab : a ≤ b := hwf.2 (a, b) List.mem_cons_self
    have hcd : c ≤ d := hwf.2 (c, d) (List.mem_cons_of_mem _ List.mem_cons_self)
    have hrestPw : ((c, d) :: rest).Pairwise (fun p q => p.1 ≤ q.1) := hpw.2
    have hrestMem : ∀ p ∈ rest, p.1 ≤ p.2 := fun p hp =>
      hwf.2 p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    by_cases hmerge : c ≤ b + 1
    · have hwf' : WellFormedSortedIntervals ((a, max b d) :: rest) := by
        refine ⟨List.pairwise_cons.mpr ⟨?_, (List.pairwise_cons.mp hrestPw).2⟩, ?_⟩
        · intro p hp
          have hcp : c ≤ p.1 := (List.pairwise_cons.mp hrestPw).1 p hp
          exact Nat.le_trans hac hcp
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact hrestMem p hp
      have ih := mergeSortedIntervals_spec ((a, max b d) :: rest) hwf'
      have heq : mergeSortedIntervals ((a, b) :: (c, d) :: rest) =
          mergeSortedIntervals ((a, max b d) :: rest) := by
        simp [mergeSortedIntervals, hmerge]
      rw [heq]
      refine ⟨ih.1, ?_⟩
      intro l
      rw [ih.2 l]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · by_cases hlb : l ≤ b
          · exact ⟨(a, b), List.mem_cons_self, h1, hlb⟩
          · exact ⟨(c, d), List.mem_cons_of_mem _ List.mem_cons_self, by omega, by omega⟩
        · exact ⟨p, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp), h1, h2⟩
      · rintro ⟨p, hp, h1, h2⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨(a, max b d), List.mem_cons_self, h1, by omega⟩
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨(a, max b d), List.mem_cons_self, Nat.le_trans hac h1, by omega⟩
          · exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩
    · have hwf' : WellFormedSortedIntervals ((c, d) :: rest) :=
        ⟨hrestPw, fun p hp => hwf.2 p (List.mem_cons_of_mem _ hp)⟩
      have ih := mergeSortedIntervals_spec ((c, d) :: rest) hwf'
      have heq : mergeSortedIntervals ((a, b) :: (c, d) :: rest) =
          (a, b) :: mergeSortedIntervals ((c, d) :: rest) := by
        simp [mergeSortedIntervals, hmerge]
      rw [heq]
      refine ⟨⟨List.pairwise_cons.mpr ⟨?_, ih.1.1⟩, ?_⟩, ?_⟩
      · intro q hq
        have hqMem := fst_mem_expandIntervals hq (ih.1.2 q hq)
        have ⟨p, hp, hp1, _⟩ := (ih.2 q.1).mp hqMem
        have hcp : c ≤ p.1 := by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.le_refl _
          · exact (List.pairwise_cons.mp hrestPw).1 p hp
        omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hab
        · exact ih.1.2 p hp
      · intro l
        simp only [expandIntervals, List.mem_append, List.mem_range']
        rw [ih.2 l]
        constructor
        · rintro (⟨k, hk1, hk2⟩ | ⟨p, hp, h1, h2⟩)
          · exact ⟨(a, b), List.mem_cons_self, by omega, by omega⟩
          · exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩
        · rintro ⟨p, hp, h1, h2⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · left; exact ⟨l - a, by omega, by omega⟩
          · right; exact ⟨p, hp, h1, h2⟩
termination_by xs.length

theorem mem_expandIntervals_ge_head {xs : List (Nat × Nat)} {minStart y : Nat}
    (hmin : ∀ q ∈ xs, minStart ≤ q.1) (hy : y ∈ expandIntervals xs) :
    minStart ≤ y := by
  induction xs with
  | nil => simp [expandIntervals] at hy
  | cons hd tl ih =>
    simp only [expandIntervals, List.mem_append, List.mem_range'] at hy
    rcases hy with ⟨k, _, rfl⟩ | htl
    · have h1 := hmin hd List.mem_cons_self
      omega
    · exact ih (fun q hq => hmin q (List.mem_cons_of_mem _ hq)) htl

theorem expandIntervals_pairwise_lt (xs : List (Nat × Nat)) (h : DisjointSortedIntervals xs) :
    (expandIntervals xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [expandIntervals]
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    have hab : a ≤ b := h.2 (a, b) List.mem_cons_self
    have hpw := List.pairwise_cons.mp h.1
    have hrest : DisjointSortedIntervals rest := ⟨hpw.2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩
    have ih' := ih hrest
    simp only [expandIntervals]
    refine List.pairwise_append.mpr ⟨?_, ih', ?_⟩
    · refine List.pairwise_iff_getElem.mpr ?_
      intro i j hi hj hij
      simp only [List.getElem_range']
      omega
    · intro x hx y hy
      simp only [List.mem_range'] at hx
      rcases hx with ⟨i, hi, rfl⟩
      have hyGe := mem_expandIntervals_ge_head (fun q hq => hpw.1 q hq) hy
      omega

theorem validIntervals_sorted_wf (comments : List Comment) :
    WellFormedSortedIntervals ((validIntervals comments).mergeSort leInterval) := by
  refine ⟨?_, ?_⟩
  · have hpw := List.pairwise_mergeSort (le := leInterval)
      (fun a b c h1 h2 => by
        simp only [leInterval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
        omega)
      (fun a b => by
        simp only [leInterval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        omega)
      (validIntervals comments)
    exact hpw.imp fun {p q} hpq => by
      simp only [leInterval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq
      omega
  · intro p hp
    have hp' := (List.mergeSort_perm (validIntervals comments) leInterval).mem_iff.mp hp
    simp only [validIntervals, List.mem_filterMap] at hp'
    rcases hp' with ⟨c, _, hc⟩
    split at hc
    · rename_i hle; cases hc; exact hle
    · cases hc

theorem coveredLines_strictly_increasing (comments : Array Comment) :
    (coveredLines comments).Pairwise (· < ·) :=
  expandIntervals_pairwise_lt _
    (mergeSortedIntervals_spec _ (validIntervals_sorted_wf comments.toList)).1

theorem mem_coveredLines_iff (comments : Array Comment) (l : Nat) :
    l ∈ coveredLines comments ↔ ∃ c ∈ comments.toList, c.startLine ≤ l ∧ l ≤ c.endLine := by
  rw [coveredLines, (mergeSortedIntervals_spec _ (validIntervals_sorted_wf comments.toList)).2 l]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    have hp' := (List.mergeSort_perm (validIntervals comments.toList) leInterval).mem_iff.mp hp
    simp only [validIntervals, List.mem_filterMap] at hp'
    rcases hp' with ⟨c, hcMem, hcEq⟩
    split at hcEq
    · cases hcEq; exact ⟨c, hcMem, h1, h2⟩
    · cases hcEq
  · rintro ⟨c, hcMem, h1, h2⟩
    have hle : c.startLine ≤ c.endLine := Nat.le_trans h1 h2
    have hp' : (c.startLine, c.endLine) ∈ validIntervals comments.toList := by
      simp only [validIntervals, List.mem_filterMap]
      exact ⟨c, hcMem, by simp [hle]⟩
    have hp := (List.mergeSort_perm (validIntervals comments.toList) leInterval).mem_iff.mpr hp'
    exact ⟨(c.startLine, c.endLine), hp, h1, h2⟩

theorem distinctCommentLines_exact (comments : Array Comment) :
    ∃ ls : List Nat,
      ls.Pairwise (· < ·) ∧
      (∀ l, l ∈ ls ↔ ∃ c ∈ comments.toList, c.startLine ≤ l ∧ l ≤ c.endLine) ∧
      distinctCommentLines comments = ls.length :=
  ⟨coveredLines comments, coveredLines_strictly_increasing comments,
    mem_coveredLines_iff comments, distinctCommentLines_eq_length comments⟩

theorem nodup_length_eq_of_mem_iff {ls₁ ls₂ : List Nat}
    (h1 : ls₁.Nodup) (h2 : ls₂.Nodup) (hiff : ∀ l, l ∈ ls₁ ↔ l ∈ ls₂) :
    ls₁.length = ls₂.length :=
  ((List.perm_ext_iff_of_nodup h1 h2).mpr hiff).length_eq

theorem distinctCommentLines_unique (comments : Array Comment) (ls : List Nat)
    (hnodup : ls.Nodup)
    (hiff : ∀ l, l ∈ ls ↔ ∃ c ∈ comments.toList, c.startLine ≤ l ∧ l ≤ c.endLine) :
    distinctCommentLines comments = ls.length := by
  have hnodupCov : (coveredLines comments).Nodup :=
    (coveredLines_strictly_increasing comments).imp fun h => Nat.ne_of_lt h
  rw [distinctCommentLines_eq_length]
  exact nodup_length_eq_of_mem_iff hnodupCov hnodup fun l => (mem_coveredLines_iff comments l).trans (hiff l).symm

structure SortedFingerprints where
  values : Array String
  sorted : values.toList.Pairwise (· ≤ ·)

@[expose] def SortedFingerprints.empty : SortedFingerprints :=
  ⟨#[], .nil⟩

@[expose] def firstOutOfOrder : List String → Option String
  | [] | [_] => none
  | a :: b :: rest => if b < a then some b else firstOutOfOrder (b :: rest)

theorem firstOutOfOrder_eq_none_iff :
    ∀ l : List String, firstOutOfOrder l = none ↔ l.Pairwise (· ≤ ·)
  | [] => by simp [firstOutOfOrder]
  | [_] => by simp [firstOutOfOrder]
  | a :: b :: rest => by
    constructor
    · intro h
      unfold firstOutOfOrder at h
      split at h
      · cases h
      · rename_i hba
        have hab : a ≤ b := Std.not_lt.mp hba
        have htail := (firstOutOfOrder_eq_none_iff (b :: rest)).mp h
        have ⟨hb, _⟩ := List.pairwise_cons.mp htail
        refine List.pairwise_cons.mpr ⟨?_, htail⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hab
        · exact Std.le_trans hab (hb z hz)
    · intro h
      have ⟨ha, htail⟩ := List.pairwise_cons.mp h
      have hab : a ≤ b := ha b List.mem_cons_self
      have hnba : ¬(b < a) := Std.not_lt.mpr hab
      simp [firstOutOfOrder, hnba, (firstOutOfOrder_eq_none_iff (b :: rest)).mpr htail]

@[expose] def sortFingerprints (xs : Array String) : SortedFingerprints :=
  ⟨(xs.toList.mergeSort (fun a b => decide (a ≤ b))).toArray, by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort
        (le := fun a b : String => decide (a ≤ b))
        (fun _ _ _ h1 h2 => decide_eq_true (Std.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
        (fun a b => by
          by_cases h : a < b
          · simp [(Std.lt_iff_le_and_ne.mp h).1]
          · simp [Std.not_lt.mp h])
        xs.toList⟩

theorem sortFingerprints_count (xs : Array String) (a : String) :
    (sortFingerprints xs).values.toList.count a = xs.toList.count a :=
  (List.mergeSort_perm xs.toList (fun a b => decide (a ≤ b))).count_eq a

@[expose] def missingFromListAux (acc : List String) : List String → List String → List String
  | [], _ => acc.reverse
  | xs, [] => acc.reverse ++ xs
  | x :: xs, y :: ys =>
    if y < x then missingFromListAux acc (x :: xs) ys
    else if y == x then missingFromListAux acc xs ys
    else missingFromListAux (x :: acc) xs (y :: ys)
termination_by xs ys => xs.length + ys.length

@[expose] def missingFrom (xs ys : SortedFingerprints) : Array String :=
  (missingFromListAux [] xs.values.toList ys.values.toList).toArray

theorem count_eq_zero_of_lt_all {l : List String} {a : String} (h : ∀ z ∈ l, a < z) :
    l.count a = 0 :=
  List.count_eq_zero.mpr fun hm => Std.lt_irrefl (h a hm)

theorem missingFromListAux_count (acc xs ys : List String)
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) (a : String) :
    (missingFromListAux acc xs ys).count a = acc.count a + (xs.count a - ys.count a) := by
  match xs, ys with
  | [], _ =>
    simp [missingFromListAux]
  | x :: xs, [] =>
    simp [missingFromListAux]
  | x :: xs, y :: ys =>
    rw [missingFromListAux]
    have ⟨hx, hxs'⟩ := List.pairwise_cons.mp hxs
    have ⟨hy, hys'⟩ := List.pairwise_cons.mp hys
    split
    · rename_i hyx
      rw [missingFromListAux_count acc (x :: xs) ys hxs hys' a]
      by_cases hay : y = a
      · subst hay
        have h0 : (x :: xs).count y = 0 := count_eq_zero_of_lt_all fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hyx
          · exact Std.lt_of_lt_of_le hyx (hx z hz)
        simp [h0]
      · simp [List.count_cons_of_ne hay]
    · rename_i hnyx
      split
      · rename_i heq
        have hyx : y = x := eq_of_beq heq
        subst hyx
        rw [missingFromListAux_count acc xs ys hxs' hys' a]
        by_cases hax : y = a
        · subst hax
          simp
        · simp [List.count_cons_of_ne hax]
      · rename_i hneq
        have hne : x ≠ y := fun h => hneq (beq_iff_eq.mpr h.symm)
        have hxy : x < y := Std.lt_iff_le_and_ne.mpr ⟨Std.not_lt.mp hnyx, hne⟩
        rw [missingFromListAux_count (x :: acc) xs (y :: ys) hxs' hys a]
        by_cases hax : x = a
        · subst hax
          have h0 : (y :: ys).count x = 0 := count_eq_zero_of_lt_all fun z hz => by
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hxy
            · exact Std.lt_of_lt_of_le hxy (hy z hz)
          simp [h0]
          omega
        · simp [List.count_cons_of_ne hax]
termination_by xs.length + ys.length

theorem missingFrom_count (xs ys : SortedFingerprints) (a : String) :
    (missingFrom xs ys).toList.count a = xs.values.toList.count a - ys.values.toList.count a := by
  simp [missingFrom, missingFromListAux_count [] xs.values.toList ys.values.toList xs.sorted ys.sorted a]

theorem missingFrom_isEmpty_iff (xs ys : SortedFingerprints) :
    (missingFrom xs ys).isEmpty = true ↔
      ∀ a, xs.values.toList.count a ≤ ys.values.toList.count a := by
  have hiff : (missingFrom xs ys).isEmpty = true ↔ (missingFrom xs ys).toList = [] := by
    cases h : missingFrom xs ys with
    | mk l => simp [Array.isEmpty, List.length_eq_zero_iff]
  rw [hiff]
  constructor
  · intro hnil a
    have hcnt := missingFrom_count xs ys a
    rw [hnil, List.count_nil] at hcnt
    omega
  · intro h
    cases hl : (missingFrom xs ys).toList with
    | nil => rfl
    | cons a rest =>
      have hcnt := missingFrom_count xs ys a
      rw [hl, List.count_cons_self] at hcnt
      have := h a
      omega

theorem missingFrom_both_isEmpty_iff (xs ys : SortedFingerprints) :
    ((missingFrom xs ys).isEmpty && (missingFrom ys xs).isEmpty) = true ↔
      ∀ a, xs.values.toList.count a = ys.values.toList.count a := by
  simp only [Bool.and_eq_true, missingFrom_isEmpty_iff]
  constructor
  · intro ⟨h1, h2⟩ a
    exact Nat.le_antisymm (h1 a) (h2 a)
  · intro h
    exact ⟨fun a => Nat.le_of_eq (h a), fun a => Nat.le_of_eq (h a).symm⟩

end

end NoComments.Core
