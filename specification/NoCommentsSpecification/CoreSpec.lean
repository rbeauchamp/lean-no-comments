module

public import Lean.Data.Json
public import NoCommentsSpecification.Types

@[expose] public section

namespace NoCommentsSpecification.CoreSpec

open Lean
open NoComments

def isHexLowerChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def IsFingerprint (s : String) : Prop :=
  s.length = 16 ∧ ∀ c ∈ s.toList, isHexLowerChar c = true

def parseWith {α : Type} (env : Environment) (p : Parser.ParserFn) (input : String)
    (k : Syntax → Option α) : Option α :=
  let s := p.run (Parser.mkInputContext input "<token>") { env := env, options := ∅ } ∅
    (Parser.mkParserState input)
  if !s.hasError && s.stackSize == 1 then
    k s.stxStack.back
  else
    none

def literalToken (env : Environment) (token : Syntax) (raw : String) : Bool :=
  match token with
  | .ident _ spelling _ _ =>
    match parseWith env Parser.tokenFn raw pure with
    | some (.ident _ parsed _ _) => spelling.toString == raw && parsed.toString == raw
    | _ => false
  | .node _ k _ =>
    if Syntax.isLit? k token == some raw then
      if k == interpolatedStrLitKind then
        let chunk := if raw.startsWith "}" then "\"" ++ (raw.drop 1).toString else raw
        let emptyHole : Parser.ParserFn := fun _ s => s.pushSyntax .missing
        match parseWith env (Parser.interpolatedStrFn emptyHole) (chunk ++ "}\"") pure with
        | some parsed => ((parsed[0]?).bind (Syntax.isLit? k)) == some chunk
        | none => false
      else
        (parseWith env Parser.tokenFn raw (Syntax.isLit? k)) == some raw
    else
      false
  | _ => false

def registeredSymbol (ctx : Parser.ParserContextCore) (token : Syntax) : Bool :=
  let leaf := match token with
    | .node _ _ #[arg] => arg
    | _ => token
  match leaf with
  | .atom (.original _ start _ stop) spelling =>
    let parsed := (Parser.symbolFn spelling).run ctx.toInputContext ctx.toParserModuleContext
      ctx.tokens { pos := start, cache := Parser.initCacheForInput ctx.inputString }
    !parsed.hasError && parsed.stackSize == 1 && parsed.stxStack.back.getTailPos? == some stop
  | _ => false

def hasCharPair (a b : Char) : List Char → Bool
  | x :: y :: rest => (x == a && y == b) || hasCharPair a b (y :: rest)
  | _ => false

def containsOpener (raw : String) : Bool :=
  hasCharPair '-' '-' raw.toList || hasCharPair '/' '-' raw.toList

def crossesBoundary (raw : String) (next : Char) : Bool :=
  next == '-' && (raw.toList.getLast? == some '-' || raw.toList.getLast? == some '/')

def TokenSafe (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char) : Prop :=
  literalToken ctx.env token raw = true ∨
    registeredSymbol ctx token = true ∨
    (containsOpener raw = false ∧ crossesBoundary raw next = false)

inductive TokenRefusal (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char) :
    Prop where
  | openerInRaw :
      literalToken ctx.env token raw = false →
      registeredSymbol ctx token = false →
      containsOpener raw = true →
      TokenRefusal ctx token raw next
  | boundaryCross :
      literalToken ctx.env token raw = false →
      registeredSymbol ctx token = false →
      crossesBoundary raw next = true →
      TokenRefusal ctx token raw next

def docKind (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.docComment ||
    k == ``Parser.Command.plainDocComment ||
    k == ``Parser.Command.moduleDoc

inductive OriginalLeafIn : Syntax → Syntax → String.Pos.Raw → String.Pos.Raw → Prop where
  | atom (info : SourceInfo) (val : String) (leading trail : Substring.Raw)
      (start stop : String.Pos.Raw) :
      info = .original leading start trail stop →
      OriginalLeafIn (.atom info val) (.atom info val) start stop
  | ident (info : SourceInfo) (rawVal : Substring.Raw) (val : Name)
      (preresolved : List Syntax.Preresolved) (leading trail : Substring.Raw)
      (start stop : String.Pos.Raw) :
      info = .original leading start trail stop →
      OriginalLeafIn (.ident info rawVal val preresolved)
        (.ident info rawVal val preresolved) start stop
  | singletonAtomNode (info : SourceInfo) (k : SyntaxNodeKind) (atomInfo : SourceInfo)
      (val : String) (leading trail : Substring.Raw) (start stop : String.Pos.Raw) :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original leading start trail stop →
      OriginalLeafIn (.node info k #[.atom atomInfo val])
        (.node info k #[.atom atomInfo val]) start stop
  | child (info : SourceInfo) (k : SyntaxNodeKind) (args : Array Syntax) (arg leaf : Syntax)
      (start stop : String.Pos.Raw) :
      arg ∈ args.toList →
      OriginalLeafIn arg leaf start stop →
      OriginalLeafIn (.node info k args) leaf start stop

inductive DocNodeIn : Syntax → String → Nat → Nat → Prop where
  | here {info k args l1 start t1 s1 l2 s2 t2 stop kind} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      kind = (if k == ``Parser.Command.moduleDoc then "moddoc" else "doc") →
      DocNodeIn (.node info k args) kind start.byteIdx stop.byteIdx
  | child {info k args arg kind sb eb} :
      docKind k = false →
      arg ∈ args.toList →
      DocNodeIn arg kind sb eb →
      DocNodeIn (.node info k args) kind sb eb

def TriviaByteCovered (str : String) (acc : Core.CommentAcc) (lo hi b : Nat) : Prop :=
  (∃ sb eb c, acc.spans[sb]? = some (eb, c) ∧ sb < eb ∧ sb ≤ b ∧ b < eb) ∨
    ∃ p : String.Pos.Raw,
      lo ≤ p.byteIdx ∧ p.byteIdx ≤ b ∧ b < (String.Pos.Raw.next str p).byteIdx ∧
        (String.Pos.Raw.next str p).byteIdx ≤ hi ∧ (String.Pos.Raw.get str p).isWhitespace = true

def ByteAccounted (ctx : Parser.ParserContextCore) (stx : Syntax) (acc : Core.CommentAcc)
    (lo hi b : Nat) : Prop :=
  TriviaByteCovered ctx.fileMap.source acc lo hi b ∨
    ∃ leaf start stop,
      OriginalLeafIn stx leaf start stop ∧
        lo ≤ start.byteIdx ∧ start.byteIdx ≤ b ∧ b < stop.byteIdx ∧ stop.byteIdx ≤ hi ∧
        TokenSafe ctx leaf (ctx.extract start stop) (ctx.get stop)

def ContiguousFrom : String.Pos.Raw → String.Pos.Raw → List Core.CommandRange → Prop
  | start, endPos, [] => start = endPos
  | start, endPos, r :: rest =>
      r.prevPos = start ∧ r.prevPos ≤ r.nextPos ∧ ContiguousFrom r.nextPos endPos rest

def validCommentKind (kind : String) : Prop :=
  kind ∈ ["line", "block", "doc", "moddoc"]

def GenuineCommentSpan (ctx : Parser.ParserContextCore) (stx : Syntax) (sb eb : Nat)
    (c : Core.Comment) : Prop :=
  sb < eb ∧
  eb ≤ ctx.endPos.byteIdx ∧
  validCommentKind c.kind ∧
  IsFingerprint c.fingerprint ∧
  c.startLine = (ctx.fileMap.toPosition ⟨sb⟩).line ∧
  c.endLine = (ctx.fileMap.toPosition (String.Pos.Raw.prev ctx.fileMap.source ⟨eb⟩)).line ∧
  ((c.kind = "line" ∧
      let p0 : String.Pos.Raw := ⟨sb⟩
      let p1 := String.Pos.Raw.next ctx.fileMap.source p0
      let p2 := String.Pos.Raw.next ctx.fileMap.source p1
      String.Pos.Raw.get ctx.fileMap.source p0 = '-' ∧
      String.Pos.Raw.get ctx.fileMap.source p1 = '-' ∧
      p2.byteIdx ≤ eb) ∨
    (c.kind = "block" ∧
      let p0 : String.Pos.Raw := ⟨sb⟩
      let p1 := String.Pos.Raw.next ctx.fileMap.source p0
      let p2 := String.Pos.Raw.next ctx.fileMap.source p1
      let p3 := String.Pos.Raw.next ctx.fileMap.source p2
      String.Pos.Raw.get ctx.fileMap.source p0 = '/' ∧
      String.Pos.Raw.get ctx.fileMap.source p1 = '-' ∧
      p2.byteIdx < eb ∧
      String.Pos.Raw.get ctx.fileMap.source p2 ≠ '-' ∧
      String.Pos.Raw.get ctx.fileMap.source p2 ≠ '!' ∧
      p3.byteIdx ≤ eb ∧
      ∃ pm ps : String.Pos.Raw,
        ps = String.Pos.Raw.next ctx.fileMap.source pm ∧
        eb = (String.Pos.Raw.next ctx.fileMap.source ps).byteIdx ∧
        String.Pos.Raw.get ctx.fileMap.source pm = '-' ∧
        String.Pos.Raw.get ctx.fileMap.source ps = '/') ∨
    ((c.kind = "doc" ∨ c.kind = "moddoc") ∧ DocNodeIn stx c.kind sb eb))

abbrev SpanState : Type := Nat → Option (Nat × String)

def stateOfAcc (acc : Core.CommentAcc) : SpanState :=
  fun sb => (acc.spans[sb]?).map fun p => (p.1, p.2.kind)

def insertSpan (state : SpanState) (kind : String) (sb eb : Nat) : SpanState :=
  fun k => if k == sb then some (eb, kind) else state k

inductive LineEnd (str : String) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → Prop where
  | done {p} : ¬ p < stopPos → LineEnd str stopPos p stopPos
  | nl {p} : p < stopPos → String.Pos.Raw.get str p = '\n' → LineEnd str stopPos p p
  | step {p eol} : p < stopPos → String.Pos.Raw.get str p ≠ '\n' →
      LineEnd str stopPos (String.Pos.Raw.next str p) eol → LineEnd str stopPos p eol

inductive BlockStep (str : String) (stopPos : String.Pos.Raw) :
    Nat → String.Pos.Raw → String.Pos.Raw → Prop where
  | closeTop {nesting pos} :
      nesting = 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockStep str stopPos nesting pos (String.Pos.Raw.next str (String.Pos.Raw.next str pos))
  | closeNested {nesting pos endPos} :
      nesting ≠ 1 →
      nesting ≥ 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockStep str stopPos (nesting - 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos →
      BlockStep str stopPos nesting pos endPos
  | openNested {nesting pos endPos} :
      nesting ≥ 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '/' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockStep str stopPos (nesting + 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos →
      BlockStep str stopPos nesting pos endPos
  | other {nesting pos endPos} :
      nesting ≥ 1 →
      pos < stopPos →
      ¬ (String.Pos.Raw.get str pos = '-' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/') →
      ¬ (String.Pos.Raw.get str pos = '/' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-') →
      BlockStep str stopPos nesting (String.Pos.Raw.next str pos) endPos →
      BlockStep str stopPos nesting pos endPos

inductive BlockFails (str : String) (stopPos : String.Pos.Raw) :
    Nat → String.Pos.Raw → Prop where
  | atEof {nesting pos} : ¬ pos < stopPos → BlockFails str stopPos nesting pos
  | closeBoundary {nesting pos} :
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      ¬ String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockFails str stopPos nesting pos
  | openBoundary {nesting pos} :
      pos < stopPos →
      String.Pos.Raw.get str pos = '/' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-' →
      ¬ String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockFails str stopPos nesting pos
  | closeNested {nesting pos} :
      nesting ≠ 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockFails str stopPos (nesting - 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) →
      BlockFails str stopPos nesting pos
  | openNested {nesting pos} :
      pos < stopPos →
      String.Pos.Raw.get str pos = '/' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockFails str stopPos (nesting + 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) →
      BlockFails str stopPos nesting pos
  | other {nesting pos} :
      pos < stopPos →
      ¬ (String.Pos.Raw.get str pos = '-' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/') →
      ¬ (String.Pos.Raw.get str pos = '/' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-') →
      BlockFails str stopPos nesting (String.Pos.Raw.next str pos) →
      BlockFails str stopPos nesting pos

def SpanConflict (state : SpanState) (kind : String) (sb eb : Nat) : Prop :=
  eb ≤ sb ∨ ∃ prevEb prevKind, state sb = some (prevEb, prevKind) ∧ (prevEb ≠ eb ∨ prevKind ≠ kind)

inductive TriviaFails (fileMap : FileMap) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → SpanState → Prop where
  | wsBoundary {pos state} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = true →
      ¬ String.Pos.Raw.next fileMap.source pos ≤ stopPos →
      TriviaFails fileMap stopPos pos state
  | wsStep {pos state} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = true →
      String.Pos.Raw.next fileMap.source pos ≤ stopPos →
      TriviaFails fileMap stopPos (String.Pos.Raw.next fileMap.source pos) state →
      TriviaFails fileMap stopPos pos state
  | lineBoundary {pos state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      ¬ String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      TriviaFails fileMap stopPos pos state
  | lineSpanConflict {pos eol state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      LineEnd fileMap.source stopPos
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) eol →
      SpanConflict state "line" pos.byteIdx eol.byteIdx →
      TriviaFails fileMap stopPos pos state
  | lineStep {pos eol state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      LineEnd fileMap.source stopPos
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) eol →
      pos.byteIdx < eol.byteIdx →
      ¬ SpanConflict state "line" pos.byteIdx eol.byteIdx →
      TriviaFails fileMap stopPos eol (insertSpan state "line" pos.byteIdx eol.byteIdx) →
      TriviaFails fileMap stopPos pos state
  | blockUnterminated1 {pos state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '/' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      ¬ String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) < stopPos →
      TriviaFails fileMap stopPos pos state
  | docOpenerInTrivia {pos state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '/' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) < stopPos →
      (String.Pos.Raw.get fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) = '-' ∨
        String.Pos.Raw.get fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) = '!') →
      TriviaFails fileMap stopPos pos state
  | blockUnterminated2 {pos state} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '/' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) < stopPos →
      String.Pos.Raw.get fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≠ '-' →
      String.Pos.Raw.get fileMap.source
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≠ '!' →
      ¬ String.Pos.Raw.next fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) ≤ stopPos →
      TriviaFails fileMap stopPos pos state
  | blockBodyFails {pos state} :
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
      BlockFails fileMap.source stopPos 1
        (String.Pos.Raw.next fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos))) →
      TriviaFails fileMap stopPos pos state
  | blockSpanConflict {pos endPos state} :
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
      SpanConflict state "block" pos.byteIdx endPos.byteIdx →
      TriviaFails fileMap stopPos pos state
  | blockStep {pos endPos state} :
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
      ¬ SpanConflict state "block" pos.byteIdx endPos.byteIdx →
      TriviaFails fileMap stopPos endPos (insertSpan state "block" pos.byteIdx endPos.byteIdx) →
      TriviaFails fileMap stopPos pos state
  | unexpectedChar {pos state} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = false →
      ¬ (String.Pos.Raw.get fileMap.source pos = '-' ∧ String.Pos.Raw.next fileMap.source pos < stopPos ∧
          String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-') →
      ¬ (String.Pos.Raw.get fileMap.source pos = '/' ∧ String.Pos.Raw.next fileMap.source pos < stopPos ∧
          String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-') →
      TriviaFails fileMap stopPos pos state

inductive TriviaStep (fileMap : FileMap) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → SpanState → SpanState → Prop where
  | done {pos state} : ¬ pos < stopPos → TriviaStep fileMap stopPos pos state state
  | ws {pos state state'} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = true →
      String.Pos.Raw.next fileMap.source pos ≤ stopPos →
      TriviaStep fileMap stopPos (String.Pos.Raw.next fileMap.source pos) state state' →
      TriviaStep fileMap stopPos pos state state'
  | line {pos eol state state'} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      LineEnd fileMap.source stopPos
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) eol →
      ¬ SpanConflict state "line" pos.byteIdx eol.byteIdx →
      TriviaStep fileMap stopPos eol (insertSpan state "line" pos.byteIdx eol.byteIdx) state' →
      TriviaStep fileMap stopPos pos state state'
  | block {pos endPos state state'} :
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
      ¬ SpanConflict state "block" pos.byteIdx endPos.byteIdx →
      TriviaStep fileMap stopPos endPos (insertSpan state "block" pos.byteIdx endPos.byteIdx) state' →
      TriviaStep fileMap stopPos pos state state'

mutual

inductive SyntaxStep (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    Syntax → String.Pos.Raw → SpanState → String.Pos.Raw → SpanState → Prop where
  | atomOrig {l start t stop val pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenSafe ctx (Syntax.atom (.original l start t stop) val)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxStep ctx nextPos (Syntax.atom (.original l start t stop) val) pos state stop state1
  | identOrig {l start t stop rawVal val pre pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenSafe ctx (Syntax.ident (.original l start t stop) rawVal val pre)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxStep ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos state stop state1
  | doc {info k args l1 start t1 s1 l2 s2 t2 stop pos state state1 kind} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      kind = (if k == ``Parser.Command.moduleDoc then "moddoc" else "doc") →
      ¬ SpanConflict state1 kind start.byteIdx stop.byteIdx →
      SyntaxStep ctx nextPos (Syntax.node info k args) pos state stop
        (insertSpan state1 kind start.byteIdx stop.byteIdx)
  | choice {info first alts pos state stop state1 state2} :
      SyntaxStep ctx nextPos first pos state stop state1 →
      AltsStep ctx nextPos pos stop alts state1 state2 →
      SyntaxStep ctx nextPos (Syntax.node info choiceKind ⟨first :: alts⟩) pos state stop state2
  | singletonAtomNode {info k atomInfo val l start t stop pos state state1} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenSafe ctx (Syntax.node info k #[.atom atomInfo val])
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxStep ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos state stop state1
  | nodeList {info k args pos state stop state'} :
      docKind k = false →
      k ≠ choiceKind →
      (∀ l start t stop val, args ≠ #[.atom (.original l start t stop) val]) →
      ListStep ctx nextPos args.toList pos state stop state' →
      SyntaxStep ctx nextPos (Syntax.node info k args) pos state stop state'
  | other {s pos state} :
      (∀ l start t stop val, s ≠ .atom (.original l start t stop) val) →
      (∀ l start t stop rawVal val pre, s ≠ .ident (.original l start t stop) rawVal val pre) →
      (∀ info k args, s ≠ .node info k args) →
      SyntaxStep ctx nextPos s pos state pos state

inductive AltsStep (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → List Syntax → SpanState → SpanState → Prop where
  | nil {pos stop state} : AltsStep ctx nextPos pos stop [] state state
  | cons {pos stop alt rest state state1 state2} :
      SyntaxStep ctx nextPos alt pos state stop state1 →
      AltsStep ctx nextPos pos stop rest state1 state2 →
      AltsStep ctx nextPos pos stop (alt :: rest) state state2

inductive ListStep (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    List Syntax → String.Pos.Raw → SpanState → String.Pos.Raw → SpanState → Prop where
  | nil {pos state} : ListStep ctx nextPos [] pos state pos state
  | cons {arg rest pos state mid state1 stop state2} :
      SyntaxStep ctx nextPos arg pos state mid state1 →
      ListStep ctx nextPos rest mid state1 stop state2 →
      ListStep ctx nextPos (arg :: rest) pos state stop state2

end

mutual

inductive SyntaxFails (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    Syntax → String.Pos.Raw → SpanState → Prop where
  | atomRange {l start t stop val pos state} :
      ¬ (pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos) →
      SyntaxFails ctx nextPos (Syntax.atom (.original l start t stop) val) pos state
  | atomTrivia {l start t stop val pos state} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaFails ctx.fileMap start pos state →
      SyntaxFails ctx nextPos (Syntax.atom (.original l start t stop) val) pos state
  | atomToken {l start t stop val pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenRefusal ctx (Syntax.atom (.original l start t stop) val)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxFails ctx nextPos (Syntax.atom (.original l start t stop) val) pos state
  | identRange {l start t stop rawVal val pre pos state} :
      ¬ (pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos) →
      SyntaxFails ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos state
  | identTrivia {l start t stop rawVal val pre pos state} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaFails ctx.fileMap start pos state →
      SyntaxFails ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos state
  | identToken {l start t stop rawVal val pre pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenRefusal ctx (Syntax.ident (.original l start t stop) rawVal val pre)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxFails ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos state
  | docMissingInfo {info k args pos state} :
      docKind k = true →
      (∀ l1 start t1 s1 l2 s2 t2 stop,
        ¬ ((Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) ∧
           (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop))) →
      SyntaxFails ctx nextPos (Syntax.node info k args) pos state
  | docRange {info k args l1 start t1 s1 l2 s2 t2 stop pos state} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      ¬ (pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos) →
      SyntaxFails ctx nextPos (Syntax.node info k args) pos state
  | docTrivia {info k args l1 start t1 s1 l2 s2 t2 stop pos state} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaFails ctx.fileMap start pos state →
      SyntaxFails ctx nextPos (Syntax.node info k args) pos state
  | docSpanConflict {info k args l1 start t1 s1 l2 s2 t2 stop pos state state1 kind} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      kind = (if k == ``Parser.Command.moduleDoc then "moddoc" else "doc") →
      SpanConflict state1 kind start.byteIdx stop.byteIdx →
      SyntaxFails ctx nextPos (Syntax.node info k args) pos state
  | emptyChoice {info pos state} :
      SyntaxFails ctx nextPos (Syntax.node info choiceKind #[]) pos state
  | choiceFirst {info first alts pos state} :
      SyntaxFails ctx nextPos first pos state →
      SyntaxFails ctx nextPos (Syntax.node info choiceKind ⟨first :: alts⟩) pos state
  | choiceAlts {info first alts pos stop state state1} :
      SyntaxStep ctx nextPos first pos state stop state1 →
      AltsFails ctx nextPos pos stop alts state1 →
      SyntaxFails ctx nextPos (Syntax.node info choiceKind ⟨first :: alts⟩) pos state
  | singletonAtomRange {info k atomInfo val l start t stop pos state} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      ¬ (pos ≤ start ∧ start ≤ stop ∧ stop ≤ nextPos) →
      SyntaxFails ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos state
  | singletonAtomTrivia {info k atomInfo val l start t stop pos state} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaFails ctx.fileMap start pos state →
      SyntaxFails ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos state
  | singletonAtomToken {info k atomInfo val l start t stop pos state state1} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      TriviaStep ctx.fileMap start pos state state1 →
      TokenRefusal ctx (Syntax.node info k #[.atom atomInfo val])
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxFails ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos state
  | nodeList {info k args pos state} :
      docKind k = false →
      k ≠ choiceKind →
      (∀ l start t stop val, args ≠ #[.atom (.original l start t stop) val]) →
      ListFails ctx nextPos args.toList pos state →
      SyntaxFails ctx nextPos (Syntax.node info k args) pos state

inductive AltsFails (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → List Syntax → SpanState → Prop where
  | head {pos stop alt rest state} :
      SyntaxFails ctx nextPos alt pos state →
      AltsFails ctx nextPos pos stop (alt :: rest) state
  | mismatch {pos stop altStop alt rest state state1} :
      SyntaxStep ctx nextPos alt pos state altStop state1 →
      altStop ≠ stop →
      AltsFails ctx nextPos pos stop (alt :: rest) state
  | tail {pos stop alt rest state state1} :
      SyntaxStep ctx nextPos alt pos state stop state1 →
      AltsFails ctx nextPos pos stop rest state1 →
      AltsFails ctx nextPos pos stop (alt :: rest) state

inductive ListFails (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    List Syntax → String.Pos.Raw → SpanState → Prop where
  | head {arg rest pos state} :
      SyntaxFails ctx nextPos arg pos state →
      ListFails ctx nextPos (arg :: rest) pos state
  | tail {arg rest pos mid state state1} :
      SyntaxStep ctx nextPos arg pos state mid state1 →
      ListFails ctx nextPos rest mid state1 →
      ListFails ctx nextPos (arg :: rest) pos state

end

inductive CollectRefusalAt : List Core.CommandRange → SpanState → Prop where
  | badBounds {r rest state} :
      ¬ (r.prevPos ≤ r.nextPos ∧ r.nextPos ≤ r.ctx.endPos) →
      CollectRefusalAt (r :: rest) state
  | syntaxFails {r rest state} :
      r.prevPos ≤ r.nextPos →
      r.nextPos ≤ r.ctx.endPos →
      SyntaxFails r.ctx r.nextPos r.stx r.prevPos state →
      CollectRefusalAt (r :: rest) state
  | trailingTriviaFails {r rest state mid state1} :
      r.prevPos ≤ r.nextPos →
      r.nextPos ≤ r.ctx.endPos →
      SyntaxStep r.ctx r.nextPos r.stx r.prevPos state mid state1 →
      TriviaFails r.ctx.fileMap r.nextPos mid state1 →
      CollectRefusalAt (r :: rest) state
  | restFails {r rest state mid state1 state2} :
      r.prevPos ≤ r.nextPos →
      r.nextPos ≤ r.ctx.endPos →
      SyntaxStep r.ctx r.nextPos r.stx r.prevPos state mid state1 →
      TriviaStep r.ctx.fileMap r.nextPos mid state1 state2 →
      CollectRefusalAt rest state2 →
      CollectRefusalAt (r :: rest) state

def CollectRefusal (ranges : List Core.CommandRange) (acc : Core.CommentAcc) : Prop :=
  CollectRefusalAt ranges (stateOfAcc acc)

def SourceOrdered (acc : Core.CommentAcc) (res : Array Core.Comment) : Prop :=
  ∃ entries : List (Nat × Nat × Core.Comment),
    entries.Pairwise (fun a b => a.1 < b.1) ∧
    (∀ sb eb c, (sb, eb, c) ∈ entries ↔ acc.spans[sb]? = some (eb, c)) ∧
    res.toList = entries.map (·.2.2)

def DistinctLines (comments : Array Core.Comment) (n : Nat) : Prop :=
  ∃ ls : List Nat,
    ls.Nodup ∧
    (∀ l, l ∈ ls ↔ ∃ c ∈ comments.toList, c.startLine ≤ l ∧ l ≤ c.endLine) ∧
    n = ls.length

def FirstOutOfOrderSpec (l : List String) (res : Option String) : Prop :=
  (res = none ↔ l.Pairwise (· ≤ ·)) ∧
  (∀ b, res = some b → ∃ pfx a sfx, l = pfx ++ [a, b] ++ sfx ∧ (pfx ++ [a]).Pairwise (· ≤ ·) ∧ b < a)

def MultisetEq (xs ys : List String) : Prop :=
  ∀ a, xs.count a = ys.count a

def MultisetDiff (xs ys diff : List String) : Prop :=
  ∀ a, diff.count a = xs.count a - ys.count a

end NoCommentsSpecification.CoreSpec
