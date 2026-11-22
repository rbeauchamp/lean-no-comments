module

public import Lean.Data.Json
public import NoCommentsSpecification.Types

@[expose] public section

namespace NoCommentsSpecification.Healthy

open Lean
open NoComments

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

def noOpener (raw : String) : Bool :=
  !hasCharPair '-' '-' raw.toList && !hasCharPair '/' '-' raw.toList

def noBoundaryCross (raw : String) (next : Char) : Bool :=
  !(next == '-' && (raw.toList.getLast? == some '-' || raw.toList.getLast? == some '/'))

def Token (ctx : Parser.ParserContextCore) (token : Syntax) (raw : String) (next : Char) : Prop :=
  literalToken ctx.env token raw = true ∨
    registeredSymbol ctx token = true ∨
    (noOpener raw = true ∧ noBoundaryCross raw next = true)

abbrev SpanState : Type := Nat → Option (Nat × String)

def stateOfAcc (acc : Core.CommentAcc) : SpanState :=
  fun sb => (acc.spans[sb]?).map fun p => (p.1, p.2.kind)

def SpanCompatible (state : SpanState) (kind : String) (sb eb : Nat) : Prop :=
  sb < eb ∧
    match state sb with
    | some (prevEb, prevKind) => prevEb = eb ∧ prevKind = kind
    | none => True

def insertSpan (state : SpanState) (kind : String) (sb eb : Nat) : SpanState :=
  fun k => if k == sb then some (eb, kind) else state k

inductive LineEnd (str : String) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → Prop where
  | done {p} : ¬ p < stopPos → LineEnd str stopPos p stopPos
  | nl {p} : p < stopPos → String.Pos.Raw.get str p = '\n' → LineEnd str stopPos p p
  | step {p eol} : p < stopPos → String.Pos.Raw.get str p ≠ '\n' →
      LineEnd str stopPos (String.Pos.Raw.next str p) eol → LineEnd str stopPos p eol

inductive BlockCloses (str : String) (stopPos : String.Pos.Raw) :
    Nat → String.Pos.Raw → String.Pos.Raw → Prop where
  | closeTop {nesting pos} :
      nesting = 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockCloses str stopPos nesting pos (String.Pos.Raw.next str (String.Pos.Raw.next str pos))
  | closeNested {nesting pos endPos} :
      nesting ≠ 1 →
      nesting ≥ 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '-' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockCloses str stopPos (nesting - 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos →
      BlockCloses str stopPos nesting pos endPos
  | openNested {nesting pos endPos} :
      nesting ≥ 1 →
      pos < stopPos →
      String.Pos.Raw.get str pos = '/' →
      String.Pos.Raw.next str pos < stopPos →
      String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-' →
      String.Pos.Raw.next str (String.Pos.Raw.next str pos) ≤ stopPos →
      BlockCloses str stopPos (nesting + 1) (String.Pos.Raw.next str (String.Pos.Raw.next str pos)) endPos →
      BlockCloses str stopPos nesting pos endPos
  | other {nesting pos endPos} :
      nesting ≥ 1 →
      pos < stopPos →
      ¬ (String.Pos.Raw.get str pos = '-' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '/') →
      ¬ (String.Pos.Raw.get str pos = '/' ∧ String.Pos.Raw.next str pos < stopPos ∧
          String.Pos.Raw.get str (String.Pos.Raw.next str pos) = '-') →
      BlockCloses str stopPos nesting (String.Pos.Raw.next str pos) endPos →
      BlockCloses str stopPos nesting pos endPos

inductive Trivia (fileMap : FileMap) (stopPos : String.Pos.Raw) :
    String.Pos.Raw → SpanState → SpanState → Prop where
  | done {pos state} : ¬ pos < stopPos → Trivia fileMap stopPos pos state state
  | ws {pos state state'} :
      pos < stopPos →
      (String.Pos.Raw.get fileMap.source pos).isWhitespace = true →
      String.Pos.Raw.next fileMap.source pos ≤ stopPos →
      Trivia fileMap stopPos (String.Pos.Raw.next fileMap.source pos) state state' →
      Trivia fileMap stopPos pos state state'
  | line {pos eol state state'} :
      pos < stopPos →
      String.Pos.Raw.get fileMap.source pos = '-' →
      String.Pos.Raw.next fileMap.source pos < stopPos →
      String.Pos.Raw.get fileMap.source (String.Pos.Raw.next fileMap.source pos) = '-' →
      String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos) ≤ stopPos →
      LineEnd fileMap.source stopPos
        (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)) eol →
      SpanCompatible state "line" pos.byteIdx eol.byteIdx →
      Trivia fileMap stopPos eol (insertSpan state "line" pos.byteIdx eol.byteIdx) state' →
      Trivia fileMap stopPos pos state state'
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
      BlockCloses fileMap.source stopPos 1
        (String.Pos.Raw.next fileMap.source
          (String.Pos.Raw.next fileMap.source (String.Pos.Raw.next fileMap.source pos)))
        endPos →
      SpanCompatible state "block" pos.byteIdx endPos.byteIdx →
      Trivia fileMap stopPos endPos (insertSpan state "block" pos.byteIdx endPos.byteIdx) state' →
      Trivia fileMap stopPos pos state state'

def docKind (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.docComment ||
    k == ``Parser.Command.plainDocComment ||
    k == ``Parser.Command.moduleDoc

mutual

inductive SyntaxOk (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    Syntax → String.Pos.Raw → SpanState → String.Pos.Raw → SpanState → Prop where
  | atomOrig {l start t stop val pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      Trivia ctx.fileMap start pos state state1 →
      Token ctx (Syntax.atom (.original l start t stop) val)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxOk ctx nextPos (Syntax.atom (.original l start t stop) val) pos state stop state1
  | identOrig {l start t stop rawVal val pre pos state state1} :
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      Trivia ctx.fileMap start pos state state1 →
      Token ctx (Syntax.ident (.original l start t stop) rawVal val pre)
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxOk ctx nextPos (Syntax.ident (.original l start t stop) rawVal val pre) pos state stop state1
  | doc {info k args l1 start t1 s1 l2 s2 t2 stop pos state state1 kind} :
      docKind k = true →
      (Syntax.node info k args).getHeadInfo? = some (.original l1 start t1 s1) →
      (Syntax.node info k args).getTailInfo? = some (.original l2 s2 t2 stop) →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      Trivia ctx.fileMap start pos state state1 →
      kind = (if k == ``Parser.Command.moduleDoc then "moddoc" else "doc") →
      SpanCompatible state1 kind start.byteIdx stop.byteIdx →
      SyntaxOk ctx nextPos (Syntax.node info k args) pos state stop
        (insertSpan state1 kind start.byteIdx stop.byteIdx)
  | choice {info first alts pos state stop state1 state2} :
      SyntaxOk ctx nextPos first pos state stop state1 →
      AltsOk ctx nextPos pos stop alts state1 state2 →
      SyntaxOk ctx nextPos (Syntax.node info choiceKind ⟨first :: alts⟩) pos state stop state2
  | singletonAtomNode {info k atomInfo val l start t stop pos state state1} :
      docKind k = false →
      k ≠ choiceKind →
      atomInfo = .original l start t stop →
      pos ≤ start → start ≤ stop → stop ≤ nextPos →
      Trivia ctx.fileMap start pos state state1 →
      Token ctx (Syntax.node info k #[.atom atomInfo val])
        (ctx.extract start stop) (ctx.get stop) →
      SyntaxOk ctx nextPos (Syntax.node info k #[.atom atomInfo val]) pos state stop state1
  | nodeList {info k args pos state stop state'} :
      docKind k = false →
      k ≠ choiceKind →
      (∀ l start t stop val, args ≠ #[.atom (.original l start t stop) val]) →
      ListOk ctx nextPos args.toList pos state stop state' →
      SyntaxOk ctx nextPos (Syntax.node info k args) pos state stop state'
  | other {s pos state} :
      (∀ l start t stop val, s ≠ .atom (.original l start t stop) val) →
      (∀ l start t stop rawVal val pre, s ≠ .ident (.original l start t stop) rawVal val pre) →
      (∀ info k args, s ≠ .node info k args) →
      SyntaxOk ctx nextPos s pos state pos state

inductive AltsOk (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    String.Pos.Raw → String.Pos.Raw → List Syntax → SpanState → SpanState → Prop where
  | nil {pos stop state} : AltsOk ctx nextPos pos stop [] state state
  | cons {pos stop alt rest state state1 state2} :
      SyntaxOk ctx nextPos alt pos state stop state1 →
      AltsOk ctx nextPos pos stop rest state1 state2 →
      AltsOk ctx nextPos pos stop (alt :: rest) state state2

inductive ListOk (ctx : Parser.ParserContextCore) (nextPos : String.Pos.Raw) :
    List Syntax → String.Pos.Raw → SpanState → String.Pos.Raw → SpanState → Prop where
  | nil {pos state} : ListOk ctx nextPos [] pos state pos state
  | cons {arg rest pos state mid state1 stop state2} :
      SyntaxOk ctx nextPos arg pos state mid state1 →
      ListOk ctx nextPos rest mid state1 stop state2 →
      ListOk ctx nextPos (arg :: rest) pos state stop state2

end

inductive RangesOk : List Core.CommandRange → SpanState → SpanState → Prop where
  | nil {state} : RangesOk [] state state
  | cons {r rest state mid state1 state2 state'} :
      r.prevPos ≤ r.nextPos →
      r.nextPos ≤ r.ctx.endPos →
      SyntaxOk r.ctx r.nextPos r.stx r.prevPos state mid state1 →
      Trivia r.ctx.fileMap r.nextPos mid state1 state2 →
      RangesOk rest state2 state' →
      RangesOk (r :: rest) state state'

def Collect (ranges : List Core.CommandRange) (acc : Core.CommentAcc) : Prop :=
  ∃ state', RangesOk ranges (stateOfAcc acc) state'

def cleanStr (s : String) : Bool :=
  !s.toList.any fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x00' || c == '\\'

def stripDotSlashChars : List Char → List Char
  | '.' :: '/' :: rest => stripDotSlashChars rest
  | cs => cs

def stripTrailingSlashRev : List Char → List Char
  | '/' :: rest@(_ :: _) => stripTrailingSlashRev rest
  | cs => cs

def stripDotSlash (s : String) : String :=
  String.ofList (stripDotSlashChars s.toList)

def stripTrailingSlashes (s : String) : String :=
  String.ofList (stripTrailingSlashRev s.toList.reverse).reverse

def validSegmentsBool (s : String) : Bool :=
  (s.splitOn "/").all fun seg => seg != "" && seg != "." && seg != ".."

def ValidRelDir (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    let cleaned := stripTrailingSlashes (stripDotSlash raw)
    (((cleaned == "." || cleaned == "") = true ∧ out = ".") ∨
      (cleaned ≠ "." ∧ cleaned ≠ "" ∧ validSegmentsBool cleaned = true ∧ out = cleaned))

def ValidRelFile (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    (raw.toList.getLast? == some '/') = false ∧
    let cleaned := stripDotSlash raw
    cleaned ≠ "" ∧ cleaned ≠ "." ∧ validSegmentsBool cleaned = true ∧ out = cleaned

def ValidPrefix (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    let cleaned := stripDotSlash raw
    cleaned ≠ "" ∧ cleaned ≠ "." ∧ cleaned ≠ "./" ∧
      let trailing := cleaned.toList.getLast? == some '/'
      let body := if trailing then String.ofList cleaned.toList.dropLast else cleaned
      body ≠ "" ∧ validSegmentsBool body = true ∧ out = (if trailing then body ++ "/" else body)

def prefixMatches (path pfx : String) : Bool :=
  if pfx.toList.getLast? == some '/' then
    pfx.toList.isPrefixOf path.toList
  else
    path == pfx || (pfx.toList ++ ['/']).isPrefixOf path.toList

def cleanStringList (j : Json) : Prop :=
  ∃ arr, j = Json.arr arr ∧ ∀ item ∈ arr.toList, ∃ s, item = Json.str s ∧ cleanStr s = true

def validPrefixList (j : Json) : Prop :=
  ∃ arr, j = Json.arr arr ∧ ∀ item ∈ arr.toList, ∃ s pfx, item = Json.str s ∧ ValidPrefix s pfx

def ValidWorkspaceJson (j : Json) (dirOut : String) : Prop :=
  ∃ obj, j = Json.obj obj ∧
    (∀ k _v, obj.get? k = some _v → k ∈ ["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"]) ∧
    (∃ dirRaw, obj.get? "dir" = some (Json.str dirRaw) ∧ ValidRelDir dirRaw dirOut) ∧
    (match obj.get? "srcDir" with
      | some v => ∃ s out, v = Json.str s ∧ ValidRelDir s out
      | none => True) ∧
    (match obj.get? "lakeArgs" with
      | some v => cleanStringList v
      | none => True) ∧
    (match obj.get? "toolPrefixes" with
      | some v => validPrefixList v
      | none => True) ∧
    (match obj.get? "excludePrefixes" with
      | some v => validPrefixList v
      | none => True)

def ValidExcludeJson (j : Json) : Prop :=
  ∃ obj, j = Json.obj obj ∧
    (∀ k _v, obj.get? k = some _v → k ∈ ["prefix", "reason"]) ∧
    (∃ pfxRaw pfxOut, obj.get? "prefix" = some (Json.str pfxRaw) ∧ ValidPrefix pfxRaw pfxOut) ∧
    (∃ reasonRaw, obj.get? "reason" = some (Json.str reasonRaw) ∧ reasonRaw.trimAscii.toString ≠ "")

def ConfigText (text : String) : Prop :=
  ∃ obj wsArr, ∃ dirs : List String, ∃ ratchetRaw ratchetOut,
    Json.parse text = .ok (Json.obj obj) ∧
    (∀ k _v, obj.get? k = some _v → k ∈ ["workspaces", "exclude", "ratchet"]) ∧
    obj.get? "workspaces" = some (Json.arr wsArr) ∧
    wsArr.size > 0 ∧
    dirs.length = wsArr.size ∧
    dirs.Nodup ∧
    (∀ (i : Nat) (h : i < wsArr.size),
      ∃ hd : i < dirs.length, ValidWorkspaceJson wsArr[i] dirs[i]) ∧
    (match obj.get? "exclude" with
      | some (Json.arr exclArr) => ∀ item ∈ exclArr.toList, ValidExcludeJson item
      | some _ => False
      | none => True) ∧
    obj.get? "ratchet" = some (Json.str ratchetRaw) ∧
    ValidRelFile ratchetRaw ratchetOut

def matchWsRel (w : Config.WorkspaceConfig) (relPath : String) : Option String := do
  let wsRel ←
    if w.dir == "." then
      some relPath
    else
      let prefixChars := w.dir.toList ++ ['/']
      if prefixChars.isPrefixOf relPath.toList then
        some (String.ofList (relPath.toList.drop prefixChars.length))
      else
        none
  if w.excludePrefixes.any (prefixMatches wsRel ·) then none else some wsRel

def ClassifyInput (cfg : Config.RepoConfig) (relPath : String) : Prop :=
  let exclHits := cfg.exclude.toList.filter fun r => prefixMatches relPath r.prefix_
  match exclHits with
  | [_] => True
  | [] => (cfg.workspaces.toList.filterMap fun ws => matchWsRel ws relPath).length = 1
  | _ :: _ :: _ => False

def ClassifyTrackedInput (cfg : Config.RepoConfig) (tracked : Array String) : Prop :=
  ∀ relPath ∈ tracked.toList, ClassifyInput cfg relPath

def isHexLowerChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def isFingerprintStr (s : String) : Prop :=
  s.length = 16 ∧ ∀ c ∈ s.toList, isHexLowerChar c = true

def ValidRatchetEntryJson (j : Json) (fileOut : String) : Prop :=
  ∃ obj fileRaw comments lines fpsJson, ∃ fpsStrs : List String,
    j = Json.obj obj ∧
    (∀ k _v, obj.get? k = some _v → k ∈ ["file", "comments", "lines", "fingerprints"]) ∧
    obj.get? "file" = some (Json.str fileRaw) ∧
    ValidRelFile fileRaw fileOut ∧
    obj.get? "comments" = some (.num ⟨comments, 0⟩) ∧
    comments > 0 ∧
    obj.get? "lines" = some (.num ⟨lines, 0⟩) ∧
    lines > 0 ∧
    obj.get? "fingerprints" = some (Json.arr fpsJson) ∧
    fpsJson.toList = fpsStrs.map Json.str ∧
    fpsStrs.length = comments ∧
    (∀ fp ∈ fpsStrs, isFingerprintStr fp) ∧
    fpsStrs.Pairwise (· ≤ ·)

def RatchetText (text : String) : Prop :=
  ∃ arr, ∃ files : List String,
    Json.parse text = .ok (Json.arr arr) ∧
    files.length = arr.size ∧
    files.Nodup ∧
    ∀ (i : Nat) (h : i < arr.size),
      ∃ hf : i < files.length, ValidRatchetEntryJson arr[i] files[i]

def ExactSyncHolds (analysis : RatchetCore.FileAnalysis) (entry? : Option RatchetCore.RatchetEntry) :
    Prop :=
  match entry? with
  | none => analysis.comments.isEmpty = true ∧ analysis.lines = 0
  | some entry =>
    entry.comments = analysis.comments.size ∧
    entry.lines = analysis.lines ∧
    ∀ a, analysis.fingerprints.values.toList.count a = entry.fingerprints.values.toList.count a

def MonotonicHolds (liveFps : Core.SortedFingerprints) (liveLines : Nat)
    (baseEntry? : Option RatchetCore.RatchetEntry) : Prop :=
  let expFps := match baseEntry? with | some e => e.fingerprints.values.toList | none => []
  let expLines := match baseEntry? with | some e => e.lines | none => 0
  (∀ a, liveFps.values.toList.count a ≤ expFps.count a) ∧ liveLines ≤ expLines

def ValidateInput (analyses : Array RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (targetFile? : Option String) : Prop :=
  (∀ f e, currentRatchet[f]? = some e → f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList) ∧
  (match baseRatchet? with
    | some base => ∀ f e, base[f]? = some e → f ∉ excludedFiles.toList
    | none => True) ∧
  match targetFile? with
  | some target =>
    ∃ live, analyses.find? (·.file == target) = some live ∧
      ExactSyncHolds live currentRatchet[target]? ∧
      match baseRatchet? with
      | some base => MonotonicHolds live.fingerprints live.lines base[target]?
      | none => True
  | none =>
    ∀ a ∈ analyses.toList,
      ExactSyncHolds a currentRatchet[a.file]? ∧
      match baseRatchet? with
      | some base => MonotonicHolds a.fingerprints a.lines base[a.file]?
      | none => True

end NoCommentsSpecification.Healthy
