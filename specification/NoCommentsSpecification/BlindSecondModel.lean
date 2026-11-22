module

public import Lean.Data.Json
public import LeanIntent.Record
public import NoCommentsSpecification.Types

@[expose] public section

namespace NoCommentsSpecification.BlindSecondModel

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification

def FingerprintText (s : String) : Prop :=
  s.toList.length = 16 ∧
    ∀ c ∈ s.toList, ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')

def NonconstantDigest (f : FingerprintFn) : Prop :=
  ∃ x y, x ≠ y ∧ f x ≠ f y

def Outcome {α : Type} (valid : α → Prop) : Except String α → Prop
  | .ok a => valid a
  | .error _ => ¬ ∃ a, valid a

def Succeeds {α : Type} (r : Except String α) : Prop :=
  ∃ a, r = .ok a

def HasSpan (s : Syntax) (lo hi : Nat) : Prop :=
  s.getPos? = some ⟨lo⟩ ∧ s.getTailPos? = some ⟨hi⟩

inductive Subsyntax : Syntax → Syntax → Prop where
  | self (s : Syntax) : Subsyntax s s
  | nested {info k args child s} :
      child ∈ args.toList → Subsyntax child s →
      Subsyntax (.node info k args) s

def InterpolationChunk (s : Syntax) (lo hi : Nat) : Prop :=
  ∃ (nodeInfo : SourceInfo) (nodeKind : Name) (args : Array Syntax) (chunk : Syntax),
    Subsyntax s (.node nodeInfo nodeKind args) ∧
    chunk ∈ args.toList ∧ HasSpan chunk lo hi ∧
    (chunk.isOfKind `interpolatedStrLit ∨
      ((nodeKind = `interpolatedStr ∨
        nodeKind = `Lean.Parser.Term.interpolatedStr) ∧
        match chunk with | .atom _ _ => True | _ => False))

def LiteralAt (ctx : Parser.ParserContextCore) (tok : Syntax)
    (raw : String) (start : String.Pos.Raw) : Prop :=
  (match tok with | .ident .. => True | _ => False) ∨
  (∃ s, Parser.runParserCategory ctx.env `term raw = .ok s ∧
    (s.isOfKind `str ∨ s.isOfKind `char) ∧ HasSpan s 0 raw.utf8ByteSize) ∨
  (∃ pre left right post : String,
    ctx.inputString = pre ++ left ++ raw ++ right ++ post ∧
    start.byteIdx = pre.utf8ByteSize + left.utf8ByteSize ∧
    ∃ s, Parser.runParserCategory ctx.env `term ("s!" ++ left ++ raw ++ right) = .ok s ∧
      InterpolationChunk s (2 + left.utf8ByteSize)
        (2 + left.utf8ByteSize + raw.utf8ByteSize))

def parserAt (ctx : Parser.ParserContextCore) (p : Parser.ParserFn)
    (start : String.Pos.Raw) : Parser.ParserState :=
  let initial := { (Parser.mkParserState ctx.inputString) with pos := start }
  p.run ctx.toInputContext ctx.toParserModuleContext ctx.tokens initial

def SymbolAt (ctx : Parser.ParserContextCore) (raw : String)
    (start : String.Pos.Raw) : Prop :=
  let p : Parser.ParserFn := Parser.symbolFn raw
  let result := parserAt ctx p start
  ¬ result.hasError ∧
    HasSpan result.stxStack.back start.byteIdx (start.byteIdx + raw.utf8ByteSize)

def OpenerFree (raw : String) (next : Char) : Prop :=
  ¬ (∃ a b : String, raw = a ++ "--" ++ b ∨ raw = a ++ "/-" ++ b) ∧
    ¬ (next = '-' ∧ (raw.endsWith "-" ∨ raw.endsWith "/"))

def SafeToken (ctx : Parser.ParserContextCore) (tok : Syntax) (raw : String)
    (next : Char) (start : String.Pos.Raw) : Prop :=
  LiteralAt ctx tok raw start ∨ SymbolAt ctx raw start ∨ OpenerFree raw next

def OriginalInfo : SourceInfo → Prop
  | .original .. => True
  | _ => False

def docKind (k : Name) : Option String :=
  if k == `Lean.Parser.Command.docComment then some "doc"
  else if k == `Lean.Parser.Command.moduleDoc then some "moddoc"
  else none

inductive SyntaxItem : Syntax → Syntax → Option String → Prop where
  | atom {info val} :
      OriginalInfo info →
      SyntaxItem (.atom info val) (.atom info val) none
  | ident {info spelling val resolution} :
      OriginalInfo info →
      SyntaxItem (.ident info spelling val resolution)
        (.ident info spelling val resolution) none
  | doc {info k args tag} :
      docKind k = some tag →
      SyntaxItem (.node info k args) (.node info k args) (some tag)
  | child {info k args child item tag} :
      docKind k = none → child ∈ args.toList → SyntaxItem child item tag →
      SyntaxItem (.node info k args) item tag

def blockRemainder : List Char → Nat → Option (List Char)
  | [], _ => none
  | '/' :: '-' :: rest, depth => blockRemainder rest (depth + 1)
  | '-' :: '/' :: rest, 0 => some rest
  | '-' :: '/' :: rest, depth + 1 => blockRemainder rest depth
  | _ :: rest, depth => blockRemainder rest depth

def CommentSpelling (raw after kind : String) : Prop :=
  (kind = "line" ∧ raw.startsWith "--" ∧ '\n' ∉ raw.toList ∧
    (after = "" ∨ after.startsWith "\n")) ∨
  (∃ body, raw.toList = '/' :: '-' :: body ∧ blockRemainder body 0 = some [] ∧
    kind = (if raw.startsWith "/--" then "doc"
      else if raw.startsWith "/-!" then "moddoc" else "block"))

def LocatedComment (before raw after : String) (c : Core.Comment) : Prop :=
  CommentSpelling raw after c.kind ∧
    c.startLine = (before.splitOn "\n").length ∧
    c.endLine = ((before ++ raw).splitOn "\n").length ∧
    FingerprintText c.fingerprint

structure ScanPart where
  lo : Nat
  hi : Nat
  item : Option (Syntax × Option String)
  comment : Option Core.Comment

def PartContent (r : Core.CommandRange) (p : ScanPart)
    (before raw after : String) : Prop :=
  match p.item, p.comment with
  | none, none => ∀ c ∈ raw.toList, c.isWhitespace = true
  | none, some c =>
      LocatedComment before raw after c ∧ (c.kind = "line" ∨ c.kind = "block")
  | some (tok, none), none =>
      SyntaxItem r.stx tok none ∧ HasSpan tok p.lo p.hi ∧
      SafeToken r.ctx tok raw (after.toList.head?.getD (Char.ofNat 0)) ⟨p.lo⟩
  | some (tok, some tag), some c =>
      SyntaxItem r.stx tok (some tag) ∧ HasSpan tok p.lo p.hi ∧
      c.kind = tag ∧ LocatedComment before raw after c
  | _, _ => False

def ValidPart (r : Core.CommandRange) (p : ScanPart) : Prop :=
  ∃ before raw after : String,
    r.ctx.inputString = before ++ raw ++ after ∧
    p.lo = before.utf8ByteSize ∧ p.hi = p.lo + raw.utf8ByteSize ∧
    PartContent r p before raw after

def Tiling : Nat → List ScanPart → Nat → Prop
  | lo, [], hi => lo = hi
  | lo, p :: rest, hi => lo = p.lo ∧ Tiling p.hi rest hi

def RangeScan (r : Core.CommandRange) (parts : List ScanPart) : Prop :=
  (∃ before body after : String, r.ctx.inputString = before ++ body ++ after ∧
    r.prevPos.byteIdx = before.utf8ByteSize ∧
    r.nextPos.byteIdx = before.utf8ByteSize + body.utf8ByteSize) ∧
  Tiling r.prevPos.byteIdx parts r.nextPos.byteIdx ∧
  (∀ p ∈ parts, ValidPart r p) ∧
  (∀ tok tag, SyntaxItem r.stx tok tag →
    ∃ p ∈ parts, p.item = some (tok, tag))

def Collected (ranges : List Core.CommandRange) (initial result : Core.CommentAcc) : Prop :=
  ∃ scans : List (Core.CommandRange × List ScanPart),
    scans.map Prod.fst = ranges ∧
    (∀ scan ∈ scans, RangeScan scan.1 scan.2) ∧
    (∀ (k : Nat) (v : Nat × Core.Comment), initial.spans[k]? = some v → result.spans[k]? = some v) ∧
    (∀ scan ∈ scans, ∀ p ∈ scan.2, ∀ c, p.comment = some c →
      result.spans[p.lo]? = some (p.hi, c)) ∧
    (∀ (k : Nat) (v : Nat × Core.Comment), result.spans[k]? = some v →
      initial.spans[k]? = some v ∨
      ∃ scan ∈ scans, ∃ p ∈ scan.2,
        p.lo = k ∧ p.hi = v.1 ∧ p.comment = some v.2)

def InSourceOrder (acc : Core.CommentAcc) (out : Array Core.Comment) : Prop :=
  ∃ entries : List (Nat × (Nat × Core.Comment)),
    entries.Perm acc.spans.toList ∧
    entries.Pairwise (fun a b => a.1 < b.1) ∧
    out.toList = entries.map (fun e => e.2.2)

def coveredLines (c : Core.Comment) : List Nat :=
  let firstLine := max 1 c.startLine
  List.range' firstLine (c.endLine + 1 - firstLine)

def LineCount (comments : Array Core.Comment) (n : Nat) : Prop :=
  n = (comments.toList.flatMap coveredLines).eraseDups.length

def FirstDescent (xs : List String) : Option String → Prop
  | none => xs.Pairwise (· ≤ ·)
  | some b =>
      ∃ pre a rest, xs = pre ++ (a :: b :: rest) ∧
        (pre ++ [a]).Pairwise (· ≤ ·) ∧ b < a

def SameCounts (xs ys : Array String) : Prop :=
  ∀ a : String, xs.toList.count a = ys.toList.count a

def SortedCopy (xs : Array String) (out : Core.SortedFingerprints) : Prop :=
  out.values.toList.Pairwise (· ≤ ·) ∧ SameCounts out.values xs

def Difference (xs ys : Core.SortedFingerprints) (out : Array String) : Prop :=
  ∀ a : String, out.toList.count a = xs.values.toList.count a - ys.values.toList.count a

def CleanText (s : String) : Prop :=
  s ≠ "" ∧ s.trimAscii.toString = s ∧
    ∀ c ∈ s.toList, 32 ≤ c.toNat ∧ c.toNat ≠ 127

def PathSegment (s : String) : Prop :=
  CleanText s ∧ s ≠ "." ∧ s ≠ ".." ∧ '\\' ∉ s.toList

def FilePath (s : String) : Prop :=
  (∀ part ∈ s.splitOn "/", PathSegment part) ∧
    ¬ (∃ drive : Char, drive.isAlpha = true ∧
      s.startsWith (String.ofList [drive, ':', '/']))

def Directory (s : String) : Prop :=
  s = "." ∨ FilePath s

def PrefixPath (s : String) : Prop :=
  FilePath s ∨ ∃ dir, FilePath dir ∧ s = dir ++ "/"

def Fields (j : Json) (keys : List String) : Prop :=
  ∃ obj, j.getObj? = .ok obj ∧ ∀ kv ∈ obj.toList, kv.1 ∈ keys

def Field (j : Json) (key : String) (value : Json) : Prop :=
  j.getObjVal? key = .ok value

def Absent (j : Json) (key : String) : Prop :=
  ¬ ∃ v, Field j key v

def ArrayOf {α : Type} (entry : Json → α → Prop) (j : Json) (out : Array α) : Prop :=
  ∃ items, j.getArr? = .ok items ∧ items.size = out.size ∧
    ∀ i, (hi : i < items.size) → ∃ ho : i < out.size, entry items[i] out[i]

def OptionalField {α : Type} (j : Json) (key : String)
    (entry : Json → α → Prop) (fallback out : α) : Prop :=
  (Absent j key ∧ out = fallback) ∨
    ∃ v, Field j key v ∧ entry v out

def StringValue (valid : String → Prop) (j : Json) (s : String) : Prop :=
  j = .str s ∧ valid s

def WorkspaceValue (j : Json) (w : Config.WorkspaceConfig) : Prop :=
  Fields j ["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"] ∧
    Field j "dir" (.str w.dir) ∧ Directory w.dir ∧
    OptionalField j "srcDir" (StringValue Directory) "." w.srcDir ∧
    OptionalField j "lakeArgs" (ArrayOf (StringValue CleanText)) #[] w.lakeArgs ∧
    OptionalField j "toolPrefixes" (ArrayOf (StringValue PrefixPath)) #[] w.toolPrefixes ∧
    OptionalField j "excludePrefixes" (ArrayOf (StringValue PrefixPath)) #[] w.excludePrefixes

def ExcludeValue (j : Json) (rule : Config.ExcludeRule) : Prop :=
  Fields j ["prefix", "reason"] ∧ Field j "prefix" (.str rule.prefix_) ∧
    PrefixPath rule.prefix_ ∧
    ∃ reason : String, Field j "reason" (.str reason) ∧
      rule.reason = reason.trimAscii.toString ∧ rule.reason ≠ ""

def ConfigText (text : String) (cfg : Config.RepoConfig) : Prop :=
  ∃ j ws, Json.parse text = .ok j ∧ Fields j ["workspaces", "exclude", "ratchet"] ∧
    Field j "workspaces" ws ∧ ArrayOf WorkspaceValue ws cfg.workspaces ∧
    0 < cfg.workspaces.size ∧ (cfg.workspaces.toList.map (·.dir)).Nodup ∧
    OptionalField j "exclude" (ArrayOf ExcludeValue) #[] cfg.exclude ∧
    Field j "ratchet" (.str cfg.ratchet) ∧ FilePath cfg.ratchet

def workspaceRelative (dir path : String) : Option String :=
  if dir == "." then some path
  else if path.startsWith (dir ++ "/") then
    some (String.ofList (path.toList.drop (dir.toList.length + 1)))
  else none

def workspaceHit (cfg : Config.RepoConfig) (path : String) (i : Nat) :
    Option Config.ClassifiedFile := do
  let ws ← cfg.workspaces[i]?
  let rel ← workspaceRelative ws.dir path
  if ws.excludePrefixes.any (fun p => rel.startsWith p) then none
  else some (.checked path i rel (ws.toolPrefixes.any (fun p => rel.startsWith p)))

def Classification (cfg : Config.RepoConfig) (path : String)
    (out : Config.ClassifiedFile) : Prop :=
  let excluded := cfg.exclude.toList.filter (fun rule => path.startsWith rule.prefix_)
  (∃ rule, excluded = [rule] ∧ out = .excluded path rule) ∨
    (excluded = [] ∧ (List.range cfg.workspaces.size).filterMap (workspaceHit cfg path) = [out])

def TrackedClassification (cfg : Config.RepoConfig) (paths : Array String)
    (out : Array Config.ClassifiedFile) : Prop :=
  paths.size = out.size ∧
    ∀ i, (hi : i < paths.size) → ∃ ho : i < out.size, Classification cfg paths[i] out[i]

def AnalysisOf (file : String) (comments : Array Core.Comment)
    (a : RatchetCore.FileAnalysis) : Prop :=
  a.file = file ∧ a.comments = comments ∧ LineCount comments a.lines ∧
    SortedCopy (comments.map (·.fingerprint)) a.fingerprints

abbrev RatchetMap := Std.HashMap String RatchetCore.RatchetEntry

def PositiveNatField (j : Json) (key : String) (n : Nat) : Prop :=
  0 < n ∧ ∃ v, Field j key v ∧ v.getNat? = .ok n

def RatchetValue (j : Json) (e : RatchetCore.RatchetEntry) : Prop :=
  Fields j ["file", "comments", "lines", "fingerprints"] ∧
    Field j "file" (.str e.file) ∧ FilePath e.file ∧
    PositiveNatField j "comments" e.comments ∧ PositiveNatField j "lines" e.lines ∧
    (∃ fps, Field j "fingerprints" fps ∧
      ArrayOf (StringValue FingerprintText) fps e.fingerprints.values) ∧
    e.fingerprints.values.size = e.comments ∧ e.fingerprints.values.toList.Pairwise (· ≤ ·)

def RatchetText (text : String) (out : RatchetMap) : Prop :=
  ∃ (j : Json) (entries : Array RatchetCore.RatchetEntry),
    Json.parse text = .ok j ∧ ArrayOf RatchetValue j entries ∧
    (entries.toList.map (·.file)).Nodup ∧
    ∀ file e, out[file]? = some e ↔ e ∈ entries.toList ∧ e.file = file

def ExactSync (a : RatchetCore.FileAnalysis) : Option RatchetCore.RatchetEntry → Prop
  | none => a.comments.size = 0 ∧ a.lines = 0
  | some e => a.comments.size = e.comments ∧ a.lines = e.lines ∧
      SameCounts a.fingerprints.values e.fingerprints.values

def Monotonic (fps : Core.SortedFingerprints) (lines : Nat)
    (base : Option RatchetCore.RatchetEntry) : Prop :=
  let oldFps := (base.map (fun e => e.fingerprints.values)).getD #[]
  let oldLines := (base.map (fun e => e.lines)).getD 0
  lines ≤ oldLines ∧ ∀ a : String, fps.values.toList.count a ≤ oldFps.toList.count a

def AnalysisPasses (current : RatchetMap) (base : Option RatchetMap)
    (a : RatchetCore.FileAnalysis) : Prop :=
  ExactSync a current[a.file]? ∧
    ∀ b, base = some b → Monotonic a.fingerprints a.lines b[a.file]?

def ValidCheck (analyses : Array RatchetCore.FileAnalysis) (checked excluded : Array String)
    (current : RatchetMap) (base : Option RatchetMap) (target : Option String) : Prop :=
  (∀ file e, current[file]? = some e → file ∉ excluded.toList ∧ file ∈ checked.toList) ∧
    (∀ b, base = some b → ∀ file e, b[file]? = some e → file ∉ excluded.toList) ∧
    (match target with
     | some file => ∃ a ∈ analyses.toList, a.file = file ∧ AnalysisPasses current base a
     | none => ∀ a ∈ analyses.toList, AnalysisPasses current base a)

def isFingerprintRecord : IntentRecord IsFingerprintFn where
  shape := .function _ _
  dom := []
  props := [⟨"recognizesFingerprint", fun f => ∀ s, f s = true ↔ FingerprintText s⟩]
  vocab := [⟨"FingerprintText", String, FingerprintText⟩]

def fingerprintRecord : IntentRecord FingerprintFn where
  shape := .function _ _
  dom := []
  props := [
    ⟨"digestFormat", fun f => ∀ s, FingerprintText (f s)⟩,
    ⟨"nonconstantDigest", NonconstantDigest⟩]
  vocab := [
    ⟨"FingerprintText", String, FingerprintText⟩,
    ⟨"NonconstantDigest", FingerprintFn, NonconstantDigest⟩]

def checkTokenRecord : IntentRecord CheckTokenFn where
  shape := .function _ _
  dom := []
  props := [⟨"acceptsExactlySafeTokens", fun f => ∀ ctx tok raw next start,
    Succeeds (f ctx tok raw next start) ↔ SafeToken ctx tok raw next start⟩]
  vocab := [
    ⟨"Succeeds", Except String Unit, Succeeds⟩,
    ⟨"SafeToken", Parser.ParserContextCore × Syntax × String × Char × String.Pos.Raw,
      fun (ctx, tok, raw, next, start) => SafeToken ctx tok raw next start⟩]

def collectRangesRecord : IntentRecord CollectRangesFn where
  shape := .function _ _
  dom := []
  props := [⟨"collectsRanges", fun f => ∀ ranges acc,
    Outcome (Collected ranges acc) (f ranges acc)⟩]
  vocab := [
    ⟨"Collected", List Core.CommandRange × Core.CommentAcc × Core.CommentAcc,
      fun (ranges, initial, result) => Collected ranges initial result⟩,
    ⟨"Outcome", (Core.CommentAcc → Prop) × Except String Core.CommentAcc,
      fun (p, r) => Outcome p r⟩]

def sourceOrderRecord : IntentRecord SourceOrderFn where
  shape := .function _ _
  dom := []
  props := [⟨"extractsInSourceOrder", fun f => ∀ acc, InSourceOrder acc (f acc)⟩]
  vocab := [⟨"InSourceOrder", Core.CommentAcc × Array Core.Comment,
    fun (acc, cs) => InSourceOrder acc cs⟩]

def distinctCommentLinesRecord : IntentRecord DistinctLinesFn where
  shape := .function _ _
  dom := []
  props := [⟨"countsCoveredLines", fun f => ∀ cs, LineCount cs (f cs)⟩]
  vocab := [⟨"LineCount", Array Core.Comment × Nat, fun (cs, n) => LineCount cs n⟩]

def firstOutOfOrderRecord : IntentRecord FirstOutOfOrderFn where
  shape := .function _ _
  dom := []
  props := [⟨"findsFirstDescent", fun f => ∀ xs, FirstDescent xs (f xs)⟩]
  vocab := [⟨"FirstDescent", List String × Option String,
    fun (xs, result) => FirstDescent xs result⟩]

def sortFingerprintsRecord : IntentRecord SortFingerprintsFn where
  shape := .function _ _
  dom := []
  props := [⟨"sortsPreservingCounts", fun f => ∀ xs, SortedCopy xs (f xs)⟩]
  vocab := [⟨"SortedCopy", Array String × Core.SortedFingerprints,
    fun (xs, result) => SortedCopy xs result⟩]

def missingFromRecord : IntentRecord MissingFromFn where
  shape := .function _ _
  dom := []
  props := [⟨"subtractsCounts", fun f => ∀ xs ys, Difference xs ys (f xs ys)⟩]
  vocab := [⟨"Difference", Core.SortedFingerprints × Core.SortedFingerprints × Array String,
    fun (xs, ys, result) => Difference xs ys result⟩]

def parseConfigRecord : IntentRecord ParseConfigFn where
  shape := .function _ _
  dom := []
  props := [⟨"parsesConfig", fun f => ∀ text, Outcome (ConfigText text) (f text)⟩]
  vocab := [
    ⟨"ConfigText", String × Config.RepoConfig, fun (text, cfg) => ConfigText text cfg⟩,
    ⟨"Outcome", (Config.RepoConfig → Prop) × Except String Config.RepoConfig,
      fun (p, r) => Outcome p r⟩]

def classifyFileRecord : IntentRecord ClassifyFileFn where
  shape := .function _ _
  dom := []
  props := [⟨"classifiesUniqueMatch", fun f => ∀ cfg path,
    Outcome (Classification cfg path) (f cfg path)⟩]
  vocab := [
    ⟨"Classification", Config.RepoConfig × String × Config.ClassifiedFile,
      fun (cfg, path, out) => Classification cfg path out⟩,
    ⟨"Outcome", (Config.ClassifiedFile → Prop) × Except String Config.ClassifiedFile,
      fun (p, r) => Outcome p r⟩]

def classifyTrackedRecord : IntentRecord ClassifyTrackedFn where
  shape := .function _ _
  dom := []
  props := [⟨"classifiesAllInOrder", fun f => ∀ cfg paths,
    Outcome (TrackedClassification cfg paths) (f cfg paths)⟩]
  vocab := [
    ⟨"TrackedClassification", Config.RepoConfig × Array String × Array Config.ClassifiedFile,
      fun (cfg, paths, out) => TrackedClassification cfg paths out⟩,
    ⟨"Outcome", (Array Config.ClassifiedFile → Prop) × Except String (Array Config.ClassifiedFile),
      fun (p, r) => Outcome p r⟩]

def analyzeCommentsRecord : IntentRecord AnalyzeCommentsFn where
  shape := .function _ _
  dom := []
  props := [⟨"summarizesComments", fun f => ∀ file cs, AnalysisOf file cs (f file cs)⟩]
  vocab := [⟨"AnalysisOf", String × Array Core.Comment × RatchetCore.FileAnalysis,
    fun (file, cs, a) => AnalysisOf file cs a⟩]

def parseRatchetRecord : IntentRecord ParseRatchetFn where
  shape := .function _ _
  dom := []
  props := [⟨"parsesRatchet", fun f => ∀ text, Outcome (RatchetText text) (f text)⟩]
  vocab := [
    ⟨"RatchetText", String × RatchetMap, fun (text, out) => RatchetText text out⟩,
    ⟨"Outcome", (RatchetMap → Prop) × Except String RatchetMap, fun (p, r) => Outcome p r⟩]

def checkExactSyncRecord : IntentRecord CheckExactSyncFn where
  shape := .function _ _
  dom := []
  props := [⟨"reportsSyncMismatch", fun f => ∀ a e,
    (f a e).isEmpty = true ↔ ExactSync a e⟩]
  vocab := [⟨"ExactSync", RatchetCore.FileAnalysis × Option RatchetCore.RatchetEntry,
    fun (a, e) => ExactSync a e⟩]

def checkMonotonicFileRecord : IntentRecord CheckMonotonicFn where
  shape := .function _ _
  dom := []
  props := [⟨"reportsRegression", fun f => ∀ file fps comments lines base,
    (f file fps comments lines base).isEmpty = true ↔ Monotonic fps lines base⟩]
  vocab := [⟨"Monotonic", Core.SortedFingerprints × Nat × Option RatchetCore.RatchetEntry,
    fun (fps, lines, base) => Monotonic fps lines base⟩]

def validateCheckRecord : IntentRecord ValidateCheckFn where
  shape := .function _ _
  dom := []
  props := [⟨"validatesRatchetsAndAnalyses", fun f => ∀ analyses checked excluded current base target,
    Succeeds (f analyses checked excluded current base target) ↔
      ValidCheck analyses checked excluded current base target⟩]
  vocab := [
    ⟨"Succeeds", Except String Unit, Succeeds⟩,
    ⟨"ValidCheck", Array RatchetCore.FileAnalysis × Array String × Array String ×
        RatchetMap × Option RatchetMap × Option String,
      fun (analyses, checked, excluded, current, base, target) =>
        ValidCheck analyses checked excluded current base target⟩]

end NoCommentsSpecification.BlindSecondModel