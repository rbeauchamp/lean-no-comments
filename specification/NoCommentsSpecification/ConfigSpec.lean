module

public import Lean.Data.Json
public import NoCommentsSpecification.Types

@[expose] public section

namespace NoCommentsSpecification.ConfigSpec

open Lean
open NoComments

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

def NormRelDir (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    let cleaned := stripTrailingSlashes (stripDotSlash raw)
    (((cleaned == "." || cleaned == "") = true ∧ out = ".") ∨
      (cleaned ≠ "." ∧ cleaned ≠ "" ∧ validSegmentsBool cleaned = true ∧ out = cleaned))

def NormRelFile (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    (raw.toList.getLast? == some '/') = false ∧
    let cleaned := stripDotSlash raw
    cleaned ≠ "" ∧ cleaned ≠ "." ∧ validSegmentsBool cleaned = true ∧ out = cleaned

def NormPrefix (raw out : String) : Prop :=
  raw ≠ "" ∧ cleanStr raw = true ∧ (raw.toList.head? == some '/') = false ∧
    let cleaned := stripDotSlash raw
    cleaned ≠ "" ∧ cleaned ≠ "." ∧ cleaned ≠ "./" ∧
      let trailing := cleaned.toList.getLast? == some '/'
      let body := if trailing then String.ofList cleaned.toList.dropLast else cleaned
      body ≠ "" ∧ validSegmentsBool body = true ∧ out = (if trailing then body ++ "/" else body)

def PrefixMatches (path pfx : String) : Bool :=
  if pfx.toList.getLast? == some '/' then
    pfx.toList.isPrefixOf path.toList
  else
    path == pfx || (pfx.toList ++ ['/']).isPrefixOf path.toList

def ValidCleanStringArray (j : Json) (out : Array String) : Prop :=
  ∃ arr, j = Json.arr arr ∧
    out.size = arr.size ∧
    ∀ (i : Nat) (_h : i < arr.size),
      ∃ (_ho : i < out.size), arr[i] = Json.str out[i] ∧ cleanStr out[i] = true

def ValidPrefixArray (j : Json) (out : Array String) : Prop :=
  ∃ arr, j = Json.arr arr ∧
    out.size = arr.size ∧
    ∀ (i : Nat) (_h : i < arr.size),
      ∃ (_ho : i < out.size), ∃ raw, arr[i] = Json.str raw ∧ NormPrefix raw out[i]

def ValidWorkspaceJson (j : Json) (ws : Config.WorkspaceConfig) : Prop :=
  ∃ obj dirRaw,
    j = Json.obj obj ∧
    (∀ kv ∈ obj.toList, kv.1 ∈ ["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"]) ∧
    obj.get? "dir" = some (Json.str dirRaw) ∧
    NormRelDir dirRaw ws.dir ∧
    (match obj.get? "srcDir" with
      | some v => ∃ srcRaw, v = Json.str srcRaw ∧ NormRelDir srcRaw ws.srcDir
      | none => ws.srcDir = ".") ∧
    (match obj.get? "lakeArgs" with
      | some v => ValidCleanStringArray v ws.lakeArgs
      | none => ws.lakeArgs = #[]) ∧
    (match obj.get? "toolPrefixes" with
      | some v => ValidPrefixArray v ws.toolPrefixes
      | none => ws.toolPrefixes = #[]) ∧
    (match obj.get? "excludePrefixes" with
      | some v => ValidPrefixArray v ws.excludePrefixes
      | none => ws.excludePrefixes = #[])

def ValidExcludeJson (j : Json) (r : Config.ExcludeRule) : Prop :=
  ∃ obj pfxRaw reasonRaw,
    j = Json.obj obj ∧
    (∀ kv ∈ obj.toList, kv.1 ∈ ["prefix", "reason"]) ∧
    obj.get? "prefix" = some (Json.str pfxRaw) ∧
    NormPrefix pfxRaw r.prefix_ ∧
    obj.get? "reason" = some (Json.str reasonRaw) ∧
    reasonRaw.trimAscii.toString = r.reason ∧
    r.reason ≠ ""

def ValidConfigJson (text : String) (cfg : Config.RepoConfig) : Prop :=
  ∃ obj wsArr ratchetRaw,
    Json.parse text = .ok (Json.obj obj) ∧
    (∀ kv ∈ obj.toList, kv.1 ∈ ["workspaces", "exclude", "ratchet"]) ∧
    obj.get? "workspaces" = some (Json.arr wsArr) ∧
    wsArr.size > 0 ∧
    cfg.workspaces.size = wsArr.size ∧
    (∀ (i : Nat) (_h : i < wsArr.size),
      ∃ (_hc : i < cfg.workspaces.size), ValidWorkspaceJson wsArr[i] cfg.workspaces[i]) ∧
    (cfg.workspaces.toList.map (·.dir)).Nodup ∧
    (match obj.get? "exclude" with
      | some (Json.arr exclArr) =>
        cfg.exclude.size = exclArr.size ∧
          ∀ (i : Nat) (_h : i < exclArr.size),
            ∃ (_hc : i < cfg.exclude.size), ValidExcludeJson exclArr[i] cfg.exclude[i]
      | some _ => False
      | none => cfg.exclude = #[]) ∧
    obj.get? "ratchet" = some (Json.str ratchetRaw) ∧
    NormRelFile ratchetRaw cfg.ratchet

inductive ConfigRefusal (text : String) : Prop where
  | badJson : (∀ j, Json.parse text ≠ .ok j) → ConfigRefusal text
  | notObject {j} : Json.parse text = .ok j → (∀ obj, j ≠ Json.obj obj) → ConfigRefusal text
  | unknownRootKey {obj k v} :
      Json.parse text = .ok (Json.obj obj) →
      (k, v) ∈ obj.toList →
      k ∉ ["workspaces", "exclude", "ratchet"] →
      ConfigRefusal text
  | badWorkspacesField {obj} :
      Json.parse text = .ok (Json.obj obj) →
      (∀ wsArr, obj.get? "workspaces" = some (Json.arr wsArr) → wsArr.size = 0) →
      ConfigRefusal text
  | invalidWorkspace {obj wsArr i} (hi : i < wsArr.size) :
      Json.parse text = .ok (Json.obj obj) →
      obj.get? "workspaces" = some (Json.arr wsArr) →
      (∀ ws, ¬ ValidWorkspaceJson wsArr[i] ws) →
      ConfigRefusal text
  | duplicateWorkspaceDir {obj wsArr i j ws1 ws2} (hi : i < wsArr.size) (hj : j < wsArr.size) :
      Json.parse text = .ok (Json.obj obj) →
      obj.get? "workspaces" = some (Json.arr wsArr) →
      i ≠ j →
      ValidWorkspaceJson wsArr[i] ws1 →
      ValidWorkspaceJson wsArr[j] ws2 →
      ws1.dir = ws2.dir →
      ConfigRefusal text
  | badExcludeField {obj v} :
      Json.parse text = .ok (Json.obj obj) →
      obj.get? "exclude" = some v →
      (∀ exclArr, v ≠ Json.arr exclArr) →
      ConfigRefusal text
  | invalidExcludeRule {obj exclArr i} (hi : i < exclArr.size) :
      Json.parse text = .ok (Json.obj obj) →
      obj.get? "exclude" = some (Json.arr exclArr) →
      (∀ r, ¬ ValidExcludeJson exclArr[i] r) →
      ConfigRefusal text
  | badRatchetField {obj} :
      Json.parse text = .ok (Json.obj obj) →
      (∀ raw out, obj.get? "ratchet" = some (Json.str raw) → ¬ NormRelFile raw out) →
      ConfigRefusal text

def MatchWorkspace (w : Config.WorkspaceConfig) (relPath : String) : Option String := do
  let wsRel ←
    if w.dir == "." then
      some relPath
    else
      let prefixChars := w.dir.toList ++ ['/']
      if prefixChars.isPrefixOf relPath.toList then
        some (String.ofList (relPath.toList.drop prefixChars.length))
      else
        none
  if w.excludePrefixes.any (PrefixMatches wsRel ·) then none else some wsRel

def ClassifyOutcome (cfg : Config.RepoConfig) (relPath : String) (out : Config.ClassifiedFile) : Prop :=
  let exclHits := cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_
  (∃ rule, exclHits = [rule] ∧ out = .excluded relPath rule) ∨
    (exclHits = [] ∧
      ∃ ws wsIdx wsRel,
        (cfg.workspaces.toList.zipIdx.filterMap fun (w, idx) =>
          (MatchWorkspace w relPath).map fun r => (w, idx, r)) = [(ws, wsIdx, wsRel)] ∧
        out = .checked relPath wsIdx wsRel (ws.toolPrefixes.any (PrefixMatches wsRel ·)))

inductive ClassifyRefusal (cfg : Config.RepoConfig) (relPath : String) : Prop where
  | ambiguousExclude :
      (cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_).length ≥ 2 →
      ClassifyRefusal cfg relPath
  | unmatched :
      (cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_) = [] →
      (cfg.workspaces.toList.filterMap fun w => MatchWorkspace w relPath) = [] →
      ClassifyRefusal cfg relPath
  | ambiguousWorkspace :
      (cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_) = [] →
      (cfg.workspaces.toList.filterMap fun w => MatchWorkspace w relPath).length ≥ 2 →
      ClassifyRefusal cfg relPath

def ClassifyTrackedOutcome (cfg : Config.RepoConfig) (tracked : Array String)
    (out : Array Config.ClassifiedFile) : Prop :=
  out.size = tracked.size ∧
    ∀ (i : Nat) (_ht : i < tracked.size),
      ∃ (_ho : i < out.size), ClassifyOutcome cfg tracked[i] out[i]

def ClassifyTrackedRefusal (cfg : Config.RepoConfig) (tracked : Array String) : Prop :=
  ∃ relPath ∈ tracked.toList, ClassifyRefusal cfg relPath

end NoCommentsSpecification.ConfigSpec
