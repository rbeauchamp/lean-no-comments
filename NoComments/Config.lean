module

public import Lean.Data.Json

namespace NoComments.Config

public section

structure WorkspaceConfig where
  dir : String
  srcDir : String
  lakeArgs : Array String
  toolPrefixes : Array String
  excludePrefixes : Array String
  deriving @[expose] Repr, @[expose] BEq, @[expose] Inhabited

structure ExcludeRule where
  prefix_ : String
  reason : String
  deriving @[expose] Repr, @[expose] BEq, @[expose] Inhabited

structure RepoConfig where
  workspaces : Array WorkspaceConfig
  exclude : Array ExcludeRule
  ratchet : String
  deriving @[expose] Repr, @[expose] BEq, @[expose] Inhabited

inductive ClassifiedFile where
  | excluded (relPath : String) (rule : ExcludeRule)
  | checked (relPath : String) (wsIdx : Nat) (wsRelPath : String) (isTool : Bool)
  deriving @[expose] Repr, @[expose] BEq

def hasControlOrSlashIssue (s : String) : Bool :=
  s.any fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x00' || c == '\\'

private def stripLeadingDotSlashChars : List Char → List Char
  | '.' :: '/' :: rest => stripLeadingDotSlashChars rest
  | cs => cs

def stripLeadingDotSlash (s : String) : String :=
  String.ofList (stripLeadingDotSlashChars s.toList)

private def stripTrailingSlashRev : List Char → List Char
  | '/' :: rest@(_ :: _) => stripTrailingSlashRev rest
  | cs => cs

def stripTrailingSlashes (s : String) : String :=
  String.ofList (stripTrailingSlashRev s.toList.reverse).reverse

def validateSegments (context raw : String) (segs : List String) : Except String Unit := do
  for seg in segs do
    if seg == "" || seg == "." || seg == ".." then
      throw s!"{context} '{raw}' contains invalid path segment '{seg}'"

def normalizeRelDir (context raw : String) : Except String String := do
  if raw == "" then
    throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" then
    throw s!"{context} '{raw}' must be a clean repo-relative directory path"
  let cleaned := stripTrailingSlashes (stripLeadingDotSlash raw)
  if cleaned == "." || cleaned == "" then
    return "."
  validateSegments context raw (cleaned.splitOn "/")
  return cleaned

def normalizeRelFile (context raw : String) : Except String String := do
  if raw == "" then
    throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" || raw.endsWith "/" then
    throw s!"{context} '{raw}' must be a clean relative file path"
  let cleaned := stripLeadingDotSlash raw
  if cleaned == "" || cleaned == "." then
    throw s!"{context} '{raw}' must name a file"
  validateSegments context raw (cleaned.splitOn "/")
  return cleaned

def normalizePrefix (context raw : String) : Except String String := do
  if raw == "" then
    throw s!"{context} must not be empty"
  if hasControlOrSlashIssue raw || raw.startsWith "/" then
    throw s!"{context} '{raw}' must be a clean relative prefix"
  let cleaned := stripLeadingDotSlash raw
  if cleaned == "" || cleaned == "." || cleaned == "./" then
    throw s!"{context} '{raw}' must not match the entire root"
  let trailingSlash := cleaned.endsWith "/"
  let body := if trailingSlash then (cleaned.dropEnd 1).toString else cleaned
  if body == "" then
    throw s!"{context} '{raw}' must not be empty"
  validateSegments context raw (body.splitOn "/")
  return if trailingSlash then body ++ "/" else body

def prefixMatches (path pfx : String) : Bool :=
  if pfx.endsWith "/" then
    path.startsWith pfx
  else
    path == pfx || path.startsWith (pfx ++ "/")

private def checkAllowedKeys (context : String) (obj : Std.TreeMap.Raw String Lean.Json compare)
    (allowed : Array String) : Except String Unit := do
  for (k, _) in obj.toList do
    unless allowed.contains k do
      throw s!"unknown key '{k}' in {context}"

private def getRequiredField (context : String) (obj : Std.TreeMap.Raw String Lean.Json compare)
    (key : String) : Except String Lean.Json :=
  match obj.get? key with
  | some v => .ok v
  | none => .error s!"missing required field '{key}' in {context}"

private def parseStringArray (context : String) (j : Lean.Json) : Except String (Array String) := do
  let arr ← j.getArr?
  arr.mapM fun item => do
    let s ← item.getStr?
    if hasControlOrSlashIssue s then
      throw s!"invalid control character in {context} entry"
    return s

private def parseWorkspace (idx : Nat) (j : Lean.Json) : Except String WorkspaceConfig := do
  let ctx := s!"workspaces[{idx}]"
  let obj ← j.getObj?
  checkAllowedKeys ctx obj #["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"]
  let dirRaw ← (← getRequiredField ctx obj "dir").getStr?
  let dir ← normalizeRelDir s!"{ctx}.dir" dirRaw
  let srcDir ← match obj.get? "srcDir" with
    | some v => normalizeRelDir s!"{ctx}.srcDir" (← v.getStr?)
    | none => pure "."
  let lakeArgs ← match obj.get? "lakeArgs" with
    | some v => parseStringArray s!"{ctx}.lakeArgs" v
    | none => pure #[]
  let toolPrefixes ← match obj.get? "toolPrefixes" with
    | some v =>
      let rawArr ← parseStringArray s!"{ctx}.toolPrefixes" v
      rawArr.mapM (normalizePrefix s!"{ctx}.toolPrefixes")
    | none => pure #[]
  let excludePrefixes ← match obj.get? "excludePrefixes" with
    | some v =>
      let rawArr ← parseStringArray s!"{ctx}.excludePrefixes" v
      rawArr.mapM (normalizePrefix s!"{ctx}.excludePrefixes")
    | none => pure #[]
  return { dir, srcDir, lakeArgs, toolPrefixes, excludePrefixes }

private def parseExcludeRule (idx : Nat) (j : Lean.Json) : Except String ExcludeRule := do
  let ctx := s!"exclude[{idx}]"
  let obj ← j.getObj?
  checkAllowedKeys ctx obj #["prefix", "reason"]
  let pfxRaw ← (← getRequiredField ctx obj "prefix").getStr?
  let prefix_ ← normalizePrefix s!"{ctx}.prefix" pfxRaw
  let reasonRaw ← (← getRequiredField ctx obj "reason").getStr?
  let reason := reasonRaw.trimAscii.toString
  if reason == "" then
    throw s!"{ctx}.reason must not be empty"
  return { prefix_, reason }

def parseConfigJson (json : Lean.Json) : Except String RepoConfig := do
  let obj ← json.getObj?
  checkAllowedKeys "config" obj #["workspaces", "exclude", "ratchet"]
  let wsArr ← (← getRequiredField "config" obj "workspaces").getArr?
  if wsArr.isEmpty then
    throw "config.workspaces must contain at least one workspace"
  let mut workspaces := Array.emptyWithCapacity wsArr.size
  let mut seenDirs : Array String := #[]
  for h : idx in [:wsArr.size] do
    let ws ← parseWorkspace idx wsArr[idx]
    if seenDirs.contains ws.dir then
      throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
    seenDirs := seenDirs.push ws.dir
    workspaces := workspaces.push ws
  let exclude ← match obj.get? "exclude" with
    | some v =>
      let exclArr ← v.getArr?
      let mut rules := Array.emptyWithCapacity exclArr.size
      for h : idx in [:exclArr.size] do
        rules := rules.push (← parseExcludeRule idx exclArr[idx])
      pure rules
    | none => pure #[]
  let ratchetRaw ← (← getRequiredField "config" obj "ratchet").getStr?
  let ratchet ← normalizeRelFile "config.ratchet" ratchetRaw
  return { workspaces, exclude, ratchet }

def matchWorkspace (w : WorkspaceConfig) (relPath : String) : Option String := do
  let wsRel ←
    if w.dir == "." then
      some relPath
    else
      let prefix_ := w.dir ++ "/"
      if relPath.startsWith prefix_ then
        some (relPath.drop prefix_.length).toString
      else
        none
  if w.excludePrefixes.any (prefixMatches wsRel ·) then
    none
  else
    some wsRel

def classifyFile (cfg : RepoConfig) (relPath : String) : Except String ClassifiedFile := do
  let mut exclMatches : Array ExcludeRule := #[]
  for rule in cfg.exclude do
    if prefixMatches relPath rule.prefix_ then
      exclMatches := exclMatches.push rule
  match exclMatches.toList with
  | [rule] =>
    return .excluded relPath rule
  | [] =>
    let mut wsMatches : Array (WorkspaceConfig × Nat × String) := #[]
    for h : idx in [:cfg.workspaces.size] do
      let ws := cfg.workspaces[idx]
      if let some wsRel := matchWorkspace ws relPath then
        wsMatches := wsMatches.push (ws, idx, wsRel)
    match wsMatches.toList with
    | [] =>
      throw s!"tracked Lean file '{relPath}' does not match any workspace or exclude rule in config"
    | [(ws, wsIdx, wsRel)] =>
      let isTool := ws.toolPrefixes.any (prefixMatches wsRel ·)
      return .checked relPath wsIdx wsRel isTool
    | _ =>
      throw s!"tracked Lean file '{relPath}' matches multiple workspaces in config"
  | _ =>
    throw s!"tracked Lean file '{relPath}' matches multiple top-level exclude rules"

def classifyTrackedFiles (cfg : RepoConfig) (tracked : Array String) :
    Except String (Array ClassifiedFile) :=
  tracked.mapM (classifyFile cfg)

end

end NoComments.Config
