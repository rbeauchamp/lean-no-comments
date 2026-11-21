import NoComments.Core
import NoComments.Config

namespace NoComments.Ratchet

open NoComments

structure RatchetEntry where
  file : String
  comments : Nat
  lines : Nat
  fingerprints : Core.SortedFingerprints

structure FileAnalysis where
  file : String
  comments : Array Core.Comment
  lines : Nat
  fingerprints : Core.SortedFingerprints

def analyzeComments (file : String) (comments : Array Core.Comment) : FileAnalysis :=
  let fps := Core.sortFingerprints (comments.map (·.fingerprint))
  let lines := Core.distinctCommentLines comments
  { file, comments, lines, fingerprints := fps }

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

def parseRatchetEntry (idx : Nat) (j : Lean.Json) : Except String RatchetEntry := do
  let ctx := s!"ratchet[{idx}]"
  let obj ← j.getObj?
  checkAllowedKeys ctx obj #["file", "comments", "lines", "fingerprints"]
  let fileRaw ← (← getRequiredField ctx obj "file").getStr?
  let file ← Config.normalizeRelFile s!"{ctx}.file" fileRaw
  let comments ← (← getRequiredField ctx obj "comments").getNat?
  let lines ← (← getRequiredField ctx obj "lines").getNat?
  let fpsJson ← (← getRequiredField ctx obj "fingerprints").getArr?
  let fpsRaw ← fpsJson.mapM (·.getStr?)
  if comments == 0 then
    throw s!"{ctx} ({file}) has 0 comments; clean files must be omitted from the ratchet"
  if lines == 0 then
    throw s!"{ctx} ({file}) has comments but lines = 0"
  if fpsRaw.size != comments then
    throw s!"{ctx} ({file}) declares comments = {comments} but has {fpsRaw.size} fingerprints"
  for fp in fpsRaw do
    unless Core.isFingerprint fp do
      throw s!"{ctx} ({file}) contains invalid fingerprint '{fp}'"
  match hord : Core.firstOutOfOrder fpsRaw.toList with
  | some bad =>
    throw s!"{ctx} ({file}) fingerprints are not sorted (out of order at '{bad}')"
  | none =>
    have hsorted : fpsRaw.toList.Pairwise (· ≤ ·) :=
      (Core.firstOutOfOrder_eq_none_iff fpsRaw.toList).mp hord
    return {
      file
      comments
      lines
      fingerprints := ⟨fpsRaw, hsorted⟩
    }

def parseRatchetJson (text : String) : Except String (Std.HashMap String RatchetEntry) := do
  let json ← Lean.Json.parse text
  let arr ← json.getArr?
  let mut map : Std.HashMap String RatchetEntry := {}
  for h : idx in [:arr.size] do
    let entry ← parseRatchetEntry idx arr[idx]
    if map.contains entry.file then
      throw s!"duplicate ratchet entry for '{entry.file}'"
    map := map.insert entry.file entry
  return map

def loadCurrentRatchet (repoRoot : System.FilePath) (ratchetRel : String) :
    IO (Std.HashMap String RatchetEntry) := do
  let path := repoRoot / ratchetRel
  unless (← path.pathExists) do
    throw <| IO.userError s!"ratchet file not found: {path}"
  let meta_ ← path.metadata
  unless meta_.type == .file do
    throw <| IO.userError s!"ratchet path is not a regular file: {path}"
  let real ← IO.FS.realPath path
  unless real == path do
    throw <| IO.userError s!"ratchet path must not be a symlink: {path}"
  let content ← IO.FS.readFile path
  match parseRatchetJson content with
  | .ok m => return m
  | .error e => throw <| IO.userError s!"invalid ratchet file {path}: {e}"

private def runGit (repoRoot : System.FilePath) (args : Array String) :
    IO (UInt32 × String × String) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoRoot.toString] ++ args
  }
  return (out.exitCode, out.stdout, out.stderr)

private def isCommitAvailable (repoRoot : System.FilePath) (rev : String) : IO Bool := do
  let (code, _, _) ← runGit repoRoot #["rev-parse", "--verify", "--quiet", rev ++ "^{commit}"]
  return code == 0

private def computeMergeBase (repoRoot : System.FilePath) (ref : String) : IO String := do
  let (code, out, err) ← runGit repoRoot #["merge-base", "HEAD", ref]
  if code != 0 then
    throw <| IO.userError
      s!"failed to compute git merge-base HEAD {ref}: {err.trimAscii.toString}"
  let sha := out.trimAscii.toString
  if sha == "" then
    throw <| IO.userError s!"git merge-base HEAD {ref} returned empty commit"
  return sha

def resolveBaseCommit (repoRoot : System.FilePath) (baseRef? : Option String) : IO String := do
  match baseRef? with
  | some ref =>
    unless (← isCommitAvailable repoRoot ref) do
      throw <| IO.userError s!"base ref '{ref}' is not a reachable commit in {repoRoot}"
    computeMergeBase repoRoot ref
  | none =>
    if (← isCommitAvailable repoRoot "origin/main") then
      computeMergeBase repoRoot "origin/main"
    else if (← isCommitAvailable repoRoot "main") then
      computeMergeBase repoRoot "main"
    else
      throw <| IO.userError
        "neither 'origin/main' nor 'main' exists; pass --base-ref <ref> with full history (git fetch --unshallow or fetch-depth: 0)"

private def parseTreeEntryMode (lsOut : String) : Option String := do
  let first := (lsOut.splitOn "\x00").headD ""
  if first == "" then none
  else
    let metaPart := (first.splitOn "\t").headD ""
    let mode := (metaPart.splitOn " ").headD ""
    if mode == "" then none else some mode

private def commitPathMode? (repoRoot : System.FilePath) (commit relPath : String) :
    IO (Option String) := do
  let (lsCode, lsOut, lsErr) ← runGit repoRoot #["ls-tree", "-z", "--full-tree", commit, "--", relPath]
  if lsCode != 0 then
    throw <| IO.userError s!"git ls-tree failed at {commit}: {lsErr.trimAscii.toString}"
  return parseTreeEntryMode lsOut

def resolveBaseRatchet (repoRoot : System.FilePath) (ratchetRel : String)
    (baseRef? : Option String) (bootstrap : Bool) :
    IO (String × Option (Std.HashMap String RatchetEntry)) := do
  let baseSha ← resolveBaseCommit repoRoot baseRef?
  let some mode ← commitPathMode? repoRoot baseSha ratchetRel
    | do
      if bootstrap then
        return (baseSha, none)
      else
        throw <| IO.userError
          s!"missing '{ratchetRel}' at merge-base {baseSha}; pass --bootstrap only when adopting comment-ban for the first time"
  unless mode == "100644" || mode == "100755" do
    throw <| IO.userError s!"{baseSha}:{ratchetRel} has unsupported git mode '{mode}' (expected regular file blob)"
  let (typeCode, typeOut, typeErr) ← runGit repoRoot #["cat-file", "-t", s!"{baseSha}:{ratchetRel}"]
  if typeCode != 0 then
    throw <| IO.userError s!"git cat-file -t failed for {baseSha}:{ratchetRel}: {typeErr.trimAscii.toString}"
  if typeOut.trimAscii.toString != "blob" then
    throw <| IO.userError s!"{baseSha}:{ratchetRel} is not a regular file blob"
  let (showCode, showOut, showErr) ← runGit repoRoot #["show", s!"{baseSha}:{ratchetRel}"]
  if showCode != 0 then
    throw <| IO.userError s!"git show {baseSha}:{ratchetRel} failed: {showErr.trimAscii.toString}"
  match parseRatchetJson showOut with
  | .ok m => return (baseSha, some m)
  | .error e => throw <| IO.userError s!"invalid base ratchet at {baseSha}:{ratchetRel}: {e}"

private def checkExactSync (analysis : FileAnalysis) (entry? : Option RatchetEntry) :
    Array String := Id.run do
  let mut errs : Array String := #[]
  match entry? with
  | none =>
    if !analysis.comments.isEmpty || analysis.lines != 0 then
      errs := errs.push
        s!"{analysis.file}: has {analysis.comments.size} comment(s) across {analysis.lines} line(s), but is missing from the checked-in ratchet"
  | some entry =>
    if entry.comments != analysis.comments.size then
      errs := errs.push
        s!"{analysis.file}: checked-in ratchet declares {entry.comments} comment(s), found {analysis.comments.size}"
    if entry.lines != analysis.lines then
      errs := errs.push
        s!"{analysis.file}: checked-in ratchet declares {entry.lines} line(s), found {analysis.lines}"
    let extraInLive := Core.missingFrom analysis.fingerprints entry.fingerprints
    let missingFromLive := Core.missingFrom entry.fingerprints analysis.fingerprints
    unless extraInLive.isEmpty && missingFromLive.isEmpty do
      errs := errs.push
        s!"{analysis.file}: fingerprint multiset differs from checked-in ratchet (unexpected: {extraInLive.size}, stale: {missingFromLive.size})"
  return errs

private def checkMonotonicFile (file : String) (liveFps : Core.SortedFingerprints)
    (liveComments liveLines : Nat) (baseEntry? : Option RatchetEntry) : Array String := Id.run do
  let mut errs : Array String := #[]
  let (expFps, expComments, expLines) := match baseEntry? with
    | some e => (e.fingerprints, e.comments, e.lines)
    | none => (Core.SortedFingerprints.empty, 0, 0)
  let added := Core.missingFrom liveFps expFps
  unless added.isEmpty do
    errs := errs.push
      s!"{file}: added {added.size} new/modified comment(s) above merge-base ratchet ({liveComments} vs base {expComments})"
  if liveLines > expLines then
    errs := errs.push
      s!"{file}: comment line count increased from {expLines} to {liveLines}"
  return errs

def validateCheck (analyses : Array FileAnalysis) (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetEntry))
    (targetFile? : Option String) : Except String Unit := do
  let mut errs : Array String := #[]
  for (f, _) in currentRatchet.toList do
    if excludedFiles.contains f then
      errs := errs.push s!"checked-in ratchet contains excluded file '{f}'"
    else unless checkedFiles.contains f do
      errs := errs.push s!"checked-in ratchet contains unknown or untracked file '{f}'"
  if let some baseRatchet := baseRatchet? then
    for (f, _) in baseRatchet.toList do
      if excludedFiles.contains f then
        errs := errs.push s!"cannot exclude '{f}' because merge-base ratchet still tracks comments in it"
  match targetFile? with
  | some target =>
    let some live := analyses.find? (·.file == target)
      | throw s!"missing analysis for target file '{target}'"
    errs := errs ++ checkExactSync live currentRatchet[target]?
    if let some baseRatchet := baseRatchet? then
      errs := errs ++ checkMonotonicFile target live.fingerprints live.comments.size live.lines
        baseRatchet[target]?
  | none =>
    let mut liveMap : Std.HashMap String FileAnalysis := {}
    for a in analyses do
      liveMap := liveMap.insert a.file a
      errs := errs ++ checkExactSync a currentRatchet[a.file]?
      if let some baseRatchet := baseRatchet? then
        errs := errs ++ checkMonotonicFile a.file a.fingerprints a.comments.size a.lines
          baseRatchet[a.file]?
    if let some baseRatchet := baseRatchet? then
      for (f, _) in baseRatchet.toList do
        unless liveMap.contains f do
          errs := errs ++ checkMonotonicFile f Core.SortedFingerprints.empty 0 0 baseRatchet[f]?
  unless errs.isEmpty do
    throw (String.intercalate "\n" errs.toList)

end NoComments.Ratchet
