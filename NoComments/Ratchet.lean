import NoComments.RatchetCore

namespace NoComments.Ratchet

open NoComments

def loadCurrentRatchet (repoRoot : System.FilePath) (ratchetRel : String) :
    IO (Std.HashMap String RatchetCore.RatchetEntry) := do
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
  match Lean.Json.parse content >>= RatchetCore.parseRatchetJson with
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
    IO (String × Option (Std.HashMap String RatchetCore.RatchetEntry)) := do
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
  match Lean.Json.parse showOut >>= RatchetCore.parseRatchetJson with
  | .ok m => return (baseSha, some m)
  | .error e => throw <| IO.userError s!"invalid base ratchet at {baseSha}:{ratchetRel}: {e}"

end NoComments.Ratchet
