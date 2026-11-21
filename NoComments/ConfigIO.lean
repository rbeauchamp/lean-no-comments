import NoComments.Config

namespace NoComments.ConfigIO

open NoComments

def loadConfig (configPath : System.FilePath) : IO Config.RepoConfig := do
  let exists_ ← configPath.pathExists
  unless exists_ do
    throw <| IO.userError s!"config file not found: {configPath}"
  let content ← IO.FS.readFile configPath
  match Config.parseConfigJson content with
  | .ok cfg => return cfg
  | .error e => throw <| IO.userError s!"invalid config {configPath}: {e}"

def verifyGitRoot (repoRoot : System.FilePath) : IO System.FilePath := do
  let canonicalRepo ← IO.FS.realPath repoRoot
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", canonicalRepo.toString, "rev-parse", "--show-toplevel"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"not a git repository: {canonicalRepo} ({out.stderr.trimAscii.toString})"
  let canonicalTop ← IO.FS.realPath (System.FilePath.mk out.stdout.trimAscii.toString)
  if canonicalRepo != canonicalTop then
    throw <| IO.userError s!"repository root {canonicalRepo} does not match git toplevel {canonicalTop}"
  return canonicalRepo

def listTrackedLeanFiles (repoRoot : System.FilePath) : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoRoot.toString, "ls-files", "--full-name", "-z", "--", "*.lean"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"git ls-files failed in {repoRoot}: {out.stderr.trimAscii.toString}"
  let rawParts := out.stdout.splitOn "\x00"
  let mut files : Array String := #[]
  for part in rawParts do
    if part != "" then
      match Config.normalizeRelFile "git tracked file" part with
      | .ok norm => files := files.push norm
      | .error e => throw <| IO.userError e
  return files.qsort (· < ·)

def resolveTargetFile (repoRoot : System.FilePath) (rawFile : String) : IO String := do
  let rawPath := System.FilePath.mk rawFile
  let candidate := if rawPath.isAbsolute then rawPath else repoRoot / rawPath
  let canonicalRepo ← IO.FS.realPath repoRoot
  let canonicalFile ← IO.FS.realPath candidate
  let repoStr := canonicalRepo.toString
  let fileStr := canonicalFile.toString
  let prefixStr := if repoStr.endsWith "/" then repoStr else repoStr ++ "/"
  unless fileStr.startsWith prefixStr do
    throw <| IO.userError s!"target file {rawFile} resolves outside repository root {repoStr}"
  let rel := (fileStr.drop prefixStr.length).toString
  match Config.normalizeRelFile "target file" rel with
  | .ok clean => return clean
  | .error e => throw <| IO.userError e

end NoComments.ConfigIO
