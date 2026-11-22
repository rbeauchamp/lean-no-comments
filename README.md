# lean-no-comments

Ratcheted, formally backed ban on comments in Lean 4 repositories (`v4.36.0`).

`no-comments` enforces a zero-growth comment policy across single- or multi-workspace Lean 4 codebases while letting teams drain legacy comments down safely over time. It parses and elaborates every tracked `.lean` file in native compiled workers, extracts every line, block, doc, and module-doc comment using a pure formally verified core (`NoComments.Core`), tracks per-file comment fingerprints and distinct line counts in a checked-in ratchet, and rejects any PR that introduces new comments, increases comment lines, drops tracked files from coverage, or weakens a merge-base ratchet.

## Mission

Comments in Lean 4 codebases tend to drift into three failure modes: restating what the type or proof already expresses, apologizing for weak abstractions instead of fixing them, or drifting out of sync while code and theorems evolve. Rather than waiting for a massive rewrite day, `no-comments` locks the baseline in place immediately—freezing total comments and distinct comment lines across every tracked `.lean` file—and pairs that enforcement with the repeatable [`/delete-comment`](skills/delete-comment/SKILL.md) skill to drive legacy comment counts monotonically toward zero.

## Trusted Computing Base (TCB)

Every check separates a **pure proved core** (`NoCommentsCore`: `NoComments.Core`, `NoComments.Config`, and `NoComments.RatchetCore`—zero `IO`, zero `Lake`, zero `partial`, zero `sorry`, verified under `regula` `standard-logical`) from the **CLI and elaboration harness** (`NoCommentsCLI` and `NoComments.Main`):

### Formally Verified in `NoComments.Core` (Standard Logical Axioms Only)

All 41 theorems in `NoComments/Core.lean` depend solely on standard logical axioms (`[propext, Classical.choice, Quot.sound]` or `[propext, Quot.sound]`):

- **Trivia and syntax byte-interval completeness:** `scanTrivia_coverage`, `checkSlice_coverage`, `collectSyntax_coverage`, `collectRanges_coverage`, and `sourceOrder_mem_iff` prove that `scanTrivia` and `collectSyntax` run with total structural/well-founded recursion (zero `partial` functions) and account for **every single byte** in `[0, endPos)` across every command range—either covered by an original syntax leaf passing `checkToken`, a recorded comment span in `CommentAcc.spans`, or scanned whitespace (`ByteAccounted`).
- **Token boundary safety:** `checkToken_ok_iff` proves a parser token passes `checkToken` if and only if it contains no `--` / `/-` sequence and no `--` / `/-` boundary crossing, parses identically as a literal/identifier, or matches a registered symbol parser.
- **Exact distinct line counting:** `distinctCommentLines_exact` and `distinctCommentLines_unique` prove `distinctCommentLines` computes the exact cardinality of the sorted, duplicate-free union of all line intervals `[startLine, endLine]` covered by detected comments.
- **Ratchet sorting & multiset monotonicity:** `firstOutOfOrder_eq_none_iff`, `sortFingerprints_count`, `missingFrom_count`, `missingFrom_isEmpty_iff`, and `missingFrom_both_isEmpty_iff` prove sortedness validation (`Pairwise (· ≤ ·)`), count-preserving sorting, and exact multiset subset / equality semantics for comment fingerprints.

### Unproved Harness TCB

- Lean `v4.36.0` runtime, dynamic library loader, `Lean.Parser.parseHeader`, `Elab.processHeaderCore`, and `Elab.Frontend.processCommand`.
- `Lake` workspace/environment evaluation (`lake env`, `Lake.loadWorkspace`, `lake setup-file --no-build`) and toolchain version checks (`lean --version` version + commit hash).
- Git invocation (`git ls-files -z -- '*.lean'`, `git merge-base`, `git ls-tree`, `git show`) and the `.no-comments.json` configuration (`workspaces`, `exclude`, `ratchet`).

## Configuration: `.no-comments.json`

Place `.no-comments.json` at the repository root:

```json
{
  "workspaces": [
    {
      "dir": ".",
      "srcDir": ".",
      "lakeArgs": [],
      "toolPrefixes": ["tools/"],
      "excludePrefixes": ["specification/"]
    },
    {
      "dir": "specification",
      "srcDir": "src",
      "lakeArgs": ["-f", "lakefile.toml"],
      "toolPrefixes": [],
      "excludePrefixes": []
    }
  ],
  "exclude": [
    {
      "prefix": "docs/LiterateGuide.lean",
      "reason": "Literate Verso prose document"
    },
    {
      "prefix": "docs/LiterateGuide/",
      "reason": "Literate Verso documentation sections"
    }
  ],
  "ratchet": "tools/comment-ratchet.json"
}
```

### Coverage & Fail-Closed Rules

- **Exhaustive, unambiguous file coverage:** Every tracked `.lean` file returned by `git ls-files --full-name -z -- '*.lean'` must match **at most one** top-level `exclude` rule and, if unexcluded, **exactly one** workspace in `workspaces` (respecting workspace-relative `excludePrefixes`). Any unowned or doubly owned file fails closed.
- **`dir` and `ratchet`:** Repository-relative paths. Top-level `exclude[].prefix` is also repository-relative; `srcDir`, `toolPrefixes`, and `excludePrefixes` inside a workspace are relative to `workspaces[i].dir`. Trailing `/` matches directory trees (`tools/` matches `tools/Check.lean`); paths without `/` match exact files or subtrees (`lakefile.lean` matches only `lakefile.lean`; `docs` matches `docs` or `docs/...`).
- **Toolchain lock:** Before inspecting any workspace, `no-comments` runs `lean --version` in that workspace and fails closed if either the Lean version or commit githash disagrees with the compiled binary.
- **Native worker isolation:** For each file, `no-comments` queries workspace paths once via `lake <lakeArgs> env`, resolves target `leanOptions` / `dynlibs` / `plugins` via Lake (`Lake.loadWorkspace` / `lake setup-file --no-build` and `prepareToolImports` for `toolPrefixes` scripts), loads required dynamic libraries via `Lean.loadDynlib` before initializers/headers, and elaborates in per-file child workers (`--jobs N`) overriding **only** `Elab.async := false`, `debug.byAsSorry := true`, `warningAsError := false`, and `linter.all := false`.

## CLI Reference

```text
no-comments inventory [<file>] [--file <file>] [--json] [--repo <dir>] [--config <path>] [--jobs <n>]
no-comments check [--file <file>] [--base-ref <ref>] [--bootstrap] [--repo <dir>] [--config <path>] [--jobs <n>]
no-comments [--version | --help]
```

### Subcommands & Flags

- `inventory [<file>]`: Audits all checked files (or one target file) and prints per-file counts and repository totals. Pass `--json` to emit the canonical sorted ratchet JSON (`[]` when zero comments remain).
- `check`: Verifies (1) exact sync between live Lean comments and the checked-in ratchet file, and (2) strict monotonicity (`missingFrom live base` empty and `liveLines ≤ baseLines` per file) against the ratchet at `git merge-base HEAD <base-ref>`. Fails closed whenever `merge-base` cannot be computed or `<base-ref>` does not exist.
- `--base-ref <ref>`: Target branch/commit for `merge-base` (defaults to `origin/main` when present, otherwise `main`). Never silently masks a broken `origin/main` merge-base with `main`.
- `--bootstrap`: Admits a missing `<ratchet>` file at the computed merge-base **only** when the merge-base commit is reachable and genuinely lacks `<ratchet>`. If `<ratchet>` already exists at the merge-base, `--bootstrap` still enforces full monotonicity against it.
- `--file <file>`: Targets a single tracked file for fast iterative checks (while still validating repository config coverage and ratchets).
- `--jobs <n>` / `-j <n>`: Number of concurrent per-file worker processes (defaults to `min(cpus, 4)`).
- `--repo <dir>` / `--config <path>`: Run against a specified Git repository root or explicit configuration file path.

## Bootstrap Workflow (2-PR Lifecycle)

1. **PR 1 (Adoption + Baseline Freeze):**
   - Build affected Lake workspaces (`lake build`).
   - Add `.no-comments.json` covering every tracked `.lean` file.
   - Generate the baseline ratchet:
     ```bash
     no-comments inventory --json > comment-ratchet.json
     ```
   - Verify locally and in CI with `--bootstrap`:
     ```bash
     no-comments check --bootstrap --base-ref origin/main
     ```
   - Ensure GitHub Actions uses `actions/checkout` with `fetch-depth: 0` so `git merge-base HEAD origin/main` succeeds.
2. **PR 2+ (Strict Ratchet Enforcement & Drain-Down):**
   - Drop `--bootstrap` in CI so missing ratchets at merge-base always fail closed.
   - Whenever deleting or migrating comments using [`/delete-comment`](skills/delete-comment/SKILL.md), regenerate the ratchet (`no-comments inventory --json > <ratchet>`) and verify `no-comments check` passes before pushing.

## Installation & Verification

### Prebuilt Release Binaries (with SHA-256 Verification)

Download the release binary and `.sha256` file matching your platform (`darwin-arm64` or `linux-x86_64`) from [GitHub Releases](https://github.com/rbeauchamp/lean-no-comments/releases):

```bash
TARGET="linux-x86_64" # or darwin-arm64
VERSION="v0.1.1"
BASE_URL="https://github.com/rbeauchamp/lean-no-comments/releases/download/${VERSION}"

curl -fsSLO "${BASE_URL}/no-comments-${TARGET}"
curl -fsSLO "${BASE_URL}/no-comments-${TARGET}.sha256"

# Verify integrity before executing:
sha256sum -c "no-comments-${TARGET}.sha256" # on macOS: shasum -a 256 -c "no-comments-${TARGET}.sha256"
chmod +x "no-comments-${TARGET}"
./"no-comments-${TARGET}" --version
```

### Build from Source

Requires Lean matching `lean-toolchain` (`leanprover/lean4:v4.36.0`):

```bash
git clone https://github.com/rbeauchamp/lean-no-comments.git
cd lean-no-comments
lake build --wfail
lake lint
lake build no-comments
./.lake/build/bin/no-comments check
```

## Skill Integration

Copy or link [`skills/delete-comment/`](skills/delete-comment/) (`SKILL.md` and `agents/openai.yaml`) into your project or global skills directory so `/delete-comment` automatically discovers `.no-comments.json`, applies the four-category comment audit, migrates true decision records into project documentation, and drains the ratchet cleanly.

## Acknowledgments

Special thanks to [Matt Pocock](https://github.com/mattpocock), whose [November 20, 2026 post](https://x.com/mattpocockuk/status/2123798388227403983) inspired this tool and workflow. His framing—classifying every comment as a tautology, excuse, stale note, or real decision record, then pairing automated comment-ban enforcement with a repeatable refactoring pass—shaped both `no-comments`'s ratcheted zero-growth design and the companion [`/delete-comment`](skills/delete-comment/SKILL.md) skill.

## License

MIT — see [LICENSE](LICENSE).
