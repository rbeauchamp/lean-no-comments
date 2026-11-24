# lean-no-comments

Ratcheted, formally backed ban on comments in Lean 4 repositories (`v4.36.0`).

`no-comments` enforces a zero-growth comment policy across single- or multi-workspace Lean 4 codebases while letting teams drain legacy comments down safely over time. It parses and elaborates every tracked `.lean` file in native compiled workers, extracts every line, block, doc, and module-doc comment using a pure formally verified core (`NoComments.Core`), tracks per-file comment fingerprints and distinct line counts in a checked-in ratchet, and rejects any PR that introduces new comments, increases comment lines, drops tracked files from coverage, or weakens a merge-base ratchet.

## Mission

Comments in Lean 4 codebases tend to drift into three failure modes: restating what the type or proof already expresses, apologizing for weak abstractions instead of fixing them, or drifting out of sync while code and theorems evolve. Rather than waiting for a massive rewrite day, `no-comments` locks the baseline in place immediately—freezing total comments and distinct comment lines across every tracked `.lean` file—and pairs that enforcement with the repeatable [`/delete-comment`](skills/delete-comment/SKILL.md) skill to drive legacy comment counts monotonically toward zero.

## Trusted Computing Base (TCB)

Every check separates a **pure, linted core** (`NoCommentsCore`: `NoComments.Core`, `NoComments.Config`, and `NoComments.RatchetCore`—zero `IO`, zero `Lake`, zero `partial`, zero `sorry`, checked under `regula` `standard-logical`, with kernel-checked proofs in `NoComments.Core` and `specification/`'s `NoCommentsSpecification` proving adequacy, blind second-model comparison, owner confirmation via `LeanIntent.Confirmation`, end-to-end refinement for all 17 pure contracts, required-theorem coverage, and IR reachability from `no-comments` via `LeanIntent.Execution`) from the **CLI and elaboration harness** (`NoCommentsCLI` and `NoComments.Main`; see [specification/README.md](specification/README.md) and [specification/confirmation.md](specification/confirmation.md) for formal accounting and remaining trusted-base boundaries):

### Formally Verified Across `NoComments.Core` and `specification/`

Every theorem in `NoComments/Core.lean` and `specification/NoCommentsSpecification/` depends solely on standard logical axioms (`[propext, Classical.choice, Quot.sound]` or subsets thereof), verified under `regula/lint` (`standard-logical`) and `lake exe spec-check`:

- **Trivia and syntax byte-interval completeness:** `scanTrivia_coverage`, `checkSlice_coverage`, `collectSyntax_coverage`, `collectRanges_coverage`, and `sourceOrder_mem_iff` (with `collectRanges_meets` and `sourceOrder_meets` in `NoCommentsSpecification.Refinement.Core`) prove that `scanTrivia` and `collectSyntax` run with total structural/well-founded recursion (zero `partial` functions) and account for **every single byte** in `[0, endPos)` across every command range—either covered by an original syntax leaf passing `checkToken`, a recorded comment span in `CommentAcc.spans`, or scanned whitespace (`ByteAccounted`).
- **Token boundary safety:** `checkToken_ok_iff` and `checkToken_meets` prove a parser token passes `checkToken` if and only if it contains no `--` / `/-` sequence and no `--` / `/-` boundary crossing, parses identically as a literal/identifier, or matches a registered symbol parser.
- **Exact distinct line counting and comment extraction:** `distinctCommentLines_exact`, `distinctCommentLines_unique`, `isFingerprint_meets`, `fingerprint_meets`, `distinctCommentLines_meets`, and `analyzeComments_meets` establish exact cardinality of the sorted duplicate-free line union, 16-char lowercase hex fingerprints, and pure per-file comment summaries.
- **Ratchet sorting, multiset monotonicity, and check validation:** `firstOutOfOrder_eq_none_iff`, `sortFingerprints_count`, `missingFrom_count`, `missingFrom_isEmpty_iff`, `missingFrom_both_isEmpty_iff`, `parseRatchetJson_meets`, `checkExactSync_meets`, `checkMonotonicFile_meets`, and `validateCheck_meets` prove sortedness validation (`Pairwise (· ≤ ·)`), count-preserving sorting, exact multiset subset/equality semantics, ratchet JSON validation, exact sync, and strict downward merge-base monotonicity.
- **Configuration parsing and exhaustive unambiguous classification:** `parseConfigJson_meets`, `classifyFile_meets`, and `classifyTrackedFiles_meets` prove strict `.no-comments.json` normalization/schema validation and fail-closed classification where every tracked file matches at most one `exclude` prefix and (when unexcluded) exactly one workspace.

### Unproved Harness TCB (`NoCommentsCLI` and External Boundaries)

- Unproved `NoCommentsCLI` and binary modules (`NoComments.ConfigIO`, `NoComments.Ratchet`, `NoComments.Runner`, `NoComments.LakeEnv`, `NoComments.Worker`, `NoComments.TestListing`, and `NoComments.Main`): filesystem reads/writes, subprocess execution, CLI flag parsing, multi-worker IPC, and `lakefile.toml` / workspace discovery.
- Lean `v4.36.0` runtime, dynamic library loader (`Lean.loadDynlib`), opaque `Lean.Json.parse` / `Json.Parser.anyCore`, `Lean.Parser.parseHeader`, `Lean.importModules`, `Elab.checkDeprecatedImports`, `Elab.checkModuleNamePortability`, `Elab.Frontend.processCommand`, and `Parser.parseCommand` / `Parser.tokenFn` / `Parser.interpolatedStrFn` / `Parser.symbolFn`.
- `Lake` workspace/environment evaluation (`lake env`, `Lake.loadWorkspace`, `Lake.setupServerModule`, `lake setup-file --no-build`) and toolchain version checks (`lean --version` version + commit hash).
- Git invocation (`git ls-files --full-name -z -- '*.lean'`, `git merge-base`, `git ls-tree`, `git show`) and operating-system filesystem behavior.

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
- **Native worker isolation:** For each active workspace (prepared in parallel when multiple workspaces are configured), `no-comments` captures workspace paths and resolves target `leanOptions` / `dynlibs` / `plugins` / direct imports in a single `lake <lakeArgs> env` pass via `Lake.loadWorkspace` (`mod.setup.fetch`, `mod.header.fetch`, `Lake.setupServerModule`, and `Lake.realConfigFile` for `lakefile.lean`, falling back to `lake setup-file --no-build` and `prepareToolImports` for `toolPrefixes` scripts). Files sharing an identical worker runtime environment and import header are grouped into exact-header batches and scheduled across persistent child workers (`--jobs N`) that load required `dynlibs` / `plugins` once via `Lean.loadDynlib` / `Lean.importModules`, reuse the imported base `Environment` before `setMainModule` / `setModulePackage` across exact-header matches while isolating distinct import headers in fresh worker address spaces, and elaborate overriding **only** `Elab.async := false`, `debug.byAsSorry := true`, `warningAsError := false`, and `linter.all := false`.

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
- `--jobs <n>` / `-j <n>`: Number of concurrent worker processes (defaults to `min(cpus, 8)`).
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
env -u REGULA_FULL lake lint
lake build no-comments
(cd specification && lake build --wfail && env -u REGULA_FULL lake lint && lake build spec-check --wfail && lake exe spec-check)
./.lake/build/bin/no-comments check
```

## Skill Integration

Copy or link [`skills/delete-comment/`](skills/delete-comment/) (`SKILL.md` and `agents/openai.yaml`) into your project or global skills directory so `/delete-comment` automatically discovers `.no-comments.json`, applies the four-category comment audit, migrates true decision records into project documentation, and drains the ratchet cleanly.

## Acknowledgments

Special thanks to [Matt Pocock](https://github.com/mattpocock), whose [November 20, 2026 post](https://x.com/mattpocockuk/status/2123798388227403983) inspired this tool and workflow. His framing—classifying every comment as a tautology, excuse, stale note, or real decision record, then pairing automated comment-ban enforcement with a repeatable refactoring pass—shaped both `no-comments`'s ratcheted zero-growth design and the companion [`/delete-comment`](skills/delete-comment/SKILL.md) skill.

## License

MIT — see [LICENSE](LICENSE).
