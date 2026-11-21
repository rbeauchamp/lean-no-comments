# Agent Instructions (`lean-no-comments`)

This repository (`rbeauchamp/lean-no-comments`) is **public**. Follow these rules strictly on every change.

## Architecture & TCB Split

- **`NoCommentsCore`** (claimed default target in `lakefile.toml`):
  - `NoComments.Core`: Pure `module` lexer/comment extractor, FNV-1a fingerprinting, multiset ratchet comparison (`SortedFingerprints`, `missingFrom`, byte-interval coverage, and `distinctCommentLines`), zero `IO`, zero `Lake`, standard Lean logical axioms only (`propext`, `Classical.choice`, `Quot.sound`).
  - `NoComments.Config`: Pure `module` JSON configuration parser and exhaustive tracked-file classification (`Except String`), zero `IO`, zero `!`-panics.
  - `NoComments.RatchetCore`: Pure `module` ratchet manifest parsing, exact-sync validation, and monotonicity verification (`RatchetCore.validateCheck`), zero `IO`, zero `Lake`.
- **`NoCommentsCLI`** (unclaimed thin runtime harness) and **`no-comments` executable**:
  - `NoComments.ConfigIO`, `NoComments.Ratchet`, `NoComments.Runner`, `NoComments.LakeEnv`, `NoComments.Worker`, `NoComments.TestListing`, and `NoComments.Main` isolate all `IO`, filesystem, `git`, `Lake`, and worker-process effects outside `NoCommentsCore`.
  - `lakefile.toml` intentionally sets `defaultTargets = ["NoCommentsCore"]` so strict logical linting (`lake lint`) audits every pure verified decision module without claiming `NoCommentsCLI` or the CLI binary.

## Required Build & Verification Commands

Run these checks locally before committing or opening a PR:

```sh
lake build --wfail
lake build no-comments
./.lake/build/bin/no-comments inventory
./.lake/build/bin/no-comments check
lake env lean --load-dynlib=libLake_shared.dylib --run NoComments/TestListing.lean --check
```

When a Regula `lintDriver` is configured on `lakefile.toml`, also run:

```sh
lake lint
```

## Repository Policy

- **Zero Lean comments:** `comment-ratchet.json` is `[]` (ratchet floor is `0` comments and `0` comment lines across all tracked `.lean` files). Never introduce `--`, `/- ... -/`, `/-- ... -/`, or `/-! ... -/` comments anywhere in `.lean` files. Verify with `./.lake/build/bin/no-comments inventory` (`0/10 files with comments, 0 comment(s), 0 line(s)`) and `./.lake/build/bin/no-comments check`.
- **Strict purity in `NoCommentsCore`:** Every module in `NoCommentsCore` must start with `module`, use zero `sorry`, custom axioms, `unsafe`, `partial`, `while`/`repeat`, `partial_fixpoint`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `!`-panicking operations (`[i]!`, `get!`, `panic!`), and build cleanly with `warningAsError = true`.
- **Tests forbidden as evidence (`tests_as_evidence: forbid`):** Add zero test files, test targets, unit/scenario suites, or scratch `#check`/`#print` test harnesses. Verification rests strictly on kernel-checked Lean proofs in `NoCommentsCore` and clean execution of the built checks above (including `NoComments/TestListing.lean`).
- **Public & commit hygiene:** Include zero AI co-author lines in commits or PR descriptions, use Conventional Commits, keep Markdown and GitHub issue/PR paragraphs and list items single-line (no hard line wraps), and never mention private repositories, internal tools, internal coordination details, or local filesystem paths.
