# Agent Instructions (`lean-no-comments`)

This repository (`rbeauchamp/lean-no-comments`) is **public** and self-contained for all engineering rules governing it; it does not depend on external user-level instructions. Read [CONTRIBUTING.md](CONTRIBUTING.md) and [README.md](README.md) in full before modifying code, proofs, or documentation.

## Standalone Deductive and Formal Engineering Rules

- **Methodology:** Follow [CONTRIBUTING.md#deductive-and-formal-engineering-standards](CONTRIBUTING.md#deductive-and-formal-engineering-standards) — the 5-rung enforcement ladder and cost bound, design-and-attack-first, guard-removal caller-route derivation (a wrong result under exit `0` is never cheap or exempt), proof-to-execution linkage and proof economy, and 3-part defect closure.
- **Evidence honesty and unread sources:** Distinguish machine-checked, argued from source, observed, assumed, and open claims; read every affected module and relevant source in full, and report any unreadable source immediately rather than guessing or summarizing.
- **Review cost bound and convergence:** Fix every finding whose failure is serious, hard to undo, or observed; record cheap/unobserved static remainders as accepted risk with reason. Cap validation review loops at 3 rounds and triage remaining findings under the cost bound rather than looping indefinitely.

## Architecture & TCB Split

- **`NoCommentsCore`** (claimed default target in `lakefile.toml`):
  - `NoComments.Core`: Pure `module` lexer/comment extractor, FNV-1a fingerprinting, multiset ratchet comparison (`SortedFingerprints`, `missingFrom`, byte-interval coverage, and `distinctCommentLines`), zero `IO`, zero `Lake`, standard Lean logical axioms only (`propext`, `Classical.choice`, `Quot.sound`).
  - `NoComments.Config`: Pure `module` JSON configuration parser and exhaustive tracked-file classification (`Except String`), zero `IO`, zero `!`-panics.
  - `NoComments.RatchetCore`: Pure `module` ratchet manifest parsing, exact-sync validation, and monotonicity verification (`RatchetCore.validateCheck`), zero `IO`, zero `Lake`.
- **`NoCommentsCLI`** (unclaimed thin runtime harness) and **`no-comments` executable**:
  - `NoComments.ConfigIO`, `NoComments.Ratchet`, `NoComments.Runner`, `NoComments.LakeEnv`, `NoComments.Worker`, `NoComments.TestListing`, and `NoComments.Main` isolate all `IO`, filesystem, `git`, `Lake`, and worker-process effects outside `NoCommentsCore`.
  - `lakefile.toml` intentionally sets `defaultTargets = ["NoCommentsCore"]` so strict logical linting (`lake lint`) audits every pure decision module without claiming `NoCommentsCLI` or the CLI binary.
- **`specification/` (`NoCommentsSpecification` and `spec-check`):** Isolated Lake sub-package proving adequacy, blind second-model comparison, owner confirmation, end-to-end refinement, required-theorem coverage, and compiled IR reachability from `no-comments` without adding specification dependency weight to the shipped binary.

## Required Build & Verification Commands

Run these checks locally before committing or opening a PR:

```sh
lake build --wfail
env -u REGULA_FULL lake lint
lake build no-comments
(cd specification && lake build --wfail && env -u REGULA_FULL lake lint && lake build spec-check --wfail && lake exe spec-check)
./.lake/build/bin/no-comments inventory
./.lake/build/bin/no-comments check
libdir="$(lean --print-libdir)"
lib="$libdir/libLake_shared.dylib"; [ -e "$lib" ] || lib="$libdir/libLake_shared.so"
lake env lean -DwarningAsError=true --load-dynlib="$lib" --run NoComments/TestListing.lean --check
```

## Repository Policy

- **Zero Lean comments:** `comment-ratchet.json` is `[]` (ratchet floor is `0` comments and `0` comment lines across all tracked `.lean` files in both root and `specification/`). Never introduce `--`, `/- ... -/`, `/-- ... -/`, or `/-! ... -/` comments anywhere in `.lean` files. Verify with `./.lake/build/bin/no-comments inventory` (`0 comment(s), 0 line(s)`) and `./.lake/build/bin/no-comments check`.
- **Strict purity in `NoCommentsCore`:** Every module in `NoCommentsCore` must start with `module`, use zero `sorry`, custom axioms, `unsafe`, `partial`, `while`/`repeat`, `partial_fixpoint`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `!`-panicking operations (`[i]!`, `get!`, `panic!`), and build cleanly with `warningAsError = true`.
- **Tests forbidden as evidence (`tests_as_evidence: forbid`):** Add zero test files, test targets, unit/scenario suites, `native_decide`, `example` declarations, or scratch `#guard`/`#eval`/`#check`/`#print` test harnesses. Verification rests strictly on kernel-checked Lean proofs in `NoComments.Core` and `specification/` (`NoCommentsSpecification`) together with clean execution of the built checks above (including `NoComments/TestListing.lean --check` exiting `0` with empty stdout).
- **Merge gate, commits, and public hygiene:** Every change lands through a GPG-signed squash-merged pull request onto `main` after passing local validation (`.no-mistakes.yaml`) and GitHub CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)). Title commits and PRs using [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/), fill all four top-level headings of [`.github/pull_request_template.md`](.github/pull_request_template.md), keep Markdown and GitHub issue/PR paragraphs and list items single-line without hard wraps, include zero AI co-author lines (squash-merging with the exact PR title and body so GitHub does not synthesize co-author trailers), and never mention private repositories, internal tools, internal coordination details, or local filesystem paths in public text.

## In a Cloud Session (Without Local Validation Gate)

When working in a cloud environment that cannot run the local validation pipeline:

1. **Independent adversarial review:** Have an agent that did not author the change review the diff and PR description (attacking every claim in the description) before marking the PR ready or merging, and re-review after any subsequent edit.
2. **Clean local checks and CI:** Run all commands under [Required Build & Verification Commands](#required-build--verification-commands) from a clean checkout without `.lake`, and confirm all GitHub Actions checks pass on the exact head commit standing on current `main`.
3. **Accepted risk accounting:** Record under `# Accepted risk` in the PR description that the local validation gate did not run, naming the exact commit checked, verbatim command results, the CI workflow run, who reviewed, and anything left unchecked.
4. **Merge authority:** Wait for explicit owner direction before merging from a cloud session, and do not force-push a PR branch except when authorized (followed by re-running every check on the new head).
