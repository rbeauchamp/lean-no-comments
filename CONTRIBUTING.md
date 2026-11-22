# Contributing to `lean-no-comments`

Contributions are welcome, including from AI agents directed by contributors. Read [README.md](README.md) for architecture and TCB boundaries, [AGENTS.md](AGENTS.md) for repository build rules, and follow [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) in all interactions.

## Vulnerability Disclosure

Report potential soundness defects, uncounted comments, coverage gaps, or ratchet/monotonicity bypasses privately through [SECURITY.md](SECURITY.md) (`https://github.com/rbeauchamp/lean-no-comments/security/advisories/new`). Never disclose undisclosed security or checker-bypass vulnerabilities in public issues, pull requests, or docs.

## Architecture & Purity Rules

- **`NoCommentsCore` vs. `NoCommentsCLI`:** Keep pure verified decision modules (`NoComments.Core`, `NoComments.Config`, `NoComments.RatchetCore`) strictly separate from `NoCommentsCLI` (`NoComments.ConfigIO`, `NoComments.Ratchet`, `NoComments.Runner`, `NoComments.LakeEnv`, `NoComments.Worker`, `NoComments.TestListing`) and `NoComments.Main`. Every module in `NoCommentsCore` must start with `module`, carry zero `IO` or `Lake` imports, stay within `[propext, Classical.choice, Quot.sound]`, and contain zero `sorry`, custom `axiom` declarations, `unsafe`, `partial`, `while`/`repeat`, `partial_fixpoint`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `!`-panics (`[i]!`, `get!`, `panic!`).
- **Zero Lean comments:** `comment-ratchet.json` enforces `[]` across every tracked `.lean` file. Do not introduce `--`, `/- ... -/`, `/-- ... -/`, or `/-! ... -/` comments anywhere in `.lean` code.
- **Tests forbidden as evidence (`tests_as_evidence: forbid`):** Do not add test files, Lake test drivers, unit/scenario suites, `#guard`/`#eval`/`#check`/`#print` commands, or `example` declarations. Claims rest on kernel-checked Lean proofs in `NoCommentsCore` and the compiled verification commands below.

## Local Verification

Run these commands cleanly before opening a pull request:

```sh
lake build --wfail
lake lint
lake build no-comments
./.lake/build/bin/no-comments inventory
./.lake/build/bin/no-comments check
libdir="$(lean --print-libdir)"
lib="$libdir/libLake_shared.dylib"; [ -e "$lib" ] || lib="$libdir/libLake_shared.so"
lake env lean --load-dynlib="$lib" --run NoComments/TestListing.lean --check
```

## Pull Requests & Commits

- Use the sections of [`.github/pull_request_template.md`](.github/pull_request_template.md) (`# Mission accounting`, `# Decisions`, `# Accepted risk`, `# Root cause`). Keep every paragraph and list item on a single line without hard wrapping.
- Pull requests are squash-merged onto `main`. Title PRs and commits using [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) (`feat:`, `fix:`, `docs:`, `refactor:`, `chore:`, etc.; release versioning follows [SemVer](https://semver.org/)), sign commits with GPG, include zero AI co-author lines, and keep public text free of private repository, tool, or local filesystem path names.
