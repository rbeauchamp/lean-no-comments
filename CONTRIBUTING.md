# Contributing to `lean-no-comments`

Contributions are welcome, including from AI agents directed by contributors. Read [README.md](README.md) for architecture and TCB boundaries, [AGENTS.md](AGENTS.md) for standalone repository rules, and follow [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) in all interactions. Contributions are submitted under the [MIT License](LICENSE).

## Vulnerability Disclosure

Report potential soundness defects, uncounted comments, coverage gaps, or ratchet/monotonicity bypasses privately through [SECURITY.md](SECURITY.md) (`https://github.com/rbeauchamp/lean-no-comments/security/advisories/new`). Never disclose undisclosed security or checker-bypass vulnerabilities in public issues, pull requests, or docs.

## Deductive and Formal Engineering Standards

`lean-no-comments` is a proof-backed checker: replace trial-and-error implementation and scenario-based testing with derivation, correct-by-construction types, and machine-checked universal proofs.

- **5-rung enforcement ladder and cost bound:** Prefer, in order: (1) types making illegal states unrepresentable (such as `SortedFingerprints` carrying its sortedness proof); (2) relations true by construction or derivation; (3) exhaustive compiler checks over genuinely closed finite domains; (4) machine-checked universal proofs (`∀`, zero `sorry`, standard logical axioms only); and (5) guards derived from the invariant at every state and admission/write boundary (not only where values are observed) where stronger enforcement is unavailable. Spend code enforcement only where breaking a rule causes serious or hard-to-undo harm (such as uncounted comments, dropped tracked-file coverage, or ratchet monotonicity bypasses); leave cheap, easy-to-undo rules written as accepted risk in the trusted base. Every pure decision guard added to `NoCommentsCore` gets a theorem characterizing its decision in `NoComments/Core.lean` or `specification/NoCommentsSpecification/`, or remains documented as accepted risk. Any discovery guard (such as tracked-file, workspace, or build-module discovery) must read through the owning system's own mechanism (Git, Lake, or Lean's environment) or accept only a closed, provably injective subset and reject everything else, treating empty discovery as failure unless emptiness is established.
- **Design and attack first:** Record which enforcement rung each invariant reaches and why no higher rung is available; confirm Lean, Lake, parser, and Git capabilities directly from source or documentation rather than assuming. Define every guarded boundary by its closed class (every constructor, token/comment form, refusal cause, and failure mode), never by a remembered list. Attack every design before coding with adversarial inputs, paths, configs, and syntax trees until no counterexample remains.
- **Guard-removal caller-route derivation:** Before removing or narrowing any guard or refusal, derive everything it refused across every route through the owning system (all callers, configuration fields, CLI subcommands and flags, and worker execution modes), not only the motivating examples. State in the pull request description what now happens on each route: refused by another contract, moved outside the published contract with its consequence documented, or fixed in the same change. A precondition is insufficient if breaching it requires no attacker and yields a wrong result under exit `0` — a wrong result under a success exit code is never cheap or exempt under the cost bound.
- **Proof-to-execution linkage and proof economy:** Connect proofs directly to shipped executable definitions (`NoCommentsCore` bound through `LeanIntent.Implementation` and compiled IR reachability from `no-comments` through `LeanIntent.Execution`) rather than independent shadow models, and distinguish kernel-checked theorems from unproved `NoCommentsCLI` and external TCB assumptions (`README.md`, `specification/README.md`). Apply proof economy: prefer structural and analytic arguments over brute-force enumeration or certified re-execution, weighing both initial and recurring verification costs, and choose the simplest sound proof without unnecessary proof volume. Report evidence honestly (machine-checked, argued from source, observed, assumed, or open), read every affected module and relevant source in full, and report any unreadable source immediately rather than guessing.
- **3-part defect closure:** Close every defect by fixing the instance, closing the entire defect class at the highest practical rung within the cost bound (never merely preserving a single sample as a test), and fixing the upstream check, specification, or instruction link that let it pass undetected, recording `# Mission accounting` and `# Root cause` under [`.github/pull_request_template.md`](.github/pull_request_template.md).

## Architecture & Purity Rules

- **`NoCommentsCore` vs. `NoCommentsCLI`:** Keep pure, linted core modules (`NoComments.Core`, which carries the kernel-checked theorems, plus `NoComments.Config` and `NoComments.RatchetCore`) strictly separate from `NoCommentsCLI` (`NoComments.ConfigIO`, `NoComments.Ratchet`, `NoComments.Runner`, `NoComments.LakeEnv`, `NoComments.Worker`, `NoComments.TestListing`) and `NoComments.Main`. Every module in `NoCommentsCore` must start with `module`, carry zero `IO` or `Lake` imports, stay within `[propext, Classical.choice, Quot.sound]`, and contain zero `sorry`, custom `axiom` declarations, `unsafe`, `partial`, `while`/`repeat`, `partial_fixpoint`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `!`-panics (`[i]!`, `get!`, `panic!`).
- **Zero Lean comments:** `comment-ratchet.json` enforces `[]` across every tracked `.lean` file in both the root and `specification/` workspaces. Do not introduce `--`, `/- ... -/`, `/-- ... -/`, or `/-! ... -/` comments anywhere in `.lean` code.
- **Tests forbidden as evidence (`tests_as_evidence: forbid`):** Do not add test files, Lake test drivers, unit/scenario suites, `#guard`/`#eval`/`#check`/`#print` commands, `native_decide`, or `example` declarations. Claims rest on kernel-checked Lean proofs in `NoComments.Core` and `specification/` (`NoCommentsSpecification`) together with clean execution of the verification commands below.

## Local Verification

Run these commands cleanly before opening or updating a pull request:

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

## Pull Requests & Commits

- Coding agents working on `lean-no-comments` must read [AGENTS.md](AGENTS.md) and this file in full before modifying code, proofs, or documentation.
- Use the four top-level headings of [`.github/pull_request_template.md`](.github/pull_request_template.md) (`# Mission accounting`, `# Decisions`, `# Accepted risk`, `# Root cause`). Keep every paragraph and list item on a single line without hard wrapping.
- Pull requests are squash-merged onto `main`; `main` refuses direct pushes, force-pushes, and commits without a verified GPG signature, and requires [`.github/workflows/ci.yml`](.github/workflows/ci.yml) checks alongside CodeQL to pass on the exact head commit.
- Title PRs and commits using [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) (`feat:`, `fix:`, `docs:`, `refactor:`, `chore:`, etc.; release versioning follows [SemVer](https://semver.org/)), sign commits with GPG, include zero AI co-author lines, and keep public text free of private repository, internal tool, or local filesystem path names.
- Pull requests touching paths listed in [`.github/CODEOWNERS`](.github/CODEOWNERS) automatically request review from `@rbeauchamp`.
