---
name: delete-comment
description: >-
  Audit and drain Lean 4 code comments under a repository's NO-COMMENTS ratchet
  using auto-discovered config, doc targets, cross-references, and verification
  gate. Use when draining Lean comments in a repository or when invoked as
  /delete-comment or $delete-comment.
user-invocable: true
---

# delete-comment

Drain Lean code comments (`--`, `/- ... -/`, `/-- ... -/`, `/-! ... -/`) out of a repository's in-scope `.lean` files under its downward-only fingerprinted `NO-COMMENTS` ratchet.

Non-Lean `#` comments (`.yaml`, `.yml`, `.toml`, `.json`, shell scripts, GitHub workflows), Markdown documentation, and paths explicitly excluded by the repository's `NO-COMMENTS` configuration (for example, `.no-comments.json` exclusions such as prose documentation sources) are out of scope.

## Acknowledgments

Many thanks to [Matt Pocock](https://github.com/mattpocock) for the excellent concept and originating prompt shared in [his November 20, 2026 post on X](https://x.com/mattpocockuk/status/2123798388227403983): classifying every code comment as Tautology, Excuse, Stale, or Decision Record (deleting tautologies and stale comments, filing issues for excuses, and promoting decision records into ADRs), pairing that audit with a ratcheted comment-ban lint rule, and packaging the workflow as a repeatable `/delete-comment` skill with a line-reduction summary. This skill adapts that workflow for Lean 4 repositories using Lean-frontend comment inspection and repository-discovered documentation and gate contracts.

## Procedure

1. **Discover the repository contract, disclosure boundary, inventory command, and verification gate.** Before touching any file or querying any external tracker, read `AGENTS.md`, `CONTRIBUTING.md`, `SECURITY.md` (when present), `README.md`, CI workflows, and any build/gate scripts to identify provisioning prerequisites, documentation rules, review rules, disclosure boundaries, and verification commands.
   - **Disclosure policy and authorized issue tracker:**
     - Record the repository's visibility and `SECURITY.md` vulnerability-disclosure policy (including soundness, security, or checker/gate-bypass defects that must be reported privately rather than in public issues, docs, commits, or PR text), and apply this boundary before every external search, doc edit, issue creation, and summary.
     - Resolve the working repository's authorized issue tracker (`[HOST/]OWNER/REPO`) once from its git remote (for example, `git remote get-url origin`) and repository docs—never relying on ambient `GH_REPO` or implicit `gh` repository selection; if the authorized tracker is missing or ambiguous across remotes, stop and clarify before running any `gh` command.
   - **Inventory and ratchet configuration:**
     - Derive the comment inventory command, ratchet manifest path, workspace layout, and explicit exclusions from the repository's contract first (`.no-comments.json`, gate scripts, CI workflows, config files, and docs), handling both `.no-comments.json` multi-workspace layouts (declaring `"ratchet"`, `"workspaces"` with `dir`/`srcDir`/`lakeArgs`/`toolPrefixes`/`excludePrefixes`, and `"exclude"` rules paired with `no-comments inventory`, `lake exe no-comments inventory`, or a repo-pinned wrapper) and custom repo-local checker scripts that declare a ratchet manifest JSON.
     - Stop and report only when the repository's contract defines no `NO-COMMENTS` checker or ratchet configuration at all—never guess, and never refuse a repository solely because its wrapper or manifest lives outside common paths.
     - Never rely on regexes or ad-hoc `grep` to count comments; always read remaining comments, line ranges, and 16-hex FNV-1a fingerprints through the repository's discovered Lean-frontend inventory command, and keep the per-file inventory output for every file you edit.
   - **Durable Decision Record destination and cross-reference roots:**
     - Derive both the durable documentation/ADR destination (`docs/adr/`, `docs/`, `README.md`, specifications, or generated-doc source files—regenerating derived docs from source rather than hand-editing generated outputs) and all cross-reference roots (docs, specifications, generated-doc sources, configs, workflows, scripts, skills, and tracked `.lean` files that cite docstrings) from `AGENTS.md`, `CONTRIBUTING.md`, gate scripts, and layout.
     - If an active compiler or linter setting (such as `linter.missingDocs` or a required module-doc audit) rejects deleting a docstring or module doc in the current tree, do not break the build; stop and report the blocking prerequisite.
   - **Verification gate command and success conditions:**
     - Discover and record once the repository's full verification gate command(s), required exit/empty-output success conditions, and predecessor-comparison base ref (`git merge-base HEAD <base-ref>`) before editing any file.

2. **Choose a reviewable batch.** Pick one file or a small cohesive group of related modules (for example, one subsystem or feature area) to clear completely to `0` comments in one PR; if a large file must be drained incrementally, drain complete logical units cleanly without leaving partial clutter.

3. **Check open issues and dynamic cross-references before deleting.**
   - Apply the Step 1 disclosure boundary before searching external trackers: inspect open issues explicitly targeting the resolved tracker (`gh issue list --repo <[host/]owner/repo> --state open --limit 50`, or `--search` with `--repo <[host/]owner/repo>` when the backlog is larger) so you do not file duplicates for already-tracked defects, without putting undisclosed vulnerability details or sensitive information into public search queries.
   - Dynamically grep all tracked files from the repository root (excluding only the discovered ratchet manifest) so every discovered reference root is covered before deleting any comment:
     ```sh
     git grep -n -i -e "comment" -e "docstring" -- . ':!<ratchet-manifest>'
     git grep -n -e "<File>.lean" -e "<Module.Name>" -- . ':!<ratchet-manifest>'
     ```
     A reliance need not use the word "comment": any document, config, skill, or tracked source file saying a file "describes" or "states" something, or pointing a reader to that file or its docstrings for explanation, relies on its comments; subject to Step 1 disclosure and public/private hygiene rules, migrate the relied-on content into the repository's discovered durable documentation destination and update every citation across all discovered reference roots in the same PR so no statement becomes false.

4. **Read every target file in full and classify every comment.** Read the actual surrounding Lean code completely before taking any action on a comment.
   - **Disclosure gate (applies to every category before any public action):** Check the Step 1 `SECURITY.md` disclosure policy first; if a comment describes or reveals a privately reportable vulnerability or restricted defect (for example, a security flaw, soundness defect, or checker/gate bypass where a case that must be rejected is silently accepted), do **not** file a public GitHub issue, copy it into public docs, delete or expose it in a public drain PR, or mention its existence, location, failed contract, or reproduction in public commits, PR text, or public summaries—route it through the repository's private disclosure channel (or escalate privately to the maintainer) and leave it out of any public drain PR until handled under that policy.
   - **Tautology**: repeats what is already visible from the code, types, names, or theorem statements (including trivial field/constructor docstrings and `/-! ## ... -/` section dividers) -> delete the comment.
   - **Stale**: references nonexistent or renamed symbols, removed modules, outdated Lean/Lake behavior, or claims that contradict the code -> delete the comment and fix any mirrored stale claim in documentation or reference roots.
   - **Excuse**: rationalizes a hacky, fragile, arbitrary, or corner-cutting implementation (magic bounds, silent skips, silently accepted invalid inputs, stringly-typed sentinels, unnecessary workarounds) instead of fixing it properly -> delete the comment AND file a GitHub issue against the authorized tracker resolved in Step 1 (`gh issue create --repo <[host/]owner/repo>` with an appropriate category label such as `bug` or `enhancement`, never `question`), unless an open issue in that tracker already tracks the exact defect (cite `<owner/repo>#<n>` or its issue URL); apply public/private hygiene and write GitHub issues with one line per paragraph and per list item (no hard wraps), citing exact file/lines, failed property, expected contract, and relied-on assumption.
   - **Decision Record**: documents an important, non-obvious architectural, semantic, security, performance, prior-art/equation derivation, or Trusted Computing Base (TCB) decision not visible from reading the code alone -> verify whether the repository's discovered durable documentation/ADR destination already records the full decision, hypotheses, qualifiers, and rationale; migrate any missing non-obvious detail there using single-line paragraphs and single-line list items without hard wraps (updating any ADR index, cross-references, or regenerating derived docs from source), and delete the comment.

5. **Delete comments cleanly with zero semantic Lean edits.** Remove only comment text and redundant consecutive blank lines (including leading blank lines left at the top of a file), while **preserving Lean token separation and significant layout**:
   - Comments act as whitespace separators in Lean's lexer: whenever deleting a block comment (`/- ... -/`, inline or multi-line) would merge adjacent tokens (for example, `f/- apply -/x` becoming `fx`) or glue operators/punctuation, insert whitespace (a space, or a newline when removing a multi-line comment spanning lines) so tokenization and line separation are unchanged.
   - Preserve indentation and column alignment in layout-sensitive syntax (`do`, `match`, `where`, `by` tactic blocks): if a removed comment precedes code on the same line, replace it with spaces or verify column alignment so layout meaning cannot shift.
   - Make **zero semantic Lean edits** in a pure comment-drain PR (fixes for filed Excuse issues land in their own PRs), and inspect the Lean diff directly to confirm token and layout preservation—the build and ratchet gate cannot catch a merged token that happens to type-check.
   - Never edit, reword, re-indent, or move a comment you keep: `NO-COMMENTS` fingerprints exact UTF-8 comment bytes in line-ending-normalized source, so any edited comment or kept comment moved across files registers as a new comment.

6. **Tighten the ratchet manifest strictly downward.** Each entry in the discovered ratchet file has the form `{"file": ..., "comments": N, "lines": M, "fingerprints": [...]}` with `fingerprints` in ascending order, one 16-hex entry per remaining comment (duplicates kept), `comments == fingerprints.length`, and `lines` equal to distinct lines touched by remaining comments.
   - Remove the entire entry for every file whose comment count reached `0`, and for partially drained files re-run the single-file inventory command (`<inventory-cmd> <file>`), remove one occurrence of each deleted fingerprint while preserving ascending order, and set `comments` and `lines` to exact inventory totals (or regenerate via `<inventory-cmd> --json` and verify the diff only deletes entries/fingerprints and decreases counts).
   - Establish that predecessor-manifest monotonicity can actually run before executing the gate: verify that `git merge-base HEAD <base-ref>` succeeds for the checker's selected base ref (`origin/main`, `main`, or `--base-ref`) and that the merge-base commit holds the predecessor ratchet manifest (`git cat-file -e "<base>:<ratchet-manifest>"`), deepening shallow checkouts until reachable rather than treating an uncompared run as verified (`--bootstrap` is valid only on genuine first-time adoption PRs, and must be reported as uncompared).

7. **Enforce hygiene and verify with the repository's own gate.**
   - **Respect the repository's testing and contribution rules:** follow `AGENTS.md` and `CONTRIBUTING.md` (add zero tests, scratch `#check`/`#print` checks, or comment-only test stubs where tests are forbidden as evidence).
   - **Strict disclosure and public/private hygiene:** enforce the Step 1 disclosure boundary across every artifact—never publish privately reportable vulnerabilities in public issues, docs, ADRs, commits, or PR text, and in public repositories leak zero private repository names, private tool names, internal coordination details, or local machine/home-directory paths.
   - **Markdown, GitHub & commit hygiene:** write Markdown documentation and ADRs, commit/PR descriptions, and GitHub issue/PR text with single-line paragraphs and single-line list items (no hard wraps), follow the repo's PR template when present, and omit AI co-author lines when disallowed.
   - **Run the verification gate recorded in Step 1:** execute the exact build, lint, and `NO-COMMENTS` gate command(s), confirming exit `0`, any required empty-output condition, and stdout/stderr confirmation that predecessor-manifest monotonicity actually compared against the Step 6 `merge-base`.

8. **Report a structured drain-down summary.** Report files cleared to `0` comments and any partially drained files, counts deleted by category (`Tautology`, `Stale`, `Excuse`, `Decision Record`), every public GitHub issue filed or cited qualified with `<owner/repo>#<n>` (routing any `SECURITY.md` findings privately only), durable docs/ADRs and cross-references updated, distinct comment lines and total source lines shed, remaining ratchet totals (`files`, `comments`, `lines`), and exact verification gate commands with exit status and `merge-base` commit.
