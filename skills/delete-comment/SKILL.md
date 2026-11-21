---
name: delete-comment
description: Systematically eliminate Lean comments in a repository enforced by no-comments by refactoring excuses, relocating real decision records to design docs, and shrinking the checked-in comment ratchet.
---

# Delete Comment

Reduce Lean comments cleanly while preserving invariants, code clarity, and architectural memory.

## Auto-Discovery

Before auditing comments or editing files, discover the target repository's configuration and conventions in this order:

1. Read repository guidance at the root (`AGENTS.md`, `CONTRIBUTING.md`, `README.md`) to locate documentation directories (such as `docs/adr/`, `docs/`, design specs), cross-reference checks, and required build/verification commands.
2. Locate `.no-comments.json` at the repository root and inspect its configured `workspaces`, `exclude` rules, and `ratchet` path. If `.no-comments.json` is not present yet, check whether the repository uses a legacy ratchet script and ratchet JSON file before falling back or bootstrapping `.no-comments.json`.
3. Locate the `no-comments` binary (`no-comments` on `PATH`, a repo-pinned script, or a locally built binary verified against release SHA-256 checksums or built from `rbeauchamp/lean-no-comments`).

## Policy

Classify every comment before touching it using these four categories:

1. **Tautology (Delete):** The comment restates what the declaration signature, proof step, or code already makes clear. Delete it.
2. **Excuse (Refactor, Then Delete):** The comment apologizes for awkward structure, unclear ordering, hidden coupling, or weak naming. Rename, extract a helper, strengthen a type or theorem, or reorder the declarations so the code is self-explanatory, then delete the comment.
3. **Stale or Misleading (Fix or Delete):** The comment describes old behavior, deleted names, or superseded assumptions. Delete it (and update surrounding code or documentation if a real mismatch was uncovered).
4. **Decision Record or Non-Obvious Invariant (Move to Docs, Then Delete):** Comments explaining *why* an algorithm works, trusted-computing-base assumptions, external protocol constraints, subtle concurrency ordering, or non-obvious safety requirements must never simply be discarded. Move the rationale into the repository's documentation (such as an ADR under `docs/adr/`, an architecture section in `docs/` or `README.md`, or a specification theorem) first, verify doc cross-references, and only then delete the Lean comment.

Never leave ad-hoc verification commands (`#check`, `#print`, scratch examples) or comment-only test stubs behind. Keep prose formatting single-line per logical paragraph or list item in Markdown and commit/PR descriptions without hard line wrapping.

## Workflow

1. **Inventory candidate files:**
   - Run `no-comments inventory` to rank files by comment and line count, or `no-comments inventory <file>` to inspect every remaining comment (`fingerprint`, `kind`, `startLine`–`endLine`) in one target file.
2. **Inspect full context before editing:**
   - Read each target declaration, its callers, and related doc/spec files before deleting any comment.
   - Apply the four-category rule strictly: refactor excuses in code and record real invariants in project docs *before* removing the comment.
   - Check doc comments (`/-- ... -/`) and module docstrings (`/-! ... -/`) as carefully as `--` and `/- ... -/` comments. If a public API doc or theorem invariant belongs in project documentation, migrate it there cleanly (unless the file is explicitly covered by a configured `exclude` rule in `.no-comments.json`, such as literate documentation sources).
3. **Update the ratchet and verify:**
   - Regenerate the ratchet file atomically once edits are ready:
     ```bash
     no-comments inventory --json > <ratchet-path>
     ```
   - Build affected workspaces cleanly (`lake build` inside each affected workspace) so compiled `.olean` artifacts and header setups remain current.
   - Run `no-comments check --file <file>` for fast per-file checks while iterating, then run full `no-comments check` (and any repository-specific doc grep or verification gate discovered in step 1).
   - For the initial adoption PR where `<ratchet-path>` does not yet exist at `git merge-base HEAD <base-ref>`, pass `--bootstrap` (`no-comments check --bootstrap`). On all subsequent PRs, run `no-comments check` without `--bootstrap` and enforce strict monotonic reduction against the merge-base ratchet.
4. **Report exact drain-down totals:**
   Summarize counts deleted, refactored/relocated to documentation, and remaining comments/lines from the ratchet diff.

## Acknowledgments

Warm thanks to [Matt Pocock](https://github.com/mattpocock), whose [November 20, 2026 post](https://x.com/mattpocockuk/status/2123798388227403983) on banning comments cleanly in AI-assisted codebases inspired this workflow and the ratcheted comment-ban architecture—specifically his four-category audit taxonomy (tautologies, excuses, stale comments, and true decision records) paired with automated enforcement that halts new comment drift while giving teams a disciplined path to pay down legacy noise over time.
