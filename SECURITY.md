# Security policy

Report a vulnerability privately through GitHub's [private vulnerability reporting](https://github.com/rbeauchamp/lean-no-comments/security/advisories/new), not in a public issue. Include the commit, your Lean toolchain, what fails, and the smallest reproduction.

A vulnerability is a tracked Lean file, comment, or ratchet change that `NoComments.Core`, `NoComments.Config`, or `NoComments.RatchetCore` must refuse and that passes (for example, an uncounted comment, a coverage gap, or a ratchet/monotonicity bypass), or a run of `no-comments` that harms the machine that runs it. What the [README](README.md#unproved-harness-tcb-nocommentscli-and-external-boundaries) lists as the unproved runtime TCB, such as a workspace's own `lakefile` or metaprograms executing during Lake load and header elaboration, is outside this policy until that TCB shrinks.

`lean-no-comments` has one maintainer, so it promises no response time. Fixes land on `main` and reach downstream projects in a later release.
