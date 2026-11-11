# Frozen 2 November research checkpoint: publication inventory

This is a read-only inventory, not a new kernel build or a production-root
promotion. No source was copied into the publication worktree, staged,
committed, or pushed by this audit.

The publication worktree `/tmp/max4-proof-publication-20261102` was clean at
`ffdbc2e0c61bfd708f022ad87c403113ea75dd6b`. The remote branch
`proof/quadratic-second-width-20261102` had the same head.

## Ready bounded selection

`selection.json` binds 1,520 unique source, control, receipt, and log files.
The independent project import scan covers 1,401 Lean files and found no
`sorry`, `admit`, `sorryAx`, `native_decide`, `Lean.ofReduceBool`, project
axiom declaration, or unsafe declaration. All recorded source and log hashes
match. Of the selected files:

* 1,379 already exist byte-for-byte in the publication worktree;
* 141 are new (674,754 bytes total);
* zero require replacing an existing publication file.

The exact new-file list is `copy_candidates.txt`. The unrelated edited
`research/sN/frontierN/PROOFS.md` is not selected. Neither PDF files nor Lean
build artifacts are selected. Corresponding successful `.exit` files are
included where a recorded receipt reader consumes them.

The nine selected receipts cover:

| Receipt group | Recorded exact axiom reports | Actual scope |
| --- | ---: | --- |
| Structural circuit and canonicalization | 21 | Generic cycle identity, arbitrary-N braid canonicalization and cancellation-sensitive graph bridge |
| Finite-index network constructor | 11 | Exact array reindexing, normalization and interaction identities |
| Forest matching | 9 | Actual finite forests, covers, matchings and cycle extraction |
| No periodic sum | 5 | Actual MAX cannot be an affine function plus a finite sum of functions with non-diagonal periods |
| Original-neuron rank | 3 | One original second neuron with nonzero output coefficient has observation rank at least N-1 |
| Crease-invariant controls | 4 | Elementary Lean identities and separately labelled finite/analytic counterexample evidence |
| Independent ridge audit | 3 | Expanded headline type, input-witness conclusion and necessary boundary controls |
| General first-row controls | 10 | Actual adaptive-offset Lean counterexample; separately labelled selector probability argument |
| Matching moment | Diagnostic receipt | Weighted finite matching moment, with an expanded copied-source exact-type driver |

The first eight groups contain 66 recorded reports in total; this count
includes repeated theorem reports across checks. MatchingMoment's own log
contains its separate reports. All advertised axioms remain within
`propext`, `Classical.choice`, and `Quot.sound`.

## Reproducibility limits that must remain visible

* The old MatchingMoment diagnostic receipt binds only its direct project
  import and a local `.olean`. This audit independently records its complete
  project source import closure, but does not claim a fresh rebuild. The
  `.olean` is checked locally and excluded from publication.
* The structural receipt programs inspect earlier recorded build logs.
  Rebuild their named leaf modules and exact drivers before creating fresh
  receipts. Their logs and exit inputs are present in the selection.
* The general-row and invariant helper commands expect ordinary project
  imports to have been built. The relevant source closure and toolchain are
  included; `.lake` artifacts are not.
* No selected note proves a new unrestricted exponential width bound or
  H(k,3). The general crease-span and selector probability arguments are
  mathematical arguments with exact controls, not Lean theorems.
* The unfinished actual forest-network assembly and degree-two work are
  excluded. The parent-owned root research README also remains excluded
  until its status is brought up to date.

## Countersearch is separately audited, not publication-ready as advertised

The selected six frozen finite datasets pass 5,061 literal rational column
identities, their finite matching scopes, the MAX6 positive control, and
46,440 signed-cycle point controls. Their producer, data, and certificate
hashes still match. These checks reuse the existing certificate checker;
they do not independently regenerate every continuous chamber column.

However, the aggregate `countersearch/verification_receipt.json` binds an
older `verify.py`. The current script additionally discovers an unfinished
`signed_fast/n13_b1_k21_old0.json` without a certificate. Thus its advertised
aggregate recheck is not reproducible as a passing check. This is a concrete
publication blocker, not a mathematical refutation of the six frozen
datasets.

`countersearch_audit/audit.json` contains an explicit 34-file dependency list
and hashes, plus four optional files for the separately scoped one-role
mathematical argument. Repair the aggregate verifier in a separately scoped
file or publish only the explicitly selected-six audit with this limitation.
The ready 141-file selection does not include the stale aggregate receipt.

## Repeat the inventory

Run from the repository root:

```sh
python3 research/sN/overnight_20261103/checkpoint/inventory.py
python3 research/sN/overnight_20261103/checkpoint/countersearch_audit/audit.py
```

The first command writes only this audit directory and performs no builds or
publication mutations. Re-run it immediately before copying the selected
files, because concurrent research may add later verified checkpoints.
