# Bounded publication checkpoint — 3 November 2026

This checkpoint selects frozen proof sources, receipt-bound dependencies,
mathematical drafts, and exact finite certificates. It excludes the active
star-structure proof search and other unfinished search branches. The
selection is specified by `selection.json`; `rootcopy_paths.json` lists
only paths absent from the publication baseline plus checkpoint metadata.

## Status of the mathematical claims

* **Ordinary quadratic lower bound:** the already published ordinary-network
  wrapper retains arbitrary biases and removes skips from the statement.
  Its explicit constant and existence theorem are Lean verified at the
  publication baseline. The existence theorem currently reuses the verified
  explicit bound; it is not a new self-contained short proof.
* **Normalization:** the 98-source receipt verifies same-index localization
  of a normalized homogeneous MAX model, its diagonal-preserving anchor
  lift, exact MAX identity, coordinate-sum normalization, and retention of
  full-support first rows. It does not verify the manuscript's separate
  bias-limit argument, support averaging, or the whole quadratic theorem.
* **Fixed pairs and matching:** the written argument and independent audit
  are included with exact finite controls. These are mathematical proofs and
  checks, not a Lean formalization of the new argument.
* **Six-page quadratic draft:** the draft explicitly leaves the structural
  lemma as the missing self-contained proof. The normalization and fixed-pair
  sections have a source-bound mathematical review. The complete draft is
  not claimed to be a self-contained proof of the headline result.
  The selected PDF has six pages; the selected build log reports six pages
  and has no undefined-reference or overfull-box warning.
* **MAX5 upper bounds:** the physical ordinary networks of widths `(10,6)`
  and `(9,11)` have targeted Lean verification receipts binding respectively
  181 and 231 source/evidence files. These formalize known constructions;
  they do not improve the attained widths or establish optimality.
* **MAX5 general lower bound:** the 90-source baseline receipt checks the
  existing arbitrary-bias second-width lower bound `h2 >= 4`. The unrestricted
  second-width gap remains `4 <= h2 <= 6`; at first width nine the certified
  interval remains `4 <= h2 <= 11`.
* **Triple contact:** a targeted Lean receipt proves that at a top tie of at
  least three inputs some second-layer core must vanish, including every
  point of the open segment between the relevant MAX5 contact inputs.
  The theorem permits an affine-plus-shallow remainder and signed outer
  terms. It supplies a necessary condition, not a new global width bound.
* **Same-label support sector:** the frozen six-case package includes exact
  CPC proofs, independent Ethos replay evidence, runtime sources, and the
  prior local-MAX4 certificate used in its reduction. These exclude only
  the selected six finite arithmetic models. Their actual-network reduction
  remains a written mathematical dependency, not a Lean theorem.
* **225 support classes:** the written shared-contact obstruction, independent
  mathematical audit, and two exact support recounts are included. Together
  with the six selected arithmetic cases, their union covers 227 of the
  387 classes in this particular same-label sector. This does not exhaust
  that sector, the other shared-contact sectors, or the unrestricted `(9,4)`
  problem. The separate scalar Lean lemma checks only its stated finite-point
  algebra; it does not formalize the entire segment-to-network reduction.

The source `audit/FRONTIER.md` is retained as an earlier audit snapshot. Its
statements that the physical `(9,11)` matrices lack Lean verification and
that no six-case outcomes were found have since been superseded by the
receipts included here. Use this checkpoint and the frozen `lower/STATUS.md`
for those updates. Its recorded four-shared inventory remains an inventory
of recovered historical receipts, not a fresh complete certificate replay.

## What this checkpoint verifies

`inventory.py` checks every hash in the selected receipt maps and six-case
manifest, unions all their dependencies, checks local Lean import closure,
and scans Lean source after removing nested comments and strings. The scan
rejects `sorry`, `admit`, `sorryAx`, `axiom`, `unsafe`, `native_decide`, and
`Lean.ofReduceBool`. Recorded headline axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

An independent read-only agent repeated the primary Lean receipt-union audit:
275 source/evidence paths, including 213 Lean files, matched all hashes;
197 existing publication paths were identical and 78 were absent. Every
repository-local Lean import belonged to that union, and its lexical scan
passed. The final selected union also contains the scalar leaf, mathematical
documents, paper files, and external-certificate package; its exact counts
and hashes are in `selection.json`.

The comparison baseline is publication commit
`82ef24b251327b2e1bfdf92a39c6f6b9e7c6924f`. Existing publication paths must match
byte-for-byte; the script refuses to overwrite different files. Copy mode
creates absent paths exclusively and checks their hashes again after copying.
No staging, commit, or push is performed by this checkpoint script.

This is a fresh source-integrity and scope audit of previously recorded Lean
and certificate runs. It is not a new integrated full-project Lean rebuild,
nor a fresh replay of all external proof certificates. External Mathlib and
Lake dependencies are bound by the selected toolchain and lake manifest.

Run from the repository root:

```sh
python3 research/sN/clean_quadratic_20261103/checkpoint/inventory.py
```

Once `selection.json` exists, the default command also compares every selected
artifact, including documents without separate proof receipts, against that
frozen inventory.

To regenerate the selection before its first publication copy, add `--write`.
To copy missing paths into the designated publication worktree after all
checks pass, add `--write --copy-new`. Neither option authorizes overwriting
an existing publication file. The selection and copy-list JSON files omit
their own hashes to avoid circular metadata; all other selected files,
including this audit and the checker, are hashed in `selection.json`.
