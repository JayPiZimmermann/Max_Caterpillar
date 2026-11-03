# Max5 lower-bound search, 3 November 2026

The current unrestricted ordinary-network interval is **4 ≤ h₂ ≤ 6**.
Arbitrary real weights and all biases are allowed, with no skip connections.
The lower endpoint is already a Lean theorem. `Baseline.lean` exposes its
exact Max5 specialization; this is a recovered baseline, not a new bound.

The minimum possible first hidden width is nine in the existing mathematical
proof with exact finite certificates. That full first-width theorem is not
claimed here as Lean verified. Known undominated feasible pairs are (9,11)
and (10,6); these are not asserted to be the optimal Pareto frontier.

## Current lower-bound reductions

The latest source index is `notes/max5_exact/README.md`. Older
`research/sN/best5/overnight_fixed_complete_status.md` still calls the complete
comparison-space three-core problem open; that has been superseded by the
completed comparison-space theorem indexed in the newer notes.

* Complete comparison features plus a single signed carrier pair have
  residual cost exactly four and physical second width at least six,
  attained by (10,6). Nonroot invariant rows and multiple carrier directions
  are not covered.
* At first width nine, row-sum split (2,2,5) requires second width at least
  five. The remaining (9,4) candidate has split (1,1,7) and two positive
  residual folds over the **actual seven-feature invariant span**. It
  must share at least three of the five four-way top-tie contacts.
* The three-shared, different-distinguished-label path sector has 269
  independently checked arithmetic refutations. Same-label and
  both-unique-contacts-to-one-core sectors remain separate.
* Four-shared receipt recovery by the audit worker found 421 source-bound
  independently checked case receipts out of 587, with 166 uncovered.
  This is receipt recovery, not a new replay or a full exclusion.
* A physical width-four network with one positive output coefficient
  requires first width at least fifteen. Two and three positive output
  sectors remain outside that result.

## New work owned by this branch

1. **All six minimal-root same-label support classes are now excluded.**
   `same_label/` contains independently Ethos-checked CVC5 refutations with
   unbounded real coefficients. Cases 275, 280, 307, 353 and 355 use the
   existing audited model directly. Case 277 adds only the six necessary
   singleton-triple coefficient clauses: both positive cores have equal
   nonzero curvature magnitude on the sole first wall at top triples 013
   and 014. This is a six-case sector closure; the full same-label cover
   has 387 classes. The additional analytic exclusions below overlap four
   of these six, giving a combined frozen closure of 227 classes.
2. `width4_geometry/three_negative_wall.md` proves a new necessary
   dichotomy for a three-negative-core representation at a nonroot first
   wall used by all three cores: after complementing cores to make the
   wall coefficients positive, they have equal magnitude and the
   remainder coefficient is one or two times that magnitude, **or** a
   core vanishes on an open subset of that wall. The proof retains zero
   plateaus explicitly. It is a mathematical proof, not a new Lean claim.
3. The exact ordinary-network Max5 specialization in `Baseline.lean`
   passed fresh Lean checks, including its literal-array statement and
   standard-three-axiom audit. Its 89 existing source/control dependencies
   match the current publication checkout byte for byte.
4. **A general local zero-core theorem is now Lean verified.**
   `triple_contact/TripleContact.lean` proves that at a three-way top tie,
   any exact max representation by an affine-shallow remainder and finitely
   many signed outer folds has a zero core. Its explicit two-core Max5
   corollary applies at every `-a*e_i-b*e_j`, for `a,b>0`, hence along each
   entire open triple-contact segment. Arbitrary affine shallow functions,
   first biases, independent feature spans, and widths are allowed.
5. **A short analytic midpoint argument excludes 225/387 same-label
   support classes.** At the shared contacts q3,q4 both cores vanish, while
   their mandatory comparison34 curvatures equal +1. If no nonroot first
   row contains both coordinates, exact ReLU additivity gives both core
   values -1 at q3+q4, contradicting the preceding theorem. The stronger
   segment argument forces a sole crossing row to satisfy `a3+a4=0`,
   excluding case280 and reducing case277 to a balanced four-coordinate
   direction. See `width4_geometry/segment_obstruction.md` and the
   independent `segment_audit.md`. The support classification bridge is
   mathematical, not claimed as a full Lean theorem. Two independent
   support-count scripts agree on 225 classes.

Additional triple-contact arithmetic searches are kept in separate working
bundles; their counts are not silently added to this bounded checkpoint.

No improved unrestricted width endpoint is claimed by this note.
