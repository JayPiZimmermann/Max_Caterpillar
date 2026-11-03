# Six same-label support models: independent scope audit

Date: 3 November 2026. **PASS for the necessary-model bridge in the stated
six-case sector.** This audit does not establish arithmetic unsatisfiability,
global network equality, or a new unrestricted MAX5 lower bound. Solver
refutations need their own source-bound CPC proof and independent Ethos replay.

The runner imports `research/sN/frontier5/max5_exact_three_shared_local.py`
without modifying it. Its SHA256 is
`e9ea5d767546ea8f5fb06a661ff962d7cb4034f5eea0a370353f45364d66072e`, the
exact source covered by `notes/max5_exact/three_shared_model_audit.md`.
The current audit independently inspected the source and its actual emitted
Z3 expression trees. `check.py` records all input and output hashes.

## Exact mathematical sector

The physical network has widths (9,4), with arbitrary real weights and
biases and no skip connections. The previously proved recession and
singleton-carrier reductions give

    MAX5 = ell + R + ReLU(g) + ReLU(h),

where ell is linear with coefficient sum one, and R, g, h belong to the
actual span of seven invariant physical first features. The present sector
has g uniquely zero at q0=-e0, h uniquely zero at q1=-e1, and both zero at
q2,q3,q4. The two unique comparator germs use the same distinguished label
2. After the valid independent core complementations, their matching
differences are max(x3,x4)-max(x1,x2) and max(x3,x4)-max(x0,x2).

The necessary root hyperplanes are precisely 02, 12, 34 in the minimal-root
subsector. Selecting one physical row on each and rescaling it positively
leaves three independent orientation Booleans. The other four physical rows
have exact supports of size three or four. Their coefficients are arbitrary
reals. Equal supports retain proportional, opposite, and distinct normals;
different supports cannot represent the same nonzero hyperplane.

The independent support cover in
`notes/max5_exact/three_shared_one_each_cover_audit.md` reduces this minimal
root-count subsector to exactly six representatives. The new runner selects
exactly those records, with indices 275, 277, 280, 307, 353, 355. Their four
nonroot supports are respectively:

| Index | Nonroot supports |
|---|---|
| 275 | 012, 013, 013, 014 |
| 277 | 012, 013, 0134, 014 |
| 280 | 012, 013, 014, 034 |
| 307 | 0123, 013, 014, 014 |
| 353 | 013, 013, 014, 014 |
| 355 | 013, 013, 014, 024 |

`check.py` recomputes this selection from the complete cover and compares all
six support multisets. It does not rerun the older full support enumeration;
that separate independent coverage certificate remains an explicit dependency.

## Equations and normalization

All three coefficient lists have seven entries; the only additional linear
coefficients are those of ell. No independent linear head is added to g or h.
At each unique contact, the producer matches consolidated ridge coefficients
and midpoint gradients to the exact comparator and its complementary pair
maximum. Consolidation uses the positive L1 length of every proportional
physical normal, so opposite rows retain their linear contribution and do
not manufacture an uncharged direction. Each other core has a strict sign,
represented by a free activity Boolean.

At the shared contacts, both core values are exactly zero. The sampled
directional equations are necessary: an active first feature contributes
its linear derivative, an inactive feature contributes zero, and a singular
feature contributes ReLU of its directional linear form. Both zero outer
preactivations retain their outer ReLUs. The target derivative is the maximum
of the four tied coordinates. Boolean evaluations of these germs and of the
global identity are therefore valid necessary equations; they are never
asserted sufficient for global equality.

For each nonroot row the first nonzero coefficient among (g,h,R) is normalized
to plus or minus one by positive rescaling of the physical row. This retains
remainder-only features and arbitrary zeros in the other lists. A row unused
by all three lists would give a physical realization using fewer than nine
first neurons, contrary to the established first-width lower bound. This is
the precise dependency permitting that exclusion. There is no simultaneous
coordinate gauge on those nonroot rows.

The original integer-division bug is absent. The midpoint multiplier is the
real rational one-half. The executable audit traverses every emitted formula
and finds no integer-division operation and no quantifier.

## Optional clauses are vacuous in this subsector

The runner enables both the wall and rigid-contact clauses inherited from the
general producer. Neither imposes an additional condition here:

* Every nonroot support has size at most four. Thus every strict full-support
  two-versus-three sign antecedent in the wall clause is false.
* At each shared contact there are at least four singular physical rows,
  including nonroots. Hence neither sufficient rigidity criterion holds.
* A canonical extension of either unique comparator to any shared contact
  requires an extra root outside {02,12,34}. Every corresponding comparator
  formula contains a false root-presence conjunct. The pairwise prohibitions
  against two such comparator germs are consequently tautologies.

The executable audit checks the singular counts and nonroot counts at all
eighteen shared-contact/case combinations. Thus any eventual exclusion from
these six formulas does not need the newer nonroot-wall classification or
three-contact rigidity bound beyond the earlier support-cover dependency.

## Publication boundary

All six formulas parse and pass the scope/encoding audit. The receipt is
`SIX_CASE_SCOPE_AND_ENCODING_AUDIT_PASS_NOT_UNSAT`. It does not certify an
UNSAT verdict. Even six independently checked refutations would exclude
only this minimal-root subsector: the same-label sector has 387 surviving
support classes overall, including 381 classes with more physical root
rows. Other contact sectors and other physical architectures also remain
separate obligations.
