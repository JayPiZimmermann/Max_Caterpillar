# What fiber analysis now proves for the Max5 width search

Status: 31 October 2026. Two hidden ReLU layers, exact Max5 on all real
inputs, no skips, arbitrary original biases. This is a consolidation of
new restricted lower bounds, not a claim that the unrestricted optimum
has been matched.

## A completed first-layer branch

Every exact first-width-nine Max5 network with first-row coordinate-sum
split (2,2,5) needs second hidden width at least five. Every such completion
has at least three positive and two negative output coefficients.

The five invariant supports have exactly three possibilities up to input
permutation. Their proof coverage is now complete:

| Support family | Classification and lower-bound route |
| --- | --- |
| F1, the five-cycle | All admissible orientations and arbitrary carriers in the forced plane are covered by `max5_nine_c5_child_lower.md` and `max5_facets_child_c5_width6.md`. |
| F2, one three-coordinate row | All 58 surviving labeled profiles require two negative outputs; `max5_oct30_nonroot9_f2.md` closes the eight earlier exceptions. |
| F3, two three-coordinate rows | The complete 480-profile necessary carrier classification has 262 impossible profiles, 216 coordinate-plane profiles, and two exceptional pencils. All 218 admissible profile families are now excluded at second width four. |

The physical bridge uses the first-width-nine minimum to force each
same-sign carrier pair to span a two-dimensional plane. The positive
and negative planes satisfy the separate catalogue constraints. They
need not coincide in the two exceptional F3 pencils; the new proof
explicitly permits this.

These profile counts are finite covers of parameter regimes. They are
not counts of completed networks, algorithms, or zero-loss components.

## Exact F3 closure

The coordinate-plane cover in `max5_oct30_nonroot9_f3_check.py/.json`
checks all 216 profiles by symbolic restriction over whole real parameter
strata. Its current result is PASS, with zero uncovered profiles:

* Eighteen reduce to a star-plus-edge residual problem.
* Eighty reduce to the complete ignored-rival residual problem.
* The remaining 118 reduce to the new star-plus-two mixed-direction
  problem proved in `max5_oct31_f3_star_two.md` and independently audited
  in `max5_oct31_f3_star_two_audit.md`.

The two exceptional pencils are excluded in `max5_oct30_fiber_reduction.md`,
with independent audit `max5_oct30_f3_pencil_tail_audit.md`. That argument
uses only the negative carrier plane and covers its entire real parameter,
so unequal positive and negative choices do not leave a gap.

Every route excludes an all-positive residual identity with any finite
number of folds. If a physical network had only one negative output,
that gate would have to pass on the negative diagonal tail. All free
tail outputs would then be positive, contradicting the residual theorem.
The independent five-invariant-feature positive-output theorem supplies
three positive outputs, giving the claimed five-neuron lower bound.

## The actual fiber mechanism

The useful operation is stratification of the first-layer projection,
followed by uniform obstruction of every completion over each stratum.
For the exceptional pencils, the required crease equation contains
the product F*s. Its vanishing divides the analysis into s=0 and s!=0;
both cases are excluded directly. No downstream weights are assumed
bounded, and no canonicalization homotopy is used.

For the remaining 118 profiles, a gate needed on a true maximum facet
would have a zero crossing at c=T(b). Avoiding a spurious crease forces
T to take only the values zero or one on a connected interval. Continuity
forces it to stay one, even across changes in first-feature activation.
This pins the gate coefficients globally on a half-line and ultimately
forces a crease in the region where the target is identically zero.
This is an example of fiber-compatible rigidity yielding a lower bound.

## What remains before an unrestricted lower bound improves

At first width nine, the other possible split is (1,1,7). Its opposite
carrier pair leaves a two-core residual problem if second width is four.
For coordinate-difference invariant rows the existing root8 extension
theorem gives the stronger lower bound six: pad seven root features to
eight and apply `max5_first10_root8_cover_audit.md`. Arbitrary nonroot
seven-feature dictionaries remain outside that theorem.

Therefore an unrestricted (9,4) realization, if one exists, must lie in
the (1,1,7) split and must have a nonroot invariant first direction.
The completed (2,2,5) result alone does not raise the current unrestricted
second-width lower bound from four to five. It does remove an entire
continuous first-layer branch, rather than only finitely many samples.

Nor does this result automatically transfer to first widths ten, eleven,
or twelve. There, extra carrier directions and extra invariant features
can change both the tail span and the necessary profile classification.

Fiber dimensions or empirical connectivity alone do not prove emptiness.
The repository's exact interpolation examples have nonempty fibers for
every finite input test while their all-input fiber is empty; unbounded
weights escape every compact parameter set. The compactness converse
and scaling-invariant escape witness are in `max5_oct30_related.md`.
An argument based on limiting a feature dictionary must consequently
prove properness of its realization projection or classify the escaping
boundary, rather than assume a finite exact limit.

All cited new exclusions are exact written proofs with independent audits
and exact finite symbolic cover checks. They are not new Lean formalizations.
