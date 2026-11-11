# Max5: every pure-C5 first-width-nine dictionary needs at least six second neurons

**Completed result.** For an exact two-hidden-layer Max5 network on all
real inputs, suppose the first hidden layer has nine neurons and its
five invariant rows are coordinate differences supported on a five-cycle.
Then the second hidden layer has width at least **six**. All four
noninvariant rows may be arbitrary real mixtures in their necessary
carrier plane. Biases, zero suffix coefficients, and all nongeneric
parameter cases are included.

This strengthens the previous bound five for two of the three C5
orientation classes. It does not prove that six is attainable: the
certified C5 construction currently has second width eleven.

## Proof

1. The previously audited first-layer theorem forces row-sum split
   `(2 positive,2 negative,5 zero)` and a unique nonadjacent pair of
   carrier coordinates. Relabel that pair as x0,x2. All four
   noninvariant rows lie in span{x0,x2}. Up to input permutations,
   the admissible C5 orientations have exactly three representatives.

2. The earlier C5 sign argument forces at least three positive output
   coefficients and two negative coefficients. Thus a width-five
   completion would have signs `(3 positive,2 negative)` with no zero
   output weights. The first orientation already requires four positive
   coefficients and is excluded immediately.

3. At positive diagonal infinity, at least one positive-output second
   neuron is passing, supplying translation slope one. Every zero-slope
   neuron has preactivation in the six-dimensional span of the five C5
   comparison functions and x2-x0. Passing neurons contribute an
   unrestricted feature-linear remainder plus an anchor in span{x0,x2}.

4. The complete-comparison three-core obstruction implies that at least
   four zero-slope neurons are needed. With only five physical neurons,
   there is exactly one passing neuron, which has positive output sign.
   Consequently the positive-tail identity would represent Max5-x0 as
   a feature-linear function plus exactly four folded functions, with
   signs `(positive,positive,negative,negative)`, in that six-dimensional
   function space. A different carrier anchor is absorbed into the
   coefficient of x2-x0.

5. Both remaining C5 orientation cases have independently checked
   refutations of this exact four-core problem. The formulas impose
   arbitrary real coefficients, only valid scaling/orientation/permutation
   gauges, thirty normalized binary evaluations, 180 ternary evaluations,
   and thirty necessary target-facet carrier conditions. They do not
   restrict interior cancellation groups or coefficient sizes. Both CPC
   proofs pass independent Ethos checking against their original formulas.
   Hence these necessary identities are impossible.

Every width-five possibility is excluded, proving the bound six.
Bias removal by homogeneous recession preserves widths and output signs,
so the result applies to the affine architecture as well.

## Evidence and simpler proof

* [Tail-space and orientation audit](c5_tail_audit.md).
* [Independent semantic model audit](c5_fourcore_model_audit.md).
* [Completed proof manifest](../../research/sN/frontier5/max5_exact_c5_p2_manifest.json):
  `BOTH_BALANCED_C5_CASES_INDEPENDENT_ETHOS_PASS`.
* [Elementary nine-cell proof for one orientation](c5_orientation1_wall_proof.md).
  Five target facets force two positive directions; four unwanted walls
  force two negative copies; cancellation then removes the desired creases.
* Exact source, certificate, and receipt hashes appear in the manifest.
  No new Lean-verified theorem is asserted.

The old classification and sign arguments are in
`research/sN/frontier5/cycle_contrast.md`,
`max5_nine_c5_child_lower.md`, and
`max5_facets_child_c5_width6.md`. The complete-comparison obstruction is in
`max5_oct31_complete3_theorem.md` and its checked manifest.

## Consequence for comparison-only first-width-nine networks

Every first-width-nine exact network has row-sum split `(1,1,7)` or
`(2,2,5)`. If all invariant rows are coordinate differences, the first
case has a forced signed carrier pair and already requires at least six
second neurons by the complete-comparison theorem. The second case is
precisely the pure-C5 family just treated. Therefore:

**Every Max5 first-width-nine network with comparison-only invariant
rows needs second width at least six.**

The remaining unrestricted first-width-nine cases contain genuinely
nonroot invariant rows. This theorem does not exclude them at second
width four or five.

## What the new computation does not settle

The full unrestricted minimum at first width nine remains open. The
known global construction is `(9,11)`. No second-width-six construction
at first width nine is supplied here, and no claim of a matching
first-width-nine pair is made.

The stronger residual lower bound of five in every C5 tail space is now
also complete. The two balanced-sign cases and all three cases with
three positive and one negative fold have independently checked CPC
proofs; the combined manifest reports `ALL_FIVE_CPC_ETHOS_PASS`.
At most one positive fold is excluded by the geometric positive-carrier
bounds, and an all-positive residual is excluded by the existing C5
wrong-wall argument. Consequently no four-fold residual exists with
any output signs. This is a lower bound, not a construction with five
residual folds. See [the complete residual proof package](c5_four_core_child.md)
and [the five-case manifest](../../research/sN/frontier5/max5_exact_c5_fourcore_manifest.json).

Five-core searches have produced finite-grid fits which fail global
verification. For example, one orientation-two five-core fit is exact on
the ternary grid but gives residual value 2 instead of 3 at
`(x0,x1,x2,x3,x4)=(0,0,0,3,1)`. The complete five-core model timed out
at ninety seconds. Neither outcome changes any existence bound.

## Limits of two supplementary proof routes

A sharper wrong-wall cover was computed for the orientation with forced
positive rays A0 and B0. It yields the elementary nine-cell proof linked
above. The broader conjecture that two positive residual gates are
impossible with arbitrarily many negative gates is not established.

One necessary relaxation asked whether
`a*ReLU(A0·h)+b*ReLU(B0·h)-(Max5-x0)` admits a convex homogeneous
extension from 116 ternary-grid feature points. A floating-point linear
program found such an extension with a=b=1. This does not construct a
sum of negative ReLUs, and the numerical feasibility is only diagnostic.
It shows that the tested finite Jensen-inequality relaxation did not
provide the sought stronger obstruction. The producer is
`max5_exact_c5_convex_extension.py`.
