# Raw affine-skip conditional square-root exponential theorem

Public leaf: `GrowingMatching/Bernoulli/AffineLowerBound.lean`.

The concrete theorem is
`GrowingMatching.Bernoulli.Affine.conditional_affine_sqrt_lower_bound_explicit`.
Its source model is the original nine unrestricted real arrays of
`AffineSkipNetwork N h1 h2`, with arbitrary first covectors, biases and
affine input/output skips, computing MAX on every real input. The budget
counts **all original first neurons**, including output-only terms:
`h1 <= C*N^2`, for integer `C>=1`.

Write `n=floor(N/2)` and `d=20*C`. Assume

    n >= 10000000000*d^2.

For the exact integer

    q = floor(sqrt(n)/(160000*C)),

the only structural hypothesis is `LocalMatchingObstruction (4*q+1) q`.
Then the original second width satisfies

    h2 >= (1/2)*exp(3*sqrt(n)/(160000*C)).

The growing-order obstruction is not proved here. This is an actual raw
arbitrary-first-layer conditional square-root exponential result, not an
unconditional exponential lower bound. The finite structural hypothesis
contains no probability or width estimate, but remains an open input.

The new `AffineHalf.lean` derives one same-index normalized half model and
its simultaneous actual all-first support budgets. It reuses the frozen
faithful affine normalization and the frozen exact half/budget lemmas.
Neither a normalized model, tied point, support or overlap bound, feeding
restriction, rationality condition, probability estimate, rank estimate,
nor survival estimate is supplied by the caller. Both original finite
hidden-layer index types are preserved.

The normalized Bernoulli theorem is applied to that single actual model.
Its actual matching order `floor((sqrt(n)/(1000*d))/8)` is proved equal to
`floor(sqrt(n)/(8000*d))`. Substituting `d=20*C` gives the displayed exact
denominator160000C in q and in the exponent. All input dimension positivity
instances are derived from the explicit size bound; oddN is permitted.

The independent bound driver spells out all nine arrays, the raw evaluator,
original total-width budget, floor, H arity, constants and final inequality.
The separate half driver spells out all normalization sums and both actual
support statistics, and checks a nonlinear oddMAX3-to-MAX1 example with
unchanged hidden widths(4,3). No growingH witness or concrete large-number
sqrt evaluation is asserted.

Reproduce:

    python3 research/sN/jensen_bound/affine_bernoulli_recheck.py --run
