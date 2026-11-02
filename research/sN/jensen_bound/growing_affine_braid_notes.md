# Conditional growing-matching bound for raw affine-braid networks

New public leaf: `GrowingMatching/AffineBraid.lean`.

Its headline theorem `GrowingMatching.AffineBraid.conditional_affine_braid_integer_q_lower_bound`
takes the primitive nine-array `AffineSkipNetwork N h1 h2`, its exact
all-real MAX equation, and the original braid condition: every original
zero-sum first covector has at most two nonzero coordinates. Original
nonzero-sum covectors may have arbitrary support. Every bias, input skip,
output skip, real weight and both hidden-layer widths are unrestricted.

For `q>=1` and `160000*q^2<=N`, the explicit premise
`LocalMatchingObstruction (4*q+1) q` gives `(23/25)*4^q<=h2`.
The dimension positivity instance is derived from the numeric hypotheses.
No normalized model or analytic/counting estimate is a premise.

The frozen affine-skip normalization yields a concrete model on the exact
original hidden-layer indices. Its first row is the original row precisely
when the original bias and coordinate sum both vanish, and zero otherwise.
The new helper `normalizedModel_support_le_two` therefore proves the
normalized braid support bound, which is then passed to the already checked
finite-q conditional braid theorem.

The local obstruction remains open at growing q. This wrapper proves a
conditional transfer and is not an unconditional exponential lower bound.

The independent checker expands all nine raw arrays, the original braid
predicate, and the literal obstruction arity `4*q+1`. It separately tests a
dense nonzero-sum biased row and a genuinely nonlinear exact braid MAX3
network. These tests do not assert any growing-order obstruction.

Reproduce:

    python3 research/sN/jensen_bound/growing_affine_braid_recheck.py --run
