# Independent audit of the ridge finite-difference theorem

Outcome: the mathematical argument and the read-only actual Lean signatures
agree. No gap was found in the core arbitrary-summand theorem. The independent
expected-type/control driver is kernel green with the usual three axioms.
No ridge producer file, frozen invariant file, or production file was changed.

The audited headline is
`MaxCaterpillar.ExponentialPush.Ridge.maximum_ne_affine_sum_of_exists_periods`
in the sibling `ridge_annihilator/NoRidgeSum.lean`.

For `N>=2`, an arbitrary finite family `f_j : R^N -> R` cannot satisfy

    MAX_N(x) = a(x) + c + sum_j f_j(x)

if each `f_j` has even one translation period `v_j` with two unequal
coordinates. Here `a` may be an arbitrary additive homomorphism, which is
stronger than allowing only real-linear functions. The functions need not be
continuous, measurable, bounded, homogeneous, or invariant in the diagonal
direction. They need not have all real multiples of `v_j` as periods.

## Independent proof review

1. The all-coordinate unit translation difference of the actual `MAX_N` is
   exactly `(-1)^(N-1) * max(0,1-range(x))`. The proof pairs Boolean subsets
   around a minimum coordinate. Its value at zero is nonzero.
2. The support condition used in Lean is literally:

       for all i,j there is R such that
       R < |x_i-x_j| implies f(x)=0.

   It neither assumes nor implies diagonal invariance. That is sufficient:
   a period whose i,j coordinates differ produces the unbounded arithmetic
   progression of i,j contrasts. Only the Archimedean property of the real
   numbers is used. Positive integer multiples of a single period suffice.
3. A fixed translation difference preserves this support condition, with
   bound enlarged by `|v_i-v_j|`. Hence a finite sequence of non-diagonal
   differences is injective at zero on contrast-bounded functions.
4. Translation differences commute and distribute over finite sums. One
   period difference for each summand therefore gives a common annihilator.
   Two additional repeated non-diagonal differences annihilate the additive
   affine remainder; `N>=2` supplies such a direction. There is no forbidden
   inference from annihilating a sum to annihilating its individual terms.
5. The coordinate-difference operator commutes with that annihilator. If the
   representation existed, the nonzero tent would therefore be annihilated
   by a product of non-diagonal differences, contradicting injectivity.

The actual code carries the finite affine/sum algebra and the contrast-bound
injectivity explicitly. It does not rely on a Fourier transform,
distributional derivative, compactness/topology API, or positivity of readout
weights. The stronger additive-homomorphism affine allowance is legitimate:
two differences annihilate every additive homomorphism algebraically.

## Independent controls

`ExactCheck.lean` imports the stable producer and checks the full actual-model
signature by deriving an input `x` where the proposed representation fails.
It also proves two boundary controls:

* If the period is allowed to be diagonal, the conclusion is false:
  `f(x)=MAX_N(x)-x_j` is diagonal-invariant, while `x_j+f(x)=MAX_N(x)`.
* For `N=1`, `MAX_1(x)=x_0`, so the input-arity threshold is necessary.

`tent_control.py` does not import any producer code. It enumerates subset
translations directly with exact rational arithmetic. Across 2728 cases on
arities one through five it checks equal and unequal positive increments,
ties, the nonzero origin value, and the range-one support boundary. Its
negative controls verify that nonpositive increments need not obey the
positive-increment formula and that two repeated diagonal differences
annihilate MAX. This differs from the Lean proof's minimum-coordinate subset
pairing and does not replace the all-real proof.

## Consequence and limits

If all summands factor through linear maps with non-diagonal kernels, the
theorem applies. This justifies the proposed **existence** reduction to at
least one neuron of full rank on the translation quotient, once the actual
network/kernel linear-algebra adapter is proved. It does not let one delete
low-rank terms from a representation containing other, full-rank terms.

For a normalized forest preactivation with m edges and one modular head,
rank is at most m+1, giving the necessary condition m>=N-2 on some forest
term. This dimension argument is mathematical, not part of this driver's
Lean claims. For arbitrary affine-skip networks, first-layer output-skip
terms can be absorbed into the bad ridge sum only for `N>=3`; at `N=2` a
single comparison ReLU already has full quotient rank. The producer note
states that distinction correctly.

Full-rank stars and double-stars remain. In particular the sibling
`forest_anchor_counterexample.py` already supplies full-rank spanning-tree
units with nonzero conormal cube charge, so rank pruning alone does not
restore the disproved unitwise forest-to-anchor reduction. The ridge theorem
is not a growing-matching obstruction or an exponential width bound.
