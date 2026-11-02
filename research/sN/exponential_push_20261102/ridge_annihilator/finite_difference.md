# A finite-difference obstruction to lower-dimensional ridge sums

Status: the complete no-periodic-sum obstruction has passed Lean in
`NoRidgeSum.lean`, including the all-arity maximum-to-tent identity, its nonzero
value at zero, the contrast support bound, commutation, and injectivity of the
finite-difference operator. The audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. This is a research theorem, separate from
the production roots. The reproducible exact-type and source-hash gate is
`python3 research/sN/exponential_push_20261102/ridge_annihilator/recheck.py --run`.
This is a structural obstruction, not a width lower bound by itself. It does
not allow deleting arbitrary low-rank summands from a representation containing
other summands.

Let `N ≥ 2`, let `M(x) = max_i x_i`, and let `Δ_v f(x) = f(x+v)−f(x)`.
For arbitrary functions `f_1,…,f_m : R^N → R`, suppose each `f_j` is invariant
under translation by some vector `v_j` which is not a multiple of the
all-ones vector. Then no affine function `a` satisfies

    M = a + Σ_j f_j.

The exact Lean declaration is
`MaxCaterpillar.ExponentialPush.Ridge.maximum_ne_affine_sum_of_exists_periods`.
Its remainder is allowed to be an arbitrary additive function plus a constant,
which includes every ordinary real affine function. The independent consumer
`NoRidgeSumCheck.lean` checks the ordinary affine formulation and the boundary
cases `N=1` and a diagonal-periodic maximum remainder.

Invariance under a single nonzero quotient period suffices; no continuity,
measurability, boundedness, or linear-direction invariance of the summands is
required.

## Exact finite identity

For positive coordinate increments `a_1,…,a_N`,

    (Δ_(a_1 e_1) ⋯ Δ_(a_N e_N) M)(x)
      = (−1)^(N−1) max(0, min_i(x_i+a_i) − max_i x_i).

Here is a purely algebraic proof. Put `b = max_i x_i` and
`y_i = max(0,x_i+a_i−b)`. Increasing a coordinate cannot decrease the maximum,
so for every subset `S` the shifted maximum is

    b + max({0} ∪ {y_i : i∈S}).

Choose `k` minimizing `y`. In the alternating sum over subsets, pair every
`S` not containing `k` with `S∪{k}`. For nonempty `S`, its maximum is already
at least `y_k`, so the pair cancels. Only the pair `∅,{k}` remains, contributing
`(−1)^(N−1)y_k`. Since positive part is monotone, this is the displayed formula.

Taking every increment equal to one gives the tent

    K(x) = (−1)^(N−1) max(0,1−(max_i x_i−min_i x_i)).

It is nonzero at zero and invariant under the common diagonal. On the quotient
identified with `z_i=x_i−x_N`, its nonzero set lies in the bounded box
`|z_i|<1`.

## Bounded support makes differences injective

On any finite-dimensional real vector space, if a function `g` has bounded
support and `w≠0`, then `Δ_w g=0` implies `g=0`. Otherwise a point where `g`
is nonzero has all its translates `x+n w` in the support, contradicting
boundedness. A finite translation difference preserves bounded support.
Consequently any finite product of differences in nonzero directions is
injective on functions with bounded support.

The Lean proof avoids quotient spaces: `ContrastBounded f` means that for each
pair `i,j`, the function vanishes whenever `|x_i−x_j|` exceeds some finite
bound. Applying `Δ_v` increases that bound by at most `|v_i−v_j|`. A nonzero
contrast of `v` makes the translates `x+n v` escape the corresponding bound.

Now `P=∏_j Δ_(v_j)` annihilates every `f_j`, because the differences commute.
The coordinate difference `D=∏_i Δ_(e_i)` annihilates the affine remainder
when `N≥2`. Thus the proposed representation would give

    P K = P D M = D P M = 0.

On the diagonal quotient every `v_j` is nonzero. The preceding injectivity
contradicts `K(0)=(−1)^(N−1)≠0`.

The formal affine proof equivalently prepends two copies of one non-diagonal
difference to `P`, annihilating the additive affine remainder before commuting
with the coordinate difference. This avoids any regularity assumption on the
affine map and handles an empty family of summands uniformly.

## Rank consequence and its exact scope

If every summand factors through a linear map whose kernel contains a
non-diagonal vector, the obstruction applies. In particular, a
translation-normalized second-hidden-layer neuron over a forest with `m`
interaction edges factors through its `m` edge differences and one linear
head. If `m≤N−3`, these covectors have rank at most `N−2` in the
`N−1` dimensional diagonal quotient, giving a non-diagonal invariant
direction. Therefore a finite exact maximum representation must contain
at least one neuron with full quotient rank; after forest expansion at least
one forest term has at least `N−2` edges.

The theorem does **not** show that all low-rank terms can be discarded.
A full-rank star forest has matching number one, so full rank alone does
not prove the desired growing-matching obstruction or any exponential
second-width bound.

The abstract rank consequence also applies before normalization: a biased
second-hidden-layer neuron with an affine input skip is invariant under the
common kernel of its input-skip covector and its feeding first-layer covectors.
If that span has rank at most `N−2`, its kernel contains a non-diagonal vector.
For `N≥3`, first-hidden-layer output-skip terms also have such invariant
directions. Thus an arbitrary affine-skip exact maximum representation must
have an original second-hidden-layer neuron whose feeding covectors together
with its input-skip covector span rank at least `N−1`. This consequence needs
a separate finite-dimensional linear algebra and actual-model bridge in Lean;
it is not part of `MaxTent.lean`.

## Reproducibility and alternatives

The proof uses only finite sums, translations, elementary maxima, and the
Archimedean property. It supersedes the initially suggested distributional
proof for formalization purposes. That proof differentiates once in each
coordinate to obtain `(−1)^(N−1)` times diagonal measure, then uses a
polynomial/Fourier support argument; none of those analytic tools is needed
here.
