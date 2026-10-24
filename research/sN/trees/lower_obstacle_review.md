# Why raw survival cannot prove the unrestricted tree bound

Independent mathematical audit. No new numerical search is used here.
The unrestricted all-tree exponential lower bound remains open.

## One unit survives on a constant fraction of all ties

Fix an apex `a`, a centre `c`, and the other `N-2` labels as leaves. Take

\[
U(x)=\sigma\left(x_c-x_a+
\sum_{\ell\ne a,c}\sigma(x_\ell-x_c)\right).
\]

For any leaf subset `S`, set the coordinates of `T={a,c} union S` to zero
and the remaining leaf coordinates to strictly negative distinct values.
In a sufficiently small neighbourhood, every untied leaf hinge is zero.
The local homogeneous germ on the tied coordinates is consequently

\[
U_T(y)=\sigma\left(y_c-y_a+
\sum_{\ell\in S}\sigma(y_\ell-y_c)\right),
\]

exactly the same canonical outward star on `m=|T|` labels. This conclusion
holds for every outside order; no balance cancellation is needed because
all outside hinges are inactive.

Its top class is nonzero. For example, the established generic Fourier
formula, omitting a common nonzero factor, is

\[
R_{U_T}(\omega)=
\frac{(-\omega_a)^{m-4}}
 {\prod_{\ell\in S}\omega_\ell(\omega_\ell+\omega_a)},
\qquad \sum_{i\in T}\omega_i=0.
\]

At `omega_a=-(m-1)` and every other frequency equal to one, all displayed
denominators are nonzero and the value is
`(m-1)^(m-4)/[-(m-2)]^(m-2) != 0`. Every element of `L_(m-2)` has zero
generic Fourier transform, so the star germ does not belong to that
lower-dimensional span.

For `N>=5`, the exact number of such tie sets with size at least five is

\[
2^{N-2}-1-(N-2)-\binom{N-2}{2}.
\]

This is asymptotically one quarter of all subsets of the labels.
Therefore a universal raw per-unit survival estimate of the form
`poly(N)*(2-epsilon)^N`, for any fixed positive epsilon, is false even
for a star. A proof cannot simply count every nonzero top germ as a
separate locality covered by that unit and expect exponential savings.

This is **not** a short representation of the maximum. The surviving
star germ is not the simplex germ for `m>=5`. The uniform star separator
annihilates all these nonzero star classes while taking a nonzero value
on the maximum. Thus separator-based counting remains possible; raw
survival counting alone is the invalid strategy.

## Precise odd-tie sufficient hypothesis

Suppose there is a fixed odd `m0>=5` such that, for every odd `m>=m0`,
`max_m` is outside the span modulo `L_(m-2)` of canonical tree units whose
`m-1`-vertex trees have no perfect matching. This is currently unproved.

The canonical-germ reduction would force a perfectly matchable nonapex
subtree at each large odd tie. Each such subtree is encoded by its
perfect matching in the original tree. An original tree on `N-1`
vertices has at most `F_N` matchings, by the leaf recurrence, where
`F_1=F_2=1`. Consequently the hypothesis would imply

\[
|K|\geq
\frac{2^{N-1}-\sum_{\substack{j<m_0\\j\text{ odd}}}\binom Nj}{F_N}.
\]

The exponential base is `2/phi`, approximately `1.236`, with
`phi=(1+sqrt(5))/2`. The fixed apex contributes no extra choice, and
odd ties need no unmatched vertex, so no factor `N` is needed in the
denominator. This remains a **conditional** route, not an all-tree theorem.

## What the coordinate-deletion obstruction does and does not say

At even arity `m>=4`, take any canonical tree unit `U`, duplicate any
original leaf by attaching a fresh nonroot leaf `j` to the same neighbour
`h`, and orient the new hinge as `sigma(x_j-x_h)`. The new even-vertex
tree cannot have a perfect matching, since the two leaves share `h`.

Yet the operator
`T_j=(partial_{-e_j}-partial_{e_j})` followed by inserting `x_j=0`
recovers `U` modulo a translated-zonotope support function in `L_1`.
Thus one fixed coordinate deletion maps the bad-perfect-matching family
at arity `m+1` onto all canonical tree units at arity `m`, at the level
relevant to the lower-dimensional quotient.

Since those lower-arity units span the maximum class, no separator which
factors through that one fixed deletion can solve the new odd-arity step.
This is an obstruction to that precise recursion. It does **not** rule
out combinations of different first directions, noncoordinate directions,
or another invariant, and it does not refute the matching-separation
hypothesis itself.

The canonical head `x_root-x_apex`, unit edge coefficients, and tree-face
states remain part of every assertion here. No claim is made for arbitrary
real heads or arbitrary weighted graphs.
