# A two-component noncrossing boundary dictionary

This is a precise open construction route, not a sufficiency theorem.
It retains boundary states that scalar rooted-tree recurrences discard.

Fix a cyclic label order. Let `F` be a noncrossing forest on all `N`
labels with exactly two tree components `P,Q`. Choose roots `r in P`
and `s in Q`, and orient all `N-2` forest edges independently. The basic
atom is

\[
\sigma\left(x_r-x_s+\sum_{e\in F}\sigma(\ell_e(x))\right),
\]

where every `ell_e` is one oriented coordinate difference. The head edge
`rs` is allowed to cross forest edges. This includes the existing
canonical noncrossing-tree dictionary when one component is a singleton.
It also includes the two nontrivial components arising from full-label
cycle facets.

Every noncrossing forest extends to a triangulation. Fewer than `4^N`
triangulations and fewer than `4^N` edge subsets of each give the loose
bound `16^N` on forests. At most `N^2` root pairs and five states per
forest edge give fewer than `N^2 80^N` function descriptions, including
all faces. Faces not containing the outer apex are shallow translated
zonotope support functions. The first hidden layer still needs only the
global coordinate channels and functions `sigma(x_i-x_j)`.

Consequently a uniform top-class identity for this dictionary would
settle the requested exponential upper construction by the existing
face-reduction argument. The bound is conditional on that missing
identity.

The two component vertex sets must be complementary cyclic intervals.
Otherwise four cyclically alternating labels from the two components
would force their connecting paths to cross. This reduces the external
component split in a prospective recurrence to `O(N^2)` interval cuts;
the internal noncrossing trees and their attachment/head data still
require a genuine recurrence.

## The exact boundary kernel

On `sum_i omega_i=0`, put `a=sum_(v in Q) omega_v`. Root each component
at its chosen root. For an edge `e`, let `q_e` be the frequency sum in
its root-away component and let `epsilon_e` be `+1` if the positive
endpoint of its oriented difference belongs to that component, and `-1`
otherwise. In the existing Fourier normalization the atom has kernel

\[
R_F(\omega)=
\frac{(-a)^{N-4}}{\prod_e q_e(q_e+\epsilon_e a)}.
\]

Independent edge-difference coordinates together with `x_r-x_s` have
unimodular Jacobian. The frequency of the root difference is `-a`, which
gives the stated prefactor and signs. This is the canonical formula with
a whole external component replacing its singleton apex.

General shifted heads require the additional cut/head data recorded in
`overnight_upper_full_cycle.md`. Discarding those shifts during a graft
would change the rational function.

## An exact exchange relation, and its limit

The orientation agent supplied the following whole-function identity for
arbitrary real linear forms `t_1,...,t_m`:

\[
\sum_{\varnothing\ne I\subseteq[m]}
(-1)^{|I|+1}
\sigma\left(\sum_{i\in I}t_i+
             \sum_{j\notin I}\sigma(t_j)\right)
=\sum_j\sigma(t_j).
\]

There is an elementary pointwise proof. Put `P=sum_j sigma(t_j)`. The
`I`-term is `sigma(P+sum_(i in I, t_i<0)t_i)`. If one `t_i` is
nonnegative, the alternating sum over **all** `I`, including the empty
set, cancels by toggling that index. Removing the empty term leaves
`sigma(P)=P`. If all `t_i` are negative, every term is zero. Geometrically,
this is inclusion-exclusion for the cube's facet pyramids opposite the
origin; the intersection indexed by `I` has base
`1_I+sum_(j notin I)[0,e_j]`.

For the independent edge forms of a tree on all labels, the singleton
terms are the different choices of one head edge; all terms with
`|I|>=2` have dimension at most `m-1`. Thus the sum over all head-edge
placements vanishes in the top quotient, with explicit face corrections.
This relation moves a mark within one underlying tree. It does not
change that tree, so it does not by itself uncross arbitrary trees or
prove the target identity.

At four inputs the two-component state already has a concrete role. With
`P={a,b}`, `Q={c,d}`, the term

\[
U=\sigma\bigl(b-d+\sigma(a-b)+\sigma(d-c)\bigr)
 =\sigma(\max(a,b)-\min(c,d))
\]

satisfies

\[
\max(a,b,c,d)=
 \sigma\bigl(b-d+\sigma(a-b)\bigr)
+\sigma\bigl(b-c+\sigma(a-b)\bigr)
-U+\sigma(c-d)+d.
\]

The first two outer terms have only three-label support. Hence `-U`
already equals the four-input maximum in the top quotient. This example
checks the sign of the two-component kernel, but does not provide an
induction step at larger arities.

The remaining problem is a recurrence for the *symmetric simplex target*
that retains the external component and attachment shifts. Spanning
every old caterpillar function by this fixed exponential dictionary is
not an admissible stronger target: the known factorial dictionary
dimension bound rules that out uniformly.
