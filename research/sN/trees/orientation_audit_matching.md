# Arbitrary orientations from a matching-number hypothesis

Status: mathematical proof, with finite exact controls; **not yet a Lean
declaration**. This removes every orientation restriction and allows all
omitted/linear/hinge face states. It does not remove the hypothesis on the
matching number of the original tree. The fully unrestricted all-tree
exponential bound remains open.

The model is exactly `Trees.TreeFace.unit`: an original tree on the `N-1`
nonapex labels, canonical head `x_root-x_apex`, and each edge omitted, linear,
or retained as `sigma(x_i-x_j)` in either orientation. Output coefficients
may have either sign. This is not a theorem about arbitrary real heads or
arbitrary real edge weights.

## The two statements

Write `n=N-1` and let `k` be an integer with `0 <= 2k <= n`.

1. **Pure matching class.** If every unit in an exact expansion of `max_N`
   (plus the paper's auxiliary functions) has an original tree with matching
   number at least `k`, then, for `N>=3`,

   \[
   |K|\ \geq\
   \frac{2^N-1-N-\binom N2}{n\,2^n(3/4)^k}
   \ \geq\ \frac{(4/3)^k}{4n}.
   \]

   Asymptotically the first bound is `(2-o(1))(4/3)^k/n`. This is a
   conditional theorem about any expansion in this class; sufficiency of
   this class by itself is not asserted.

2. **Nonvacuous mixed class.** Let `K0` consist of the existing caterpillar
   and rooted-star face functions, and let `K1` consist of arbitrary
   tree-face units with original matching number at least `k`. Every exact
   expansion of `max_N` by these functions and the auxiliary span satisfies

   \[
   |K_0|+|K_1|\ \geq\ \frac{(169/147)^k}{(N+1)^2}.
   \]

   The dictionary obtained by adjoining the entire `K1` class to the
   existing `K0` dictionary does span `max_N`, because the latter already
   does. Thus this is an exponential lower bound for a known spanning
   dictionary whenever `k >= epsilon (N-1)` for a fixed positive epsilon.
   Its exponential base is `(169/147)^epsilon`.

More generally, the second statement allows any base class with the existing
per-unit locality estimate `#passes_m <= 6^m m! (N-m)!`. Thus it also permits
the reviewed full-hinge source/root arbitrary-shape class when that estimate
is supplied by its degree-two covering forest.

## A weighted connected-subtree bound

For any tree `G` on `n` vertices with matching number `nu`, and any `y>=0`,

\[
\sum_{\substack{\varnothing\ne S\subseteq V(G)\\G[S]\text{ connected}}}
y^{|S|}
\ \leq\ n(1+y)^{n-2\nu}(1+y+y^2)^\nu.
\tag{1}
\]

Fix a vertex `v` and root the tree at `v`. A connected set containing `v`
is ancestor-closed. On each edge of a maximum matching, the assignment
parent absent / child present is forbidden. The other three assignments
have total weight `1+y+y^2`. Since matching edges are vertex-disjoint,
ignoring every other constraint gives the product on the right without
the factor `n`. Summing over the possible `v` counts every nonempty
connected set at least once. This proves (1). It uses no orientation of
the unit's functions; the temporary rooting is only a counting device.

At `y=1`, (1) is `#connected nonempty subsets <= n 2^n (3/4)^nu`.
At `y=1/6`, it is

\[
\sum_S 6^{-|S|}\ \leq\ n(7/6)^n(43/49)^\nu.
\tag{2}
\]

## Why every relevant germ gives a connected original subtree

Use the canonical-head reduction in `all_tree_review.md`, Section 1. For a
tie set `T` of size `m>=3`, set its coordinates to zero and the others to
distinct sufficiently separated negative powers of an integer `B`. The
apex of any nonzero top-dimensional unit germ lies in `T`; its retained
hinges connect `S=T\{apex}`. Hence `S` is a nonempty connected subset of the
original tree, regardless of its orientation or its edge states.

For completeness, the relevant dimension argument is as follows. If the
outer preactivation is nonzero, the local function is a sum of linear and
single-segment support functions, so it has no top class at `m>=3`.
If it is zero, the integer digit argument makes every frozen coordinate
coefficient zero. The apex coefficient is `-1`, forcing the apex into `T`.
If the retained hinge forest on the other `m-1` tied labels is disconnected,
it has at most `m-3` edges; its zonotope pyramid has dimension at most
`m-2`, and therefore also has zero top class. A nonzero top germ consequently
requires the stated connectedness. The detailed reduction additionally
proves that its head is again canonical, but the matching count does not
need that last conclusion.

The local germ of `max_N` is `max_m`, whose simplex class is nonzero modulo
`L_(m-2)`. For example, its generic rational Fourier transform is a nonzero
multiple of `1/(omega_1 ... omega_m)`, whereas every support function of
dimension at most `m-2` vanishes generically. Consequently at least one
unit in the expansion must have a nonzero top germ at every such locality.
The auxiliary functions have dimension at most one and vanish here.

This use of the top quotient is essential: a nonzero mixed finite
difference alone would not imply connectedness of the hinge forest.

## Proof of the pure bound

There are `2^N-1-N-binomial(N,2)` tie sets of size at least three. Choose
one outside order for each tie set and cover it by a nonzero top germ.
A fixed unit has a fixed apex, so its eligible tie sets inject into the
connected nonempty subsets of its original tree. The unweighted version
of (1) bounds their number by `n 2^n (3/4)^k`. Double counting proves the
first displayed inequality.

For `N>=3`, the number of subsets of size at least three is at least
`2^(N-3)`: every subset containing three fixed labels has this property.
Substituting this lower bound gives `(4/3)^k/(4n)`.

## Proof of the mixed bound

The passage count for the base class is the existing result
`Count.treeFace_card_passes_le` with `Delta=2`, together with the
caterpillar bridge. At each `m`, its upper bound for a fixed unit is
`6^m m! (N-m)!` over all `N!` permutations defining the localities.
A nonzero top germ satisfies those passage conditions: outside coefficients
are balanced, and a tied vertex isolated in the hinge graph must carry a
nonzero head coefficient. In the connected case every nonapex tied vertex
has a hinge neighbour; the apex has coefficient `-1`.

Choose one integer `B` large enough for the digit argument for every unit
in the finite expansion. Its value does not affect any of the counts.
For every permutation-locality, cover the nonzero maximum top class by a
nonzero unit top germ. Divide the resulting cover inequality at level `m`
by `m!(N-m)!`, and multiply by `y^m`, where `y>0`. The base class contributes
at most `(6y)^m` per unit at level `m`. A unit in the matching class
contributes, after summing over levels, at most

\[
\sum_{T\text{ eligible}}y^{|T|}
\ \leq\ ny(1+y)^n\rho^k,
\qquad \rho=\frac{1+y+y^2}{(1+y)^2},
\tag{3}
\]

by (1), including the extra factor `y` for its fixed apex. For each fixed
tie set there are exactly `m!(N-m)!` permutations, so the inequality is
valid even if some outside orders give zero germs. Thus

\[
(1+y)^N-1-Ny-\binom N2 y^2
\ \leq\ \left(\sum_{m=3}^N(6y)^m\right)|K_0|
+ny(1+y)^n\rho^k |K_1|.
\tag{4}
\]

This is the general finite inequality. The especially simple choice
`y=1/6` gives

\[
(7/6)^N-1-N/6-\binom N2/36
\ \leq\ (N-2)|K_0|+
\frac n6(7/6)^n(43/49)^k |K_1|,
\tag{5}
\]

and implies the slightly weaker mixed lower bound
`Z >= (49/43)^k/(N+1)^2`, where `Z=|K0|+|K1|`.

For the stated improved constant, take `y=2/11`, so `rho=147/169`. Set
`E=(13/11)^N rho^k` and `P=1+2N/11+4 binomial(N,2)/121`. Then

\[
E=(13/11)^{N-2k}(147/121)^k\geq(12/11)^N\geq1,
\]

because `2k<=N-1`, `13>=12`, and `147>=12^2`. Thus
`sum_{m=3}^N (12/11)^m <= (N-2)E`. Also `Z>=1`: the auxiliary span alone
cannot represent `max_N` at a tie of size three. Substitution into (4) gives

\[
(13/11)^N\leq\bigl(P+N-2+2n/13\bigr)EZ
\leq(N+1)^2 EZ.
\]

The last inequality follows by expansion: multiplying its coefficient by
`1573=121*13` gives `26N^2+2075N-1815`, which is at most `1573(N+1)^2`
for every nonnegative integer `N`. Cancelling `(13/11)^N` proves
`Z >= (169/147)^k/(N+1)^2`, including the boundary `N=3`.

## Explicit newly covered families

* A tree with a perfect or near-perfect matching, with every edge orientation
  and every face state, has `k=floor((N-1)/2)`. The mixed lower bound has
  exponential base `sqrt(169/147)`, approximately `1.0722`.
* The star with each edge subdivided once has `n=2L+1` vertices and matching
  number `L`. Every orientation and every face state is covered. In particular,
  this includes the faces obtained by linearizing all outer arm edges, which
  can create `L` outward hinge leaves at the centre and defeated the previous
  bounded-outleaf condition.
* A centre joined to `L` leaves and to an additional path of `2L` vertices
  has `n=3L+1` and matching number `L+1`. Its original centre can have `L`
  outward leaves. Thus even full-hinge units in the new class can have
  unbounded outward-leaf count.

There is also an orientation-free shape criterion. If the original tree has
`L` leaves and `n>=2`, then

\[
\nu\geq(n-L+1)/2.
\tag{6}
\]

To prove it, take a minimum vertex cover `C` of size `nu` (the matching/cover
equality for a bipartite graph). Its independent complement has `n-nu`
vertices. If `b` of these are nonleaves, the sum of their degrees is at
least `n-nu+b` and at most `n-1`, so `b<=nu-1`. There are therefore at most
`nu+(nu-1)` nonleaves in the whole tree, which is (6). Consequently every
class in which a fixed positive fraction of vertices are nonleaves is
covered, with no restrictions on orientation or face states.

Trees with matching number `o(N)`, including arbitrary oriented stars,
are not resolved by this theorem. Uniform outward-twin separation remains
a sufficient route for those trees, as recorded in `all_tree_review.md`.

## Why the old passage bound cannot simply lose its orientation hypothesis

Consider the opposite orientation of a rooted star:

\[
U(x)=\sigma\left(x_c-x_a+\sum_{\ell}\sigma(x_\ell-x_c)\right).
\]

At every top tie set `T` containing the apex `a` and centre `c`, all untied
leaf hinges are inactive. The germ is precisely the same canonical star
unit on the tied leaves, and its pyramid has dimension `|T|-1`. It passes
for every outside order. At each fixed level `m>=3`, this gives at least

\[
\binom{N-2}{m-2}m!(N-m)!
\]

passing permutations. No constant `C`, independent of `N`, can therefore
bound every arbitrary-orientation unit by `C^m m!(N-m)!`: already at `m=3`
that would require `N-2<=C^3`. The star has matching number one, so it is
exactly outside the new linear-matching hypothesis.

This refutes an extension of the existing *per-unit counting mechanism*.
It is not a counterexample to an all-tree exponential lower bound; a new
linear separator may force cancellation of such germs across the expansion.
Uniform outward-twin separation would provide one such mechanism.

## Exact controls and reproducibility

`orientation_audit_matching.py` enumerates all nonisomorphic trees on
2 through 11 vertices, computes the maximum matching by exhaustive edge
subsets independently of the tree generator, and checks the two weighted and
unweighted connected-subset estimates by enumerating all vertex subsets.
It also checks the leaf-count matching criterion (6), the rooted
ancestor-closure assertion used in (1), and the
elementary finite constants in the two theorem statements. The JSON receipt
records counts and the producer's SHA-256. These finite checks test the
proof's combinatorial calculations; they are not a substitute for its
uniform mathematical argument or a Lean proof.
