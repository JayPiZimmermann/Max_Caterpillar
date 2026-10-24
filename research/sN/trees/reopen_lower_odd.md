# Reopened lower-bound route: odd ties and a recursion obstruction

The unrestricted all-tree exponential lower bound is still **open**.
This note proves two useful refinements: the matching-based sufficient
separation hypothesis only needs odd arities, with no polynomial loss in
the resulting count; and one fixed coordinate deletion cannot prove the
new odd-arity separation steps. The latter is a uniform counterexample
to a proof strategy, not a counterexample to separation itself.

## A weaker sufficient hypothesis with a sharper consequence

Assume that for every sufficiently large **odd** integer `m`, the class
of `max_m` is outside the span modulo `L_(m-2)` of canonical tree units
whose `(m-1)`-vertex hinge tree has **no perfect matching**. The root,
tree, and every edge orientation may vary among the units in that span.

This is enough for an unrestricted all-tree exponential lower bound.
Let `m0>=5` be an odd threshold after which the hypothesis holds, and
consider an expansion of `max_N` by arbitrary `Trees.TreeFace.unit`
functions and the auxiliary span. At every odd tie set `T` with
`|T|>=m0`, the canonical-head reduction and the hypothesis force some
summand whose nonapex tied labels `S` induce a perfectly matchable tree.

For a fixed original unit with tree `G` on `n=N-1` vertices, choose the
perfect matching of `G[S]`. A forest's perfect matching is unique: the
symmetric difference of two distinct ones would contain a cycle. More
basically, any matching determines its covered vertex set, so distinct
sets `S` cannot give the same matching. Hence the number of eligible tie
sets for that unit is at most the number `M(G)` of all matchings in `G`.
The apex is fixed and contributes no additional choice. There is also
no unmatched vertex to record, because `|S|=|T|-1` is even.

For every forest on `n` vertices, `M(G)<=F_(n+1)`, where `F_1=F_2=1`
are the Fibonacci numbers. Delete an isolated vertex if one exists.
Otherwise take a leaf `l` with neighbour `v` and use
`M(G)=M(G-l)+M(G-{l,v})`; the induction follows from the Fibonacci
recurrence. In particular, `M(G)<=phi^n` for
`phi=(1+sqrt(5))/2`.

There are exactly `2^(N-1)` odd subsets of an `N`-element set. Covering
the large ones therefore gives the conditional bounds

\[
|K|\geq
\frac{2^{N-1}-\sum_{\substack{j<m_0\\j\text{ odd}}}\binom Nj}{F_N}
\geq
\frac{2^{N-1}-\sum_{\substack{j<m_0\\j\text{ odd}}}\binom Nj}
     {\varphi^{N-1}}.
\]

The latter is asymptotic to `(2/phi)^(N-1)`, with base about `1.236`.
This improves the earlier conditional count by removing its factor `N`,
and requires separation only at odd arities. The Fibonacci denominator
is a further exact improvement. Neither inequality is asserted
unconditionally: the uniform odd-arity separator is still unproved.

## Odd-arity separation automatically supplies the next even arity

Suppose the bad-perfect-matching family is separated at arity `2q+1`.
At arity `2q+2`, a tree which lacks a near-perfect matching has `2q+1`
vertices and matching number at most `q-1`. Apply one fixed coordinate
deletion operator `T_j` from `orientation_audit_stars.md`.

Deleting the apex or an internal vertex gives zero in the next top
quotient. Deleting a leaf gives a signed canonical tree unit on `2q`
vertices, or zero; its matching number is still at most `q-1`, so it
has no perfect matching. Root transfer at a root leaf does not change
this graph statement. Also `T_j max_(2q+2)=max_(2q+1)` and
`T_j L_(2q) ⊆ L_(2q-1)`. Composing with the odd-arity
separator consequently proves the next even-arity separation statement.

Thus the genuinely new matching-separation obligations arise only at
odd arities. This implication does not advance from one odd arity to
the next.

## Uniform obstruction to a fixed-coordinate deletion induction

Fix any even arity `m>=4`, any canonical tree unit `U` on those labels,
and a fresh label `j`. Its original tree has the odd number `m-1` of
vertices. Choose any original leaf `l` and let `h` be its neighbour.
Adjoin the new leaf `j` at `h`, with hinge `sigma(x_j-x_h)`, keeping the
original apex and root. Call the new canonical unit `V`.

The two leaves `l,j` share the same neighbour. The new tree has an even
number `m` of vertices and **cannot** have a perfect matching, since
both leaves would need to use `h`. This conclusion is independent of
the old leaf's orientation and whether it is the head root.

Nevertheless,

\[
\mathcal T_j V=U-h_{Z'}\equiv U\pmod{L_1},
\]

where `Z'` is a translated zonotope. Indeed, all old generators and the
old head have zero `j` coordinate. The new generator has `j` coordinate
one. The minimum coordinate face of the pyramid is exactly the original
pyramid with that generator fixed at zero, whereas the maximum face is
the translated old base with the generator fixed at one. Projection
deletes `j` and recovers `U` in the former face. This is precisely the
nonroot outward-leaf case of the deletion table.

Therefore the image under one fixed `T_j` of the bad-perfect-matching
family at arity `m+1` contains **every** canonical tree unit at arity `m`,
modulo the lower-dimensional span. Those canonical units span the
maximum's top class, by the existing caterpillar construction (all
nonhinge states vanish in that quotient).

Consequently there is no lower-arity linear functional `Lambda` which
both takes a nonzero value on `max_m` and makes `Lambda o T_j` annihilate
the whole bad-perfect-matching family at arity `m+1`. This refutes the
single-coordinate-first recursion at every new odd step, uniformly.

It does not exclude combinations of different first directions or other
functionals. The existing five-label separator already uses noncoordinate
first directions alongside coordinate ones, so it is not contradicted.
It also does not refute the outward-twin conjecture: in the construction
above the original leaf may point inward or may be the head root, so the
new tree need not have two nonroot outward leaves.

## Exact controls

The producer `reopen_lower_odd_check.py` checks all nonisomorphic trees
through 11 vertices for the matching count and uniqueness of covered
vertex sets. It also checks every root, orientation, and duplicated-leaf
choice on every tree with 3, 5, or 7 vertices, directly comparing the
minimum and maximum exposed vertex sets with the original pyramid and
translated zonotope. The receipt is `reopen_lower_odd_check.json`, with
producer hash; the run completed with exit status zero in 5.20 seconds.
These controls supplement the uniform proofs above. They do not prove
the open matching-separation hypothesis.
