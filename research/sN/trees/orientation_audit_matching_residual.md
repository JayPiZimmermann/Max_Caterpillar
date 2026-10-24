# A matching-deficiency residual for the unrestricted all-tree bound

Status: **conditional counting theorem**. The uniform separation hypothesis
below is open. Finite modular rank gaps, including the root's seven-label
probe, do not prove that hypothesis over the rationals or uniformly.

## Strong candidate local separation statement

For every sufficiently large `m`, the simplex class `max_m` is outside
the span modulo `L_(m-2)` of canonical root-head tree units whose
`m-1`-vertex hinge tree has matching number strictly less than
`floor((m-1)/2)`. Equivalently, the forbidden trees have neither a perfect
matching nor a matching leaving exactly one vertex uncovered.

This agrees with the exact five-label all-star certificate and the
uniform all-oriented-star theorem, which also covers the six-label
instance. The seven-label instance remains a modular diagnostic in the
current probe. None of these observations proves the general statement.

## Conditional unrestricted exponential count

Assume the local separation statement for every `m>=m0`, with fixed `m0`.
At each `m`-label top tie, the canonical-head germ reduction and the
separation statement force at least one summand whose retained hinge tree
has a perfect or near-perfect matching. Its nonapex tied labels form a
connected subset `S` of the unit's original tree `G`, and that induced
subtree has such a matching.

Put `n=N-1` and let `M(G)` be the number of all matchings in `G`, including
the empty one. Each eligible `S` is the union of the vertices of a matching
`M` and at most one additional unmatched vertex. Choose one such matching
by a fixed deterministic ordering. The pair `(M, optional extra vertex)`
determines `S`, hence

\[
\#\{S\text{ eligible}\}\leq(n+1)M(G).
\tag{1}
\]

A perfect matching of a forest is in fact unique when it exists, because
the symmetric difference of two would contain a cycle. But uniqueness is
not needed for (1), and near-perfect matchings need not be unique.

For every forest `F` on `n` vertices,

\[
M(F)\leq\varphi^n,\qquad \varphi=(1+\sqrt5)/2.
\tag{2}
\]

Induct on `n`. An isolated vertex can be deleted without changing `M`.
Otherwise choose a leaf `l` with neighbour `v`. Split matchings according
to whether they contain the edge `lv`:
`M(F)=M(F-l)+M(F-{l,v})`. The induction hypothesis and
`phi^(n-1)+phi^(n-2)=phi^n` prove (2). The empty forest is the base case.

The apex of each unit is fixed, so its possible tie sets inject into
these eligible `S`; there is no additional factor for choosing an apex.
Cover all tie sets of size at least `m0` to obtain

\[
|K|\ \geq\
\frac{2^N-\sum_{j=0}^{m_0-1}\binom Nj}
     {N\varphi^{N-1}}.
\tag{3}
\]

Thus the conditional exponential base is `2/phi`, approximately `1.236`.
This covers arbitrary original tree shapes, every root and edge orientation,
and every omitted/linear/hinge state, still with the canonical root-minus-
apex head. It is not an unconditional all-tree theorem.

## A weaker uniform hypothesis already suffices

The near-perfect condition above is stronger than necessary. Fix any
constant integer `d>=1`. It would suffice to prove that, for all sufficiently
large `m`, the simplex class is outside the span of canonical trees with
matching deficiency greater than `d`, where the deficiency is
`(m-1)-2 nu`. A surviving germ would then have a matching with at most
`d` uncovered vertices.

Encoding an eligible set by such a matching and its at most `d` uncovered
vertices gives

\[
\#\{S\text{ eligible}\}\leq
M(G)\sum_{j=0}^d\binom nj
\leq\varphi^n\sum_{j=0}^d\binom nj.
\]

For fixed `d`, this changes only a polynomial factor in (3), preserving
the exponential base `2/phi`. A failure of the strongest near-perfect
separation conjecture therefore would not close this counting route.

## Scope of coordinate deletion

The coordinate deletion operator from `orientation_audit_stars.md`
preserves a canonical tree top class only when the deleted label is a
leaf, with the same sign and root-transfer cases as for stars. Deleting
an internal vertex of degree at least two leaves at most `m-4` free
segments; adjoining the apex gives dimension at most `m-3`, so its class
vanishes at the next level. Deleting the apex gives a zonotope in `L_1`.
Thus any finite separator for the class `nu<=b`, at a fixed arity,
propagates to all larger arities for that same fixed `b`.

This does not by itself prove the growing threshold
`nu<floor((m-1)/2)`: the allowed matching number in that hypothesis changes
with `m`. Nor does it prove outward-twin separation, because deleting a
leaf can destroy the only twin pair while leaving a nonzero canonical
tree class. These are the precise limitations of the deletion mechanism.
