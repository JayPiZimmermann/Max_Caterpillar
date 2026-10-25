# Ordered boundary states: the product route and its limit

The nine-square construction in `overnight_upper_ordered_product.md`
is a genuine coherent lift of the four-simplex boundary. It eliminates
factorial averaging at that one step. It does not iterate by simply
multiplying more triangle boundaries.

A natural higher-dimensional candidate fixes a ghost label `r`, takes a
two-component forest `F` on the other `N-1` labels, and forms

\[
Y_{F,r,\epsilon}=\prod_{ij\in E(F)}
       \partial\bigl(\epsilon_{ij}\Delta_{rij}\bigr),
\qquad \epsilon_{ij}\in\{-1,1\}.
\]

There are `N-3` factors. The result is automatically a cubical cycle of
the correct degree for lifting the boundary of the `(N-1)`-simplex. Each
product has at most `3^(N-3)` cubes. For a noncrossing forest, every cube
uses directions in the union of that forest and the ghost star: a graph
drawable on two pages. This would have been an exponential construction
route if these cycles spanned the required simplex boundary.

They do not, already for `N=6`, even when all label permutations and all
independent triangle reflections are allowed. On five nonghost labels,
the complete two-component forest inventory has three shapes:

* an isolated vertex and a four-vertex star;
* an isolated vertex and a four-vertex path;
* an edge and a three-vertex path.

All `3*2^3=24` signed shape representatives were projected to the oriented
`S_6`-invariant boundary class. The rational function columns have rank
three, while adjoining the simplex boundary gives rank four. The upper
rank bound is exact: all 21 reconstructed rational kernel relations were
checked by principal-part elimination on every supporting hyperplane.
A modular augmented minor supplies the lower rank bound, with a prime
that does not divide the evaluation denominators. Thus this is an exact
finite obstruction, not a sampled-rank conclusion.

The orientation character matters: a label permutation acts on the
oriented simplex class by its sign. The projection therefore sums
`sign(pi) * pi(Y)`, not the unsigned chains. Since the family is closed
under all permutations, an arbitrary nonsymmetric identity would also
give an identity in this projected family. Changing the order of forest
edges or reversing the ordered vertices of a triangle only changes an
overall scalar, which is already unrestricted.

The smaller tests give useful controls. The original five-label product
agrees exactly with its simplex boundary on every hyperplane. One fixed
six-label product has three extraneous supporting hyperplanes, each
carrying a single nonzero pyramid class. With signs constant and opposite
on the two components, the full permutation family has ranks one and
two. The independent-reflection test strictly enlarges that family and
still excludes the target.

This excludes only products of triangle boundaries sharing one ghost
vertex and indexed by a two-component forest. It does not exclude general
relative chains, translated products, products of other cycles, the full
two-component noncrossing network family, or a uniform exponential
construction. Further work needs a nonproduct boundary state or another
exact algebraic recurrence; increasing the sign alphabet cannot repair
the family just tested.

Sources and exact receipts are `overnight_upper_product_signs.py` and
`overnight_upper_product_signs_6.json`, with the Fourier convention in
`overnight_upper_product_family.py`. The symbolic checker is
`all_tree_dfs/rational_identity.py`. These are mathematical research
certificates, not Lean results.
