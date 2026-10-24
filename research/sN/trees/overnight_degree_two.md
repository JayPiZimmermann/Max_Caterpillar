# Exponential width for arbitrary weighted path and cycle units

25 October 2026. A uniform mathematical proof, independently reviewed by the
construction agent. This is not a Lean declaration or an unrestricted
all-tree bound. Unlike the finite small-arity probes, the result below holds
for every input dimension in its stated range.

## Statement

Let `N>=3` and suppose

`max_N = R + sum_(j in K) d_j U_j`,

where `R` is any finite shallow ReLU function (a linear function plus a finite
linear combination of ReLUs of linear forms), and

`U_j(x)=sigma(h_j(x)+sum_(e=(u,v)) c_(j,e) sigma(x_u-x_v))`.

The heads `h_j`, inner coefficients `c_(j,e)`, and output coefficients `d_j`
are arbitrary real numbers/functions; signs and edge orientations are
unrestricted. For each unit, the simple undirected graph of comparisons with
nonzero coefficients has maximum degree at most two. Thus it is a disjoint
union of paths, cycles, and isolated vertices. Parallel comparisons may first
be merged, and reversed comparisons may be absorbed into the linear head.

For every integer `3<=m<=N`,

`binom(N,m) <= (N + (m-1)N^2/2) |K|`.

In particular, choosing `m=floor(N/2)` for `N>=6` gives
`|K|=Omega(2^N/N^(7/2))`.

The same conclusion holds with arbitrary biases in the finite network.
Taking its recession function `lim_(t->infinity) F(tx)/t` removes every bias,
preserves its graph supports and widths, and preserves the homogeneous
target `max_N`. The shallow remainder is allowed for free. Consequently the
claim is a lower bound on the counted second-hidden-layer units even when
linear heads and an arbitrary shallow skip are supplied.

## A top tie requires at most two connected components

Fix an `m`-element set `T`, use the base direction `1_T`, and vary only the
coordinates in `T`, fixing one of them to zero. The directional germ of the
target is the support function of an `(m-1)`-simplex. Its class modulo
`L_(m-2)` is nonzero. One elementary proof is induction: opposite exposed-face
differences lower the filtration by one and send a simplex to a facet modulo
a linear function; the one-dimensional simplex support function is not linear.

For a comparison `sigma(x_u-x_v)`, unequal base coordinates give a linear or
zero germ. Comparisons entirely outside `T` restrict to zero. Thus only edges
of the induced graph `G_j[T]` remain nonlinear. If this graph has `c`
connected components, including isolated vertices, its comparison forms have
rank `m-c`: within a component their span is the codimension-one subspace of
coefficient vectors summing to zero, and different components are disjoint.

If a unit's outer preactivation is positive at the base direction, its germ
is in `L1`; if it is negative, the germ is zero. If it is zero, the germ
depends on those `m-c` comparison forms and one resulting linear head. It
therefore belongs to `L_(m-c+1)`, even with signed inner coefficients. To see
this directly, split the preactivation as `h_P-h_Q`, where `P,Q` are translated
zonotopes lying in the span of those forms. Then

`sigma(h_P-h_Q)=h_conv(P union Q)-h_Q`.

Both polytopes have dimension at most `m-c+1`. Restricting one tied coordinate
to zero cannot increase that dimension. If `c>=3`, the germ is therefore in
`L_(m-2)`. Every germ of the shallow remainder is in `L1`, also contained in
that space because `m>=3`. Some counted unit must consequently have
`c(G_j[T])<=2`.

## Count those ties

For a fixed maximum-degree-two graph `G` on all `N` labels, let `C_k` be its
number of connected induced `k`-vertex subsets. Each path component on `n`
vertices contributes at most `n` such subsets. Each cycle component also
contributes at most `n`: a proper connected subset is an arc, and the whole
cycle is one additional size case. Summing component sizes gives `C_k<=N`
for every positive `k`.

An `m`-element tie with at most two induced components is either connected,
or is the unordered union of two connected induced sets of complementary
sizes. Ignoring the requirements that these sets be disjoint and have no
edge between them only increases the count. Hence its number is at most

`C_m + (1/2) sum_(k=1)^(m-1) C_k C_(m-k)
 <= N + (m-1)N^2/2`.

This includes equal-sized components: the two components are distinct and
occur in both orders. Since every one of the `binom(N,m)` ties needs a
counted unit, summing these capacities proves the bound. The central
binomial coefficient is `Theta(2^N/sqrt(N))`, giving the stated asymptotic.

## Scope

This covers all cycle orders, disconnected unions of paths and cycles,
arbitrary real heads, arbitrary signed inner and output coefficients, and
all edge states. It strengthens the lower bound substantially for this
particular graph class. It does not cover branching trees, including stars
and general caterpillars: those graphs can have exponentially many connected
induced subsets. Nor does it cover arbitrary multivariate first-hidden-layer
directions used inside the counted units.

The separate sharper cycle-only capacity and the uniform affine-cycle
obstruction are in `overnight_upper_cycle_locality.md`. They are not needed
for this proof.
