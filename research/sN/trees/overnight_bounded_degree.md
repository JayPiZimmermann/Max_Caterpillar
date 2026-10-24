# Exponential width for bounded-degree comparison forests

25 October 2026. A uniform mathematical argument, independently reviewed by
the construction agent. This is not a Lean theorem. It covers arbitrary
orientations, real linear heads, and signed inner and output coefficients.
The unrestricted all-tree exponential bound remains open.

## Statement

Use the network model of `overnight_degree_two.md`:

`max_N = R + sum_j d_j sigma(h_j(x) + sum_(uv in G_j) c_juv sigma(x_u-x_v))`,

where `R` is an arbitrary finite shallow ReLU function. Each simple comparison
graph `G_j` is a forest on all `N` labels, including isolated vertices, and
has maximum degree at most `Delta`. Put

`A_N = 1 + N/2 + binom(N,2)/4`.

For `N>=3`, the number of second-hidden-layer units satisfies

`|K| >= (1-A_N*(2/3)^N)/A_N * (27/23)^(N/(Delta+1))`.

Consequently every fixed maximum degree gives an exponential lower bound,
`Omega_Delta((27/23)^(N/(Delta+1))/N^2)`. This includes all bounded-degree tree
shapes and all orientations, with no canonical-head or unit-length assumption.
Arbitrary biases are allowed by taking the recession function. More strongly,
the same bound holds for the number of distinct simple comparison graphs
used: repeating a graph with different weights and heads does not enlarge
the set of ties it can serve in the argument below.

For arbitrary graphs of maximum degree at most `Delta`, the analogous bound is

`|K| >= (1-A_N*(2/3)^N)/A_N
        * (1-(2/3)^Delta/3)^(-N/(Delta^2+1))`.

Thus bounded degree suffices even if cycles are allowed. The sharper
`Omega(2^N/N^(7/2))` result in `overnight_degree_two.md` remains preferable
when the maximum degree is two.

## The locality input

For every tied set `T` of size at least three, some graph `G_j[T]` must have
at most two connected components, counting isolated vertices. This is exactly
the rank argument proved in `overnight_degree_two.md`: a graph with `c`
components supplies only `|T|-c` independent free comparison forms, and one
linear head adds at most one dimension. If `c>=3`, the unit's germ lies in
`L_(|T|-2)` and cannot supply the top class of the tied maximum. The shallow
remainder has its germ in `L1` and does not change this conclusion.

## Count ties by isolated selected vertices

Select a random subset `T` by including every label independently with
probability one third. For a vertex `v`, the event that `v` is an isolated
vertex of `G[T]` has probability

`p_v = (1/3)*(2/3)^deg(v)`.

Events for vertices with pairwise disjoint closed neighborhoods are
independent. If `C` is such a collection, then

`Pr(c(G[T])<=2) <= Pr(at most two isolated-selected events in C)`

`= product_(v in C)(1-p_v)
   * (1 + sum_(v in C) p_v/(1-p_v)
        + sum_({v,w} subset C) p_v p_w/((1-p_v)(1-p_w)))`

`<= A_N product_(v in C)(1-p_v)`.

The last inequality uses `0<p_v<=1/3`, so every displayed odds ratio is at
most one half. Empty induced graphs and ties of size one or two are harmless:
we will only require coverage of sets of size at least three.

## Find a large product saving in a forest

The square of a maximum-degree-`Delta` forest admits a coloring with
`Delta+1` colors. Here is a direct construction. Root every nontrivial
component and color vertices in breadth-first order. A vertex must avoid
the colors of its parent, grandparent, and previously colored siblings;
there are at most `Delta` such colors. The root case and its children use
no more colors. These are all the previously colored vertices at distance
at most two. Each color class therefore has disjoint closed neighborhoods.

A forest has at most `N` edges, so

`product_v p_v = 3^(-N)*(2/3)^(2|E|) >= (4/27)^N`.

The arithmetic-geometric mean inequality first gives
`(sum_v p_v)/N >= 4/27`, and then gives

`product_v (1-p_v) <= (1-(sum_v p_v)/N)^N <= (23/27)^N`.

The `Delta+1` color classes partition this product. At least one class `C`
therefore satisfies

`product_(v in C) (1-p_v) <= (23/27)^(N/(Delta+1))`.

For that class the preceding probability estimate becomes

`Pr(c(G[T])<=2) <= A_N (23/27)^(N/(Delta+1))`.

The probability that `|T|>=3` is `1-A_N*(2/3)^N`, and every such set
must be served by at least one comparison graph. The union bound now proves
the stated width bound. Applying the same union bound to distinct graphs proves the
stronger graph-count statement.

The choice one third optimizes this product bound: for selection probability
`p`, the guaranteed average isolation probability is `p*(1-p)^2`, and
`p*(1-p)^2` is largest at `p=1/3`.

## General bounded-degree graphs

For an arbitrary graph of maximum degree `Delta`, its square has maximum
degree at most `Delta^2`, hence a greedy coloring uses `Delta^2+1` colors.
Also `p_v >= (2/3)^Delta/3` at every vertex. A largest color class has at
least `N/(Delta^2+1)` vertices. Bound its product of `1-p_v` factor by
factor and repeat the same probability and coverage argument. This proves
the graph version.

## Why this does not settle all trees

The exponential rate depends on the maximum degree. For a star, all subsets
containing its center are connected, so a single graph can serve roughly
half of all ties under uniform subset counting in this necessary locality test. The family of stars with
every possible center serves every nonempty tie. Therefore this graph-only
coverage condition cannot yield an unrestricted all-tree exponential bound;
that target needs additional information about the heads, coefficients, or
cancellation across ties.
