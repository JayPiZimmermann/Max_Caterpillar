# The matching bound also permits one cycle per component

25 October 2026. This extends every matching-witness bound in
`overnight_weighted_matching.md` from forests to **pseudoforests**: simple
graphs whose connected components contain at most one cycle. All heads,
inner coefficients, output coefficients, and biases retain the arbitrary
real scope of that note. The argument was independently reviewed; it is
not Lean verified.

## Why the same component witnesses work

Give the graph an auxiliary orientation with indegree at most one. In a
tree component, orient edges away from a root. In a unicyclic component,
orient its cycle cyclically and every attached tree away from the cycle.
This bookkeeping orientation need not agree with any ReLU orientation.

A connected induced subgraph inherits indegree at most one. Its number
of vertices of indegree zero is exactly `|V|-|E|`, hence at most one.
For a fixed matching, each event that the parent endpoint is unselected
and its child is selected supplies such a vertex. Different matching
witnesses therefore lie in different components. Selected original
isolated vertices give additional independent witnesses.

All probability and covering arguments in `overnight_weighted_matching.md`
now apply unchanged. In particular, if every graph has matching number
`nu` and isolation count `z` with `nu+z>=k`, then

`|K| >= [1-(1+N+binom(N,2))2^(-N)] (4/3)^k`
`       / [1+k/3+binom(k,2)/9]`.

The same bound counts distinct comparison graphs. If every added graph
in a mixture with the paper's caterpillar/rooted-star face dictionary
has matching number at least `k`, then the mixture still needs at least
`(169/147)^k/(N+1)^2` terms. The free canonical-star and bounded-canonical-
matching extensions retain the respective polynomial factors stated in
the earlier note.

## The degree corollary does not need a forest vertex-cover theorem

For every simple graph of maximum degree `Delta`,

`nu+z >= ceil(N/(Delta+1))`.

For `Delta>=2`, fix a maximum matching. Its unmatched vertices are
independent, and every nonisolated unmatched vertex is adjacent to a
matched endpoint. For a matched edge `uv`, let `A,B` be the unmatched
neighbors of `u,v`. If both sets are nonempty, they must be the same
singleton: distinct choices `a in A,b in B` would give the augmenting
path `a-u-v-b`. Otherwise their union has size at most `Delta-1` because
one endpoint already uses its matching edge. Thus every matched edge
has at most `Delta-1` distinct unmatched neighbors, and

`N-z-2nu <= (Delta-1)nu`.

This proves the claim; degrees zero and one are immediate. Consequently
the stronger bounded-degree rate

`Omega_Delta((4/3)^(N/(Delta+1))/N^2)`

holds for pseudoforests too. Graphs with several independent cycles in a
single component need a different component argument; the general
bounded-degree graph bound in `overnight_bounded_degree.md` still applies
to them. No unrestricted all-tree exponential theorem follows, because
the matching number can grow sublinearly while the degree grows.

`overnight_pseudoforest_matching_check.py` independently enumerates all
small labelled pseudoforests, constructs the auxiliary orientations by
leaf peeling and cycle traversal, and checks component witnesses against
direct connectivity. It also checks both exact probability bounds used
in the proof. These finite checks validate the implementation, not the
uniform theorem by sampling.
