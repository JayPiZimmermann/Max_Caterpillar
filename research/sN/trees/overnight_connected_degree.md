# Bounded-degree comparison graphs: direct connected-set counting

25 October 2026. Uniform mathematical proof, independently reviewed; not Lean
verified. This improves and shortens the bounded-degree proof in
`overnight_read_degree.md`. The arbitrary-head, arbitrary-weight, biased
network model and the shallow remainder are unchanged.

Let Delta>=3 bound the maximum degree of every simple comparison graph, and
put

    b=1/(Delta-2),
    y_*=b/(1+b)^(Delta-1)=(Delta-2)^(Delta-2)/(Delta-1)^(Delta-1),
    C=b(1+b)=(Delta-1)/(Delta-2)^2.

For every 0<y<=y_* an exact expansion of max_N satisfies

    |K| >= [(1+y)^N-1-Ny-binom(N,2)y^2] / [1+NC+(NC)^2/2].

The same bound counts distinct comparison graphs. In particular

    |K|=Omega_Delta((1+y_*)^N/N^2).

For maximum degree three this gives base5/4. The separate degree-two theorem
has the stronger base2 and remains preferable for paths and cycles.

## A short connected-set bound

Fix an order on the neighbors of each graph vertex. For each connected
vertex set S containing a chosen root v, construct its deterministic BFS
spanning tree. Encode each child by its neighbor slot, omitting the parent
slot at nonroot vertices. The root has at most Delta slots and every other
vertex at most Delta-1. The encoded tree determines all original graph
vertices by following its slots from v, so it determines S. Thus the map
from connected sets to these slot trees is injective. Slot trees whose
projection repeats a graph vertex only add harmless overcounting.

Give every tree vertex weight y. The generating sums B_h for nonempty
planted trees of bounded height obey

    B_0=0, B_(h+1)=y(1+B_h)^(Delta-1).

Since y(1+b)^(Delta-1)<=b, induction gives B_h<=b at every finite height.
The connected sets through v therefore have total weight at most

    y(1+b)^Delta <= b(1+b)=C.

Summing over roots (which may count a connected set several times) bounds
the total connected-set weight A_G(y) by NC. A set inducing two components
is an unordered pair of disjoint nonadjacent connected sets. Consequently

    sum_(T: c(G[T])<=2) y^|T|
       <= 1+A_G(y)+A_G(y)^2/2
       <= 1+NC+(NC)^2/2.

Every tied set T of size at least three requires a unit with c(G[T])<=2,
by the existing germ-rank argument. Sum its coverage inequality with weight
y^|T|. The target sum is (1+y)^N-1-Ny-binom(N,2)y^2, proving the claim.
Repeating one graph with different heads or weights does not enlarge its
coverage event, so the graph-count version follows too.

The critical value y_* merely maximizes b/(1+b)^(Delta-1). No convergence
theorem for an infinite generating series, concentration theorem, or
independence assumption about overlapping neighborhoods is needed.

## Mixtures containing both original constructions

Adjoin all arbitrary-head, arbitrary-weight comparison graphs of maximum
degree at most Delta to the caterpillar and rooted-star face dictionaries.
Choose y=min(1/6,y_*), and let Z count both original and added functions.
Then

    Z >= [(1+y)^N-1-Ny-binom(N,2)y^2]
         / [N-2 + 1+NC+(NC)^2/2].

Indeed each original function contributes at most N-2 under this weighting,
since its size-m coverage is at most6^m and6y<=1. The new functions satisfy
the connected-set bound just proved. The sum of these two per-unit bounds
is a valid common upper bound, giving the displayed inequality. The enlarged
dictionary spans because it contains the original construction.

For fixed Delta the bound is Omega_Delta((1+min(1/6,y_*))^N/N^2). In
particular **arbitrary weighted subcubic comparison graphs, with any number
of cycles, can be added to both original dictionaries while retaining the
exponential base7/6**. Heads, orientations, inner and output weights, and
biases are unrestricted within this comparison-graph model.

## Controls and remaining scope

`overnight_connected_degree_check.py` exhausts every simple graph through
six vertices and every vertex subset. It checks the root-specific and total
connected-set inequalities and the two-component count with exact integers,
both at the critical weight and at the mixture weight.

This remains a bounded-degree result. For stars and other trees with growing
maximum degree, the displayed exponential rate is not uniform. The separate
matching bound still covers pseudoforests with large matchings regardless of
degree; the unrestricted canonical all-tree exponential bound remains open.
