# Independent semantic audit of the degree-two lower bound

This audit concerns the exact original-network declarations in
`NormalizedBound.lean` and `RawBound.lean`. The claimed result is restricted
to braid first covectors and second-neuron interaction graphs of maximum
degree two. It is **unconditional within that class**: it assumes neither a
matching obstruction nor a conjecture about MAX. There is no assumption on
the first hidden width.

## Statement checked

For every exact real nine-array affine-skip network representing MAX_N,
assume that every original first covector has coordinate sum zero and support
size at most two. For each original second neuron, sum all parallel first-row
contributions with their signed second weights; keep an edge precisely when
that sum is nonzero. Suppose each such graph has maximum degree two. Then,
for every integer m >= 3,

    choose(N,m) <= h2 * (2N + 2(m-1)N^2).

In particular, for N >= 6,

    h2 >= 2^N / [N^3(N+1)].

The exact binomial bound is sharper than the final elementary denominator.
Original first and second biases, input-to-second linear heads, first-to-output
skips, output bias, and coefficient signs are unrestricted. The graph is not
the union of raw first-row supports: cancellation is part of its definition.

## Proof chain inspected independently

1. If a neuron's graph has at least three components, choose two component
   indicators and one unused component. A nontrivial linear combination of
   the first two annihilates its corrected linear head while remaining
   non-diagonal. Every retained comparison is constant along that direction.
   This proves a period of the actual neuron, including exact cancellation
   among parallel first rows.
2. The finite-difference obstruction applies to the sum of those actual
   neurons. Every first-hidden output term also has a non-diagonal period
   when N >= 3, and zero-output second neurons are handled explicitly. The
   conclusion identifies an original second index with nonzero output
   coefficient, not an extra neuron introduced by a normal form.
3. For every selected set of at least three labels, existing proved generic
   localization produces the actual local MAX identity. Its graph is the
   exact comap of the original signed graph. The complement may be empty;
   no positive tail-size hypothesis is present. Relabeling to the selected
   subtype preserves the literal number of components, including isolates.
4. A finite connected induced subset of a degree-two graph has a spanning
   simple path. At fixed size at least two, a chosen first directed edge
   determines that path, because there is at most one continuation that
   does not backtrack. Thus there are at most 2N such subsets. Singleton
   sets are handled separately. Cycles and disconnected ambient graphs
   are included.
5. A subset with at most two components is either connected or the disjoint
   union of two nonempty connected subsets. The two orders of its components
   give two distinct preimages; the counting proof retains this factor of
   two. A union bound over original second-neuron indices then counts every
   selected set. No independence or disjointness between different neurons'
   coverage sets is assumed.
6. Bias removal is by the proved homogeneous recession identity, retaining
   every original A, U, W, L, B and d array and both original hidden widths.
   Outer translation normalization either keeps a whole W-row or zeros that
   whole row. It cannot unmask a canceled edge by deleting only one biased
   first row. The original degree bound therefore descends to the normalized
   graph.
7. The final exponential inequality uses only the elementary central-binomial
   estimate 2^N <= (N+1) choose(N,floor(N/2)) and the proved capacity bound.

No mathematical gap was found in these steps. The independent Lean driver
`Audit.lean` expands the entire forward pass into the nine original real
arrays and rewrites the degree hypothesis as a literal finite neighbor count.
Its proof cannot assume graph coverage or the desired lower bound through a
named model predicate. `AuditControl.lean` checks that the explicit MAX_4
model with two first units and one second unit has exactly the two disjoint
comparison edges and maximum degree one.

## Scope and evidence boundaries

This result does not give an unrestricted exponential lower bound when a
second neuron may have a high-degree interaction graph, such as a star. It
does not cover arbitrary non-braid first covectors under a mere width cap.
The audit does not add a new all-arity existence construction. The literal
four-input control establishes nonvacuity of the actual graph and network
assumptions; the repository's caterpillar construction is a separate source
for the broader representability question.

Lean compilation and transitive axiom output must be read from the final
content-bound receipt. This prose audit alone is not a kernel verification
receipt. The accepted axioms are only `propext`, `Classical.choice`, and
`Quot.sound`.
