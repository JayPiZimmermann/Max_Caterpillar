# An unconditional exponential bound for degree-two interaction graphs

The complete mathematical implication is now Lean checked in
`SharpBound.lean`. Its independent expanded contract and source-bound rebuild
are recorded separately by the final verification receipt. This is a
restricted graph-class theorem, not an exponential lower bound for arbitrary
two-hidden-layer MAX networks.

Let an actual network compute MAX_N on every real input. The first hidden
covectors are arbitrary real scalar multiples of coordinate differences, or
zero. First and second biases, linear heads, first-hidden-to-output skips,
the output affine term, and all coefficient signs are unrestricted. For
each original second-hidden neuron, sum the signed coefficients of all
parallel first-hidden comparisons before forming its interaction graph.
Assume each resulting graph has maximum degree at most two.

There is **no upper bound on the first hidden width**. For every m >= 3,

    2 choose(N,m) <= h2 * (2N + (m-1)N^2).

Consequently, for N >= 6,

    h2 >= 4 * 2^N / [N^3(N+1)].

The exact binomial statement is sharper than the displayed exponential
corollary. The maximum-degree hypothesis includes arbitrary disjoint unions
of paths, cycles, and isolated vertices, without a prescribed ordering or
acyclicity assumption. A raw support union would be a stronger condition;
the theorem uses the actual signed aggregate and permits cancellation.

## Proof

For every selected set T of m inputs, localize at a point where exactly
those inputs tie for the maximum. The existing exact localization machinery
produces an actual MAX_m model with the original neuron indices. Its
interaction graph is the induced graph on T, with the original signed
parallel-row sums.

If one of these induced graphs has c components, a vector constant on
each component leaves all comparison terms invariant. With c >= 3, imposing
the one remaining linear-head equation still leaves a non-diagonal period.
If every second unit had such a period, the localized MAX would be a finite
sum of periodic functions plus an affine remainder. The newly proved
finite-difference obstruction excludes that identity. Therefore every T
has an original active second neuron with at most two induced components.

A connected k-set in a degree-two graph has a spanning simple path. Its
chosen first directed edge and k determine the whole path, because there is
at most one continuation after each incoming edge. There are at most 2N
directed edges. Each connected subset supplies two distinct darts by
reversing its spanning path, so its sharper count is N; singletons also
satisfy that bound. A set with two
components is an unordered pair of connected sets. Thus one original graph
can cover at most N + (m-1)N^2/2 selected m-sets. Summing these capacities
proves the binomial inequality. Summing all binomial coefficients and using
the central coefficient as their maximum gives the explicit exponential
corollary.

Arbitrary biases are removed by a proved recession identity retaining every
original weight and covector. This is essential: deleting individually
biased rows could destroy parallel-row cancellations. Subsequent outer
normalization only retains or zeros whole second-neuron weight rows, so its
interaction graphs are subgraphs of the original graphs.

## Lean map and scope

* `GlobalComponents.lean`: the actual component-constant period obstruction.
* `ActualTie.lean`: every selected set has an original active witness;
  the full selected set and an empty complement are included.
* `GraphConnected.lean`, `GraphBound.lean`: actual degree-two graph capacity.
* `CoverCounting.lean`: finite union counting over the original second indices.
* `NormalizedBound.lean`: the complete normalized-network theorem.
* `Recession.lean`, `RecessionGraph.lean`: exact raw-array bias and graph bridges.
* `RawBound.lean`: `raw_width_binomial`, `raw_width_exponential`, and
  `raw_width_exponential_real`, with unrestricted first hidden width;
  these preserve the original coarse count as compatibility statements.
* `GraphSharp.lean`, `GraphSharpCover.lean`, `SharpBound.lean`: the sharper
  two-dart count and raw bound `raw_width_exponential_sharp_real`.
* `ActualTieFeeding.lean`, `normalized_width_binomial_sharp_feeding`: the
  normalized theorem only needs braid support on feeding first rows.
  Its translation-normalization assumption still applies to all first rows.

The basic degree-two mathematical route was already recorded in
`research/sN/trees/overnight_degree_two.md` on 25 October. This development
supplies its actual-network Lean proof using the elementary finite-difference
obstruction, explicit graph counting, and signed-cancellation-preserving
bias removal. It is not presented as a newly discovered unrestricted result.

The remaining general-case difficulty is substantial: a high-degree graph,
such as a star, can contain exponentially many connected induced subsets.
The degree-two counting estimate does not apply to those graphs. No local
matching conjecture is assumed in the theorem above, and no conclusion about
that conjecture follows from this scoped result alone.

The current concrete nonvacuity control is the exact four-input network at
widths (2,1), with two disjoint comparison edges. An exact degree-two MAX_N
construction for N >= 6 has not yet been established by this development.
Existing caterpillar constructions may have higher-degree attachments, and
the known six-input hexagon formulas contain degree-three terms. Thus the
bound is not a claim that exponential width is sufficient in this graph
class, or that its feasible widths have been classified.
