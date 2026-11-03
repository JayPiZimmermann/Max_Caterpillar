# Verified checkpoint: polynomial bounds and the remaining obstruction

This checkpoint records exact Lean theorems with source-bound receipts.
All network claims concern exact MAX_N on every real input. Arbitrary real
weights, biases, and affine skips are permitted unless a graph restriction
is explicitly stated. New modules are isolated research declarations, with
independent exact-type checks, rather than additions to the frozen production
root.

## Best unrestricted quadratic constant in this checkpoint

For every real C>=1 and every N>=3,

    h1' <= C N²  implies  h2 >= N² / (175,000 C).

Here h1' counts original first-hidden neurons having at least one nonzero
connection to the second hidden layer. Output-only first neurons are free.
The total-width hypothesis h1<=CN² is therefore sufficient as well. For any
0<C<1, use the C=1 specialization, or write max(1,C) in the denominator.
The lower-bound constant depends on C; the result does not require C=1.

The uncapped version is

    h2 >= min(N², N⁴/h1') / 175,000.

The displayed division form is intended for positive feeding width. The
formal file uses Lean's totalized division and also exposes the scaled
quadratic theorem directly.

* [Original feeding-width theorem](constants/tradeoff_theta/FeedingScaled.lean)
* [Uncapped feeding-width theorem](constants/tradeoff_theta/FeedingMin.lean)
* [Total-width version](constants/tradeoff_theta/Min.lean)
* [Exact-type, nonvacuity, and axiom receipt](constants/tradeoff_theta/feeding_min_receipt.json)

At C=1, this improves the previous published N²/10,000,000 constant by
about 57.1 times. Relative to the previous feeding tradeoff with denominator
40,000,000, the denominator improves by about 228.6 times, and the range now
starts at N=3 rather than N=1040. This is a constant improvement; the general
unconditional exponent remains two. No unrestricted cubic bound or
unconditional exponential bound is claimed.

## Ways to weaken the first-width assumption

The uncapped tradeoff already permits arbitrary h1'. For example,
h1'<=C N^(2+epsilon) gives an unconditional bound of order
N^(2-epsilon)/C, alongside the existing linear bound.

A separate structural alternative is verified in
[the support-transversal theorem](portfolio/transversal/Bounds.lean).
If C is a coordinate set meeting every original non-braid first row with
zero bias and zero coordinate sum, and m=N-|C|>=3, then

    h2 >= m² / 3,000,000,

with no numerical bound on h1. The actual retained braid MAX model and the
unchanged second-layer indices are derived inside the proof. Stronger
feeding-only and support-profile variants are separate later checkpoints.

The [conditional first-width tradeoff](h1_tradeoffs/README.md) is also
verified. Its integer parameter is chosen on the scale sqrt(h1')/N rather
than proportional to the quadratic-width coefficient C. In the superquadratic
width regime its exponent has order N^(3/2)/sqrt(h1'), with an explicit large-dimension
condition and the same unproved growing structural premise H. It permits
superquadratic first width; superpolynomial growth from this estimate requires
h1'=o(N³/log²N). Output-only first neurons remain unrestricted.

## What the obstruction still says

H(k,q) says that every exact normalized braid-first-layer MAX_k network
contains an original second neuron whose summed signed interaction graph
has q disjoint edges. It allows arbitrary real coefficients, arbitrary
linear heads, and cancellation between output neurons.

The [new exact equivalence](cycle_bridge/Equivalence.lean) reduces this to
excluding actual MAX_k representations in which every interaction graph has
a vertex cover of size at most q-1, at the same arity k. The proof deletes
cycles by an exact signed identity, expands into forest subgraphs, and applies
the forest matching/cover theorem. Width may increase, so this equivalence
is used for qualitative representability, not as a width-preserving rewrite.

The known H(5,2) also has a [new unified proof](cycle_bridge/FiveViaCover.lean)
using the star certificate and generic cycle deletion, without the specialized
triangle certificate. This simplifies the mechanism, not the theorem's scope.

No new H(k,3) obstruction has been proved in this run. The remaining issue is
global compatibility of all mixed-crease cancellations for arbitrary real
parameters. Exact face catalogs and finite families help construct a
certificate, but do not discharge that obligation. It would be misleading to
describe the proof as only routine completion away.

Relative to the previous conditional square-root-exponential theorem, the
new near-exponential counting route uses the same growing H family. At a
fixed ambient N it needs larger instances of that family. The counting
improvement does not make the structural hypothesis easier. Cycle deletion
does make the search space and the equivalent cover formulation cleaner.

## An exponential result with a different explicit assumption

The [degree-two theorem](degree_two/SharpBound.lean) proves

    h2 >= 4*2^N / [N³(N+1)]  for N>=6,

when first rows are scalar coordinate differences and each original summed
signed interaction graph has maximum degree at most two. There is no h1
cap and no H premise. This graph hypothesis does not follow from h1=O(N²).
The theorem does not establish that the restricted class represents MAX_N
for every large N; the recorded nonvacuity controls and that limitation are
explicit in its receipt.

## Verification and continued work

The [checkpoint inventory](checkpoint_002/selection.json) checks 13 receipts
and 1,994 source/control/log files with zero hash drift. The earlier checkpoint
is preserved. The [35-route ledger](IDEAS.md) records the ongoing search and
its failed shortcuts. Later refinements are not included merely because a
worker reported a compiling leaf; each needs its own complete gate.
