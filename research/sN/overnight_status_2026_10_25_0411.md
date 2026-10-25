# Overnight proof-search checkpoint, 25 October 2026, 04:11 UTC

The search is active. The unrestricted canonical all-tree exponential lower
bound and the uniform exact construction of size 2^{O(N)} remain open.
The paper's upper bound remains 2^{O(N log N)}. Unmatched small-input
results remain in research files, following the user's instruction.

## What is proved and matched at five inputs

The minimum first hidden layer width is nine, allowing arbitrary real
weights and biases, no skips, and any finite second hidden layer. A globally
verified rational (9,14) network attains nine. This does not assert that
fourteen is optimal. For the prescribed ten-row first hidden layer, the
minimum second hidden layer width is exactly six. Both matched statements
are already in the 46-page paper, which builds cleanly.

For the specific nine-row P4 first hidden layer, the new independently
verified lower bound is h2>=7, while its construction has h2=14. Its exact
certificate excludes four free outer units over the seven invariant
features, with arbitrary real coefficients. It stays outside the paper.
See `best5/overnight_fixed_p4_k4_manifest.json` and
`best5/overnight_root_p4_k4_fresh.json`, committed in `493584b`.

The remaining possible row-sum splits at first width nine are (1,1,7) and
(2,2,5). Current searches cover both: arbitrary five-core P4 constructions,
and a new directed-cycle feature map in the second split. For the cycle,
26 of 32 orientations have exact noninjectivity witnesses; six survive.
Four invariant outer units would compile to (9,6), but no such exact fit
has been found. Necessary systems alone are not accepted as constructions:
every candidate passes through the complete rational chamber verifier.

## Unrestricted canonical trees: the nine-label certificate is complete

For every N>=9, an expansion in canonical tree face functions and a shallow
auxiliary span needs at least

    binom(N,5)/126

terms whose original tree has matching number at least four. All shapes,
roots, apices, orientations, and face states are included. Canonical trees
with matching number at most three may be added for free. This is a
polynomial bound, and arbitrary real head vectors or edge lengths are not
included in this unrestricted canonical-tree statement.

The nine-label certificate proves rational rank at most 1970 for all 3822
canonical no-perfect-matching function orbits, and augmented rank at least
1971. All 1971 rows passed two independent exact arithmetic engines. The
separate streaming root verifier replayed all 3,650,292 rational relation
checks and the modular determinant reductions. Domain and DAG checks
cover all 262144 labeled eight-vertex trees and every required root and
orientation. Sources and reproduction instructions are in
`trees/overnight_lower_exact9_manifest.json`,
`trees/overnight_lower_exact9_README.md`, and
`trees/overnight_lower_nine_bridge.md`. Commit `6879364` is pushed.

The complete certificate also propagates by coordinate deletion. Thus all
previous exponential bounds for mixtures of the two original dictionaries
with weighted bounded-degree or bounded-excess graph families retain
their rates after adjoining every canonical matching-number-three tree
for free. For the explicit matching-mixture bound, the sufficient arity
threshold is now N>=36. See `trees/overnight_free_matching3.md`.

## Uniform lower-bound route

It would suffice to separate the maximum from units with two nonroot
outward leaves sharing a hub, at every sufficiently large odd arity.
The complete counting reduction gives Omega((2/phi)^N), with no polynomial
loss, under that still-unproved analytic hypothesis. Its Fibonacci dynamic
program and actual face controls are independently replayed; see
`trees/overnight_uniform_twin_dp.md`. This is a conditional theorem.

A faithful multiplicative deformation of all canonical Fourier kernels
is now proved. It respects all rational relations, including mixed apex
placements, through a common half-open cone construction. Its exact
formula and proof are in `trees/overnight_uniform_multiplicative.md`,
commit `20f8874`. This is structural progress, not a separator.

Several canonical scalar residues and quadratic torsion traces fail
already on the outward star. The complete two-character matching rule
shows exactly where wrong-apex contributions persist. Independent exact
checks and negative results are retained, rather than reusing those
functionals with larger fitted coefficient lists.

The current lower route uses double residues at two leaf-wheel poles.
Only three possible apex labels contribute, and the local denominator
arrangement has rank two. The residue map is injective on the complete
symmetric five-label outward-twin function span. A uniform injectivity
proof is missing; attachment-dependent frequency shifts must be retained.

## Uniform construction route

The actual ordered simplex filling now uses a single coface after a
canonical contraction. There is an explicit local root-transfer identity,
but repeated support growth is not yet exponentially bounded. Complete
exact obstructions exclude the specific noncrossing and two-page auxiliary
recurrences, and a fixed two-root-factor correction ansatz. They do not
exclude the requested construction.

The current actual geometric candidate groups permutation chambers by
correlated Baxter tree pairs, then adds the full apex star to each twin-tree
union. Each graph still has O(N) edges, preserving an exponential bound
on all face descriptions if the required class identity can be proved.
The sparse omitted-apex version fails by exact three-label locality, even
with arbitrary real heads and weights. The reopened apex-star family is
being evaluated by zonotope facet tilings; no identity is claimed yet.

## Verification and repository scope

The new certificates and prose arguments are independently checked but
are not new public Lean network theorems. The historical public Lean
certificate still checks 122 statements from 24 October. The paper states
the boundary between those statements and subsequent proofs.

All frozen work through `3271232` is committed and pushed to `main`.
Search artifacts in progress remain unstaged. Checkers which write runtime
receipts are replayed in temporary copies so frozen source and data hashes
remain intact. No large exact-nine campaign remains running; it finished
successfully. The three proof-search agents continue on their stated tasks.
