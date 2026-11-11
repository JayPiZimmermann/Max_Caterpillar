# Bounded checkpoint: convex-core lower bounds and contact-data limits

This checkpoint publishes three independent Lean results with their
literal-type consumers, pinned local import closures, recorded logs, and
standard-axiom receipts. It excludes the ongoing physical-width
formalization and all other unfinished MAX5 search branches.

## Headline result

For finite affine shallow functions with arbitrary biases, real first
directions and signed outer coefficients,

    MAX_N = R + sum_j d_j ReLU(g_j),

if each core `g_j` is globally convex or globally concave, the number K of
folded cores satisfies `N <= K+2`. In particular, MAX5 cannot have two such
cores. The first dictionaries need not be shared or have bounded width.

The Lean entry points are in
`../lower/unrestricted_four/convex_general/Shape.lean`:
`shape_bound`, `raw_shape_bound`, and `max5_two_core_impossible`.
`ShapeCheck.lean` and `Check.lean` check literal raw-array and function
types. The proof contains the actual local reduction, convex directional
derivatives, a smaller MAX representation, the strict decrease in core
count, and the translated-simplex argument. A MAX3 example with one convex
core checks that the hypotheses admit a real boundary case.

The selected `convex_general/receipt.json` records a fresh build of every
repository-local import in a private artifact library. All recorded
headline axioms belong to `propext`, `Classical.choice`, and `Quot.sound`.
The proof's short mathematical exposition is
`../lower/unrestricted_four/CONVEX_CORE_LINEAR_BOUND.md`.

## Two smaller verified results

`InvisibleShallow.lean` and `InvisibleShallowCheck.lean` give an actual
five-neuron shallow function with full-support, zero-sum first normals.
It is nonzero, even, and invariant under common translation. Nevertheless
it vanishes on every real triple-contact cone and on open neighborhoods
of all five four-way contacts. Thus those contact data and local germs
cannot reconstruct a general shallow core. The function is not a MAX5
network, and five is not asserted to be the minimum number of features.

`PairContactDual.lean` and its check classify finite zero-sum vector pairs
whose nonnegative two-coordinate combinations never have both components
negative: one vector is zero, or they are strictly negatively
proportional. This is a finite algebra lemma, with no network-width
conclusion hidden in its statement.

## Mathematical corollary not yet included as a Lean theorem

`CONVEX_PHYSICAL_WIDTH.md` and its independent audit prove that an ordinary
exact MAX_N network needs `h2 >= N` if every actual second preactivation
is globally convex or globally concave. This retains arbitrary biases and
first hidden width, and excludes skips. In MAX5, a physical width-four
candidate must therefore have a core that is neither convex nor concave.
The physical-wrapper Lean sources are deliberately outside this checkpoint.

This is a structural restriction on a declared curvature class. The
unrestricted ordinary MAX5 bounds remain `4 <= h2 <= 6`; neither optimal
widths nor an unrestricted second-width-five lower bound are claimed.

## Manifest and read-only verification

`manifest.json` contains SHA256 hashes of every selected source and evidence
file. `paths.json` is the exact file list for a bounded publication. The
manifest and path-list files omit their own hashes to avoid circularity;
the verifier and this scope note are hashed. The baseline is the previously
published checkpoint `a716b42`.

From the repository root, audit the frozen sources, receipt dependencies,
local import closure, forbidden proof constructs, and recorded axioms:

```sh
python3 research/sN/max5_optimal_20261103/publication_20261103/verify.py
```

To rebuild all three proof closures without changing any repository file:

```sh
python3 research/sN/max5_optimal_20261103/publication_20261103/verify.py --replay
```

Replay uses a fresh temporary artifact library, removes cached project
artifacts from `LEAN_PATH`, and reuses only the pinned external Lean/Lake
packages. It checks all hashes again after the run. The selected older
producer scripts are retained as provenance; unlike this checkpoint's
verifier, those producer scripts regenerate their own logs and receipts.
