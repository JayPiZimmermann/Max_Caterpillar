# H(5,2) through cycle deletion and the star theorem

This is a second proof of the already established five-input obstruction.
It gives no stronger numerical lower bound. Its contribution is to replace
the special triangle argument with the new, arbitrary-arity cycle reduction.

The exact theorem is
`localMatchingObstruction_five_two_via_cycle_deletion` in `FiveViaCover.lean`.
For every actual translation-normalized two-hidden-layer braid network
computing MAX_5 on all real inputs, an original second-hidden neuron has two
disjoint edges in its summed signed interaction graph. Heads, output skips,
and real coefficients are unrestricted within that model. Parallel first
rows may cancel; the graph uses their actual aggregate, not their union.

## Proof

1. The generic cycle-deletion theorem says that a representation whose
   second-hidden interaction graphs have matching number at most one can
   be rewritten as an actual finite representation with vertex cover at
   most one in each such graph. Width need not be preserved.
2. A graph with a cover of size at most one is a star, including the empty
   graph. The actual Boolean quadratic of each neuron therefore has the
   primitive star formula, using its empty/full normalizations.
3. The existing all-real star certificate annihilates every such neuron.
   The actual-network chamber and Boolean adapters imply that their signed
   sum plus its braid output remainder cannot compute MAX_5.

The new proof calls no triangle normal-form, triangle interleaving, or
triangle certificate theorem. Its complete project import closure also
contains no module with `Triangle` in its name. The certificate for stars
is retained, so this is not a new certificate-free proof of the star
obstruction.

## Exact checks and comparison

`FiveViaCoverCheck.lean` expands the cover hypothesis and produces an actual
real input where a cover-one network differs from MAX_5. It also expands
the matching conclusion into a two-element subset of the actual graph's
edge set with disjoint endpoints. Nonempty one-edge and empty-cover controls
check the graph conversion's boundary cases. These controls do not claim
that a cover-one MAX_5 network exists: excluding that simultaneous condition
is exactly the theorem.

The receipt records project source closure counts and byte totals for both
proofs, excluding external Mathlib/Lean/Std modules. At the initial checkpoint,
the new proof imports 1,161 project modules (17,535,691 bytes); old
`GrowingMatching.FiveInstance` imports 1,157 (17,503,495 bytes). Fourteen old
modules totaling 49,001 bytes disappear, including all twelve triangle
modules; eighteen modules totaling 81,197 bytes are added. Thus the new
route replaces specialized triangle machinery with a reusable general
reduction; it does **not** reduce the total file count or source size.

The largest removed triangle modules are `Triangle.lean` (8,460 bytes),
`TriangleInterleavings.lean` (6,213 bytes),
`TriangleInterleavingsStars.lean` (4,907 bytes), and
`TriangleRelabel/Fixed.lean` (4,904 bytes). The reproducible receipt is the
authority if these source sizes change.

## Reproduce

After the separate cycle-bridge core gate has rebuilt its research imports:

```sh
python3 research/sN/overnight_20261103/cycle_bridge/five_via_cover_recheck.py --run
```

This rebuilds the production star/model imports and both new leaves, checks
expanded statements and allowed axioms, scans the full project source
closure, and binds every source and control to SHA-256. It neither modifies
the original five-input proof nor the cycle-bridge core receipt.
