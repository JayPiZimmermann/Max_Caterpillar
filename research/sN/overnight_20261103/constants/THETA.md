# More isolated comparisons improve the unconditional quadratic constant

The isolated Lean theorem `Theta.affine_quadratic` proves h₂≥N²/175000 for
every N≥3 and every exact affine-skip ReLU network with total h₁≤N².
All real weights, biases, and input/hidden/output skip parameters are free.
There is no unproved structural premise.

The proof keeps at least7K/10 isolated low-rank gaps instead of K/2. The
actual finite-permutation variance proof bounds the failure probability by
1250/m when K≥50 and K≤m/10, hence by1/16 for m≥20000. Consequently the
actual matching Laplace rate improves from7K/(24m(m−1)) to49K/(120m(m−1)).
The event cover, clean recording-fiber bound, selected matching count, and
original-neuron indexing are all re-proved for the strengthened rank event.

The joint half restriction supplies, on one actual model with the same
hidden widths, 16L≤105h₁ and8M≤h₁. Here L is the fourth falling support
moment and M counts first-hidden rows with support at least three.
For h₁≤N² and retained arity m+5, these imply L≤27m² and M≤m².

Choose K=floor(m/10). Coverage is at least5/8, and each original second-hidden
neuron costs at most261/K². The floor comparison m²≤101K² yields
h₂≥m²/42200. Since N²≤4.1m², the rounded bound N²/175000 follows. The
existing linear bound handles N≤50000; all larger N have m≥20000, so there
is no uncovered finite-arity interval.

The actual five-input obstruction H(5,2) is an imported proved theorem.
The full raw theorem and independent literal-nine-array controls are in
`ThetaQuadratic.lean` and `ThetaCheck.lean`. The latter also checks the actual
joint restriction, the literal stronger rank event, and actual caterpillar
witnesses at N=3 and N=50001. The reproducible source-bound gate is
`python3 research/sN/overnight_20261103/constants/theta_recheck.py --run`.

This is an isolated research checkpoint. Earlier N²/650000 and N²/300000
checkpoints and their receipts remain unchanged.
