# The original-feeding-width version

`TradeoffTheta.Feeding.affine_min_tradeoff` in `FeedingMin.lean` states, for N≥3,

    h₂ ≥ min(N², N⁴/h₁′) / 175000,

for every exact real affine-skip network computing MAX_N on every real input.
Here h₁′ is the number of original first-hidden-layer indices j for which
some original second-hidden weight W[k,j] is nonzero. First neurons feeding
only the output do not enter this count. Both hidden index sets retain their
original meaning; the denominator is not a count after normalization.

The quadratic companion requires only h₁′≤N² and gives h₂≥N²/175000, with no
cap on output-only first neurons. All weights, biases, and affine skips are
arbitrary real numbers. There is no structural obstruction hypothesis.

`FeedingMinCheck.lean` expands all nine arrays/scalars and replaces the named
feeding-count definition by its literal subtype of original W columns. It
checks the quadratic companion and a concrete exact MAX3 network. The
minimum formula uses literal real division (x/0=0); the companion handles a
zero feeding count directly without an infinity convention.

Verification status is recorded in `feeding_min_receipt.json`; this note is
not itself a verification claim. Reproduce the exact source-bound build with:

    python3 research/sN/overnight_20261103/constants/tradeoff_theta/min_recheck.py --feeding --run

This is an isolated research result until its verified closure is published.
