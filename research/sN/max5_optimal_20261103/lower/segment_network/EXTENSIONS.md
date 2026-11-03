# Nonzero curvature and arbitrary contact pairs

`SegmentNetworkGeneral.lean` retains the actual exact network identity and
allows the two aggregate midpoint curvatures to be any nonzero real
numbers, including opposite signs. The proof divides each scalar core
curve by its own curvature only to examine its zero set. It does not
assert that the network with those divided cores still represents MAX5.

The guarded theorem `balance_or_zero_midpoint_mass` explicitly retains
both zero-curvature boundary cases. `SegmentNetworkPairs.lean` proves
the coordinate-permutation bridge and exports `balance_or_zero_pair_mass`
for every distinct pair of contact labels. The guarded conclusion is:

    first aggregate curvature = 0, or
    second aggregate curvature = 0, or
    the exceptional row's two selected entries sum to zero.

All hypotheses are on actual finite ReLU sums and literal row arrays.
The same shallow remainder, endpoint zeros, signed sums, repeated rows,
and physical-row scope as the unit theorem are retained. Exact type and
literal array consumers are in `GeneralStatements.lean` and
`PairStatements.lean`.

Replay without changing the earlier unit receipt:

```sh
python3 research/sN/max5_optimal_20261103/lower/segment_network/verify_general.py --replay
python3 research/sN/max5_optimal_20261103/lower/segment_network/verify_pairs.py --replay
```

`NoCross.lean` separately excludes two nonzero aggregate midpoint
curvatures when every row is affine or balanced on the segment. It
supplies the actual-array bridge for the zero-crossing support sector.
Its receipt and consumer are separate from both replay commands above.
