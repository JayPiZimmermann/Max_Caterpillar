# Actual shallow-network segment obstruction

`SegmentNetwork.lean` is Lean verified. It bridges the scalar segment
argument to literal finite ReLU sums, rather than assuming a decoder or
an abstract curve representation.

For an exact identity `MAX5 = R + ReLU(g) + ReLU(h)`, the remainder may be
an arbitrary affine shallow network, including biases. The two cores are
homogeneous shallow sums over a common actual first dictionary. Assume
both cores vanish at `-e3,-e4`. Apart from one distinguished physical row,
every row either omits coordinate3, omits coordinate4, or has entries3,4
that sum to zero. The signed sum of the balanced rows' midpoint hinge
coefficients is one in each core. Then the distinguished row also has
entries3,4 summing to zero.

The statement retains arbitrary first-row orientations, repeated or
opposite rows, zero coefficients, signed cancellations, and balanced
nonroot rows. The conclusion is coordinate balance, not a claim that the
row is a comparison direction or that its other entries vanish.

`no_three_coordinate_exception` additionally excludes a distinguished
row supported on `{r,3,4}` with zero coordinate sum and a nonzero entry
at `r`, where `r` differs from3,4. Nonzero entries at3,4 are not required.
This gives the actual-array obstruction needed for supports034,134,234.

The upstream reduction from an ordinary biased network to this normalized
two-core sector and the finite support-class cover are separate
dependencies. These files do not claim the complete Max5(9,4) exclusion.

Reproduce the bounded checks with:

```sh
python3 research/sN/max5_optimal_20261103/lower/segment_network/verify.py --replay
```

The replay rebuilds the relevant dependencies and checks a literal
array-and-max consumer, the expected theorem type, and transitive axioms.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The receipt binds
81 local Lean source files and the project controls. It is a targeted
workspace receipt, not a full clean public-project verification.
