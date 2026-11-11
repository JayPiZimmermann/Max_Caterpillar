# Lean verification of the invisible shallow function

`InvisibleShallow.lean` verifies the explicit five-neuron function

```
u=x0+x3+x4-2*x1-2*x2,
K=ReLU(u+x0)+ReLU(u+x3)+ReLU(u+x4)
  -2*ReLU(u+x1)-2*ReLU(u+x2).
```

The exact all-real conclusions are:

* `shallow_representation` expresses K as an actual sum of five first-layer
  ReLUs with explicit real weight vectors and output coefficients.
* `firstRow_sum` and `firstRow_full_support` check that every first normal
  has coordinate sum zero and every coordinate is nonzero.
* `translation_invariant` and `even` verify the two symmetries.
* `contact_zero` covers every `-s*e_i-t*e_j`, for arbitrary nonnegative
  real s,t, including repeated indices and zero weights.
* `shifted_contact_zero` covers every common translation of those inputs.
* `eventually_zero_at_vertex` proves zero on an actual open neighborhood
  of each `-e_i`, using the neighborhood filter on the full real input
  space. It is stronger than zero values or directional derivatives alone.
* `nonzero_witness` gives the exact value -1 at `(0,0,2,1,2)`.
* `perturbation_odd_part` and `perturbation_same_local_germ` explicitly
  verify preservation of the odd part and all five local germs after
  adding any real multiple of K to any function.

`InvisibleShallowCheck.lean` combines these conclusions in one literal
five-neuron model statement, with explicit array sums, contact inputs,
and neighborhoods. It also checks that the chosen function is nonzero.

This is a barrier to reconstructing an arbitrary core from contact data.
It is not a network computing MAX5, does not establish feasibility of a
two-core representation, and does not improve a width endpoint. The
complete mathematical interpretation is in `topology/INVISIBLE_SHALLOW.md`.

Replay from the repository root:

```sh
python3 research/sN/max5_optimal_20261103/lower/unrestricted_four/invisible_recheck.py
```

The replay builds the ordinary imported Basic target, then the new leaf
and exact-type consumer. Its receipt binds the repository-local import
closure and recorded logs. External Mathlib/Lake packages are pinned by
the toolchain and package manifest. The allowed axiom set is `propext`,
`Classical.choice`, and `Quot.sound`; this is a targeted working-tree
receipt rather than an integrated public project gate.
