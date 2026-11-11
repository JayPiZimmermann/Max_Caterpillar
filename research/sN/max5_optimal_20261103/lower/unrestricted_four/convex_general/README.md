# Linear lower bound for convex or concave residual cores

The Lean declarations prove the following statement. If an exact MAX_N
identity has a finite affine shallow remainder and K outer ReLU terms,
and every preactivation of an outer term is itself finite affine shallow
and globally convex or globally concave, then **K >= N-2**. All affine
biases, arbitrary real outer weights, and separate finite first-layer
dictionaries are allowed. Each core may choose its own curvature sign.

The additional curvature assumption is essential to the stated theorem.
This does not establish an unrestricted numerical width improvement for
MAX5, nor identify K with the physical second hidden width of a network
whose translation-tail reductions have not been proved.

## Formal statements

* `Bound.lean`, `ConvexRepresentation.bound`: convex cores, arbitrary
  finite core-index type. `convex_core_lower_bound` exposes the same
  conclusion directly in terms of functions.
* `Shape.lean`, `shape_bound`: each core may be convex or concave.
* `Shape.lean`, `raw_shape_bound`: the literal finite-array formulation,
  including all first biases and affine heads and a separate dictionary
  for each core.
* `Shape.lean`, `max5_two_core_impossible`: MAX5 cannot have two such
  residual cores. Any two-core MAX5 representation therefore needs at
  least one core that is neither convex nor concave.
* `Nonvacuity.lean`: one convex core and a linear remainder compute MAX3,
  attaining K=N-2. This is an actual all-input representation.

`Model.lean` defines finite affine shallow functions by finite affine
combinations of affine ReLUs and proves the raw-array bridge. There is no
lower-bound assertion hidden in that definition or in the representation
structure. `ShapeCheck.lean` checks the fully expanded array statement;
`Check.lean` imports it together with the local-model checks and witness.

## Proof

Complement each concave core, absorbing the resulting shallow summand
into the remainder. Induct on N. At a point where N-1 coordinates tie at
the maximum, a nonzero core can be absorbed into the shallow remainder
of the directional derivative. The other exact directional derivatives
remain convex shallow functions. The smaller MAX_(N-1) identity would
then have one fewer core, contradicting the induction hypothesis.

Thus, under a hypothetical K<N-2 representation, every core vanishes at
every such contact. Every real input is a convex combination of suitable
translated contact vertices M*1-s*e_i. Convexity makes each core
nonpositive everywhere, so all the outer ReLUs vanish. This would make
MAX_N shallow, contrary to its three-way-tie obstruction.

`Tangent.lean` and `ConvexTangent.lean` prove exact small-step identities
and convexity preservation. `ContactMaximum.lean` proves the actual
smaller MAX target identity, `Localize.lean` removes a chosen nonzero
core, and `Simplex.lean` proves the explicit convex-combination step.
The argument handles affine biases directly and needs no recession
reduction or genericity assumption.

## Reproducible verification

The fresh closure verification passed: **95 repository-local Lean files**
were rebuilt in a new private artifact library, with **290 source and
evidence hashes** and **37 recorded axiom audits**. Every audited theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`. The complete
build inventory and hashes are in `receipt.json`.

Run from the repository root:

```sh
python3 research/sN/overnight_20261103/lean_pool.py python3 research/sN/max5_optimal_20261103/lower/unrestricted_four/convex_general/recheck.py
```

The verifier rebuilds every repository-local import of `Check.lean` in a
new private artifact directory. It reuses the pinned external Lean and
Mathlib libraries, records every build result, audits printed axioms,
scans Lean source for forbidden constructs, and rejects source changes
during the run. `--hash-only` checks the resulting source/evidence hashes.

The separate `Physical*.lean` and `TailGeometry.lean` work is outside this
residual-bound receipt. The unused `Max3Control.lean` draft is also outside
the import closure and is not part of this theorem or its evidence.
