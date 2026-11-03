# Unit scale of a pair comparator

This utility proves the following exact representation implication. Let R
be any affine function plus a finite signed sum of ReLUs of affine forms,
and let

```
A(x) = max(x0,x1),   B(x) = max(x2,x3),
H(x) = linear(x) + bias + c ReLU(x0-x1).
```

If s>=0 and, on every real input,

```
MAX4(x) = R(x) + ReLU(s (A(x)-B(x))) + ReLU(H(x)),
```

then s=1. R has arbitrary real first biases and coefficients. H has an
arbitrary affine head and arbitrary real coefficient c, including zero.
The first comparison in H has exactly the displayed direction. Its
opposite orientation can be absorbed into the affine head via the usual
ReLU identity, but the theorem does not silently assume such a reduction.

The proof is local at q=-e1, where coordinates 0,2,3 tie at the top.
The comparison x0-x1 equals one there, so H is locally affine.
Consequently ReLU(H) has a locally linear odd part even when H(q)=0.
The same local odd-linearity property holds for R and B. The pair identity

```
ReLU(s(A-B)) = s(MAX4-B)
```

therefore implies that (1-s)MAX4 has a locally linear odd part at q.
The three-way-top-tie obstruction forces 1-s=0. The proof retains the
outer ReLU of H throughout; it makes no global shallow-function claim
about that outer fold.

`UnitComparator.lean` contains `unit_comparator_scale` and the general
helper `scalar_eq_zero_of_locOddLin_max`. `Statements.lean` checks both
exact types, gives a literal finite-array/max consumer, and verifies a
concrete representation at s=1 to establish nonvacuity.

Run from the repository root:

```
python3 research/sN/max5_optimal_20261103/lower/unit_scale/verify.py --replay
```

The source-bound receipt records the targeted dependency build, fresh
leaf and exact-type consumer compiles, local import closure hashes, and
transitive axioms. The permitted axioms are `propext`, `Classical.choice`,
and `Quot.sound`. Frozen earlier research sources and receipts are not
modified. This is a utility for a specified representation; applying it
to an arithmetic support case still requires the corresponding geometric
reduction. No complete support classification or width optimum is claimed.
