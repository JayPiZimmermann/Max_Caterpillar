# The physical `(10,6)` MAX₅ construction

This branch formalizes the existing sparse rational construction. It is not
a new width improvement or an optimality claim. The architecture is the
repository's ordinary `Network 5 10 6`, with two hidden ReLU layers, an
affine output, no skip connections, and zero biases.

`Network.lean` gives all three weight arrays explicitly. Its ten first-layer
preactivations are

```
x0-x1, x0-x2, x1-x2, x2-x1, x3-x1,
x1-x4, x4-x1, x3-x4, x1, -x1.
```

The six second-layer neurons include the positive and negative copies of
the signed head `x1 + ReLU(x0-x1)`. The other four implement the existing
`SmallN.Max5General4` identity. Thus “four correction neurons” means six
physical second-layer neurons here.

The proof checks the exact first- and second-layer preactivation formulas,
then invokes the already verified all-real MAX₅ identity. It does not infer
exactness from sampled inputs. `Check.lean` independently states the literal
two-matrix sum formula and the exact `Network 5 10 6` existence theorem.

Run `python3 research/sN/max5_optimal_20261103/construction/ten_six/recheck.py`
from the repository root. The checker compares the handwritten rational
arrays exactly with `research/sN/best5/netB_10_6.json`, compiles both Lean
leaves, audits their theorem axioms, and hashes the repository-owned import
closure. The separate `physical_check.json` is a fresh replay of the
independent exact rational cone checker on that same JSON witness.

The main declarations are `MaxCaterpillar.MaxFiveTenSix.net_eval` and
`MaxCaterpillar.MaxFiveTenSix.exists_network`. Publication status is recorded
in the source-bound receipt; these leaves do not modify a production root.
