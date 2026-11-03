# The existing ordinary MAX5 (9,11) construction in Lean

This folder formalizes the previously independently certified rational network
`research/sN/frontier5/max5_code_atomic_70836_11.json`. It does not claim a new
width improvement or optimality of the second width eleven.

The intended public statement is `MaxCaterpillar.Max5Optimal.NineEleven.exists_network`:
there exists an ordinary two-hidden-layer ReLU network of widths `(9,11)`
which computes MAX5 on every real input, has rational weights, and has zero
biases. The ambient `Network` architecture permits arbitrary biases and has
no skip connections. Zero biases are a property of this particular witness.

## Proof and physical model

The seven invariant first-layer functions are the positive parts of

    x0-x3, x1-x0, x1-x2, x1-x4, x2-x3, x3-x0, x4-x0.

The remaining two are `ReLU(x0)` and `ReLU(-x0)`. The first two second-layer
neurons carry the signed head `max(x2,x3)`; the other nine implement the
correction identity. Every carrier neuron is counted.

`Weights.lean` contains the literal rational matrices. `Evaluation.lean`
connects their ordinary forward evaluation to the nine-correction formula.
`Identity.lean` proves that formula by an insertion-sort cover of all 120
closed braid chambers, refined into 169 closed cells. The eight `Cells*.lean`
modules prove every cell using rational arithmetic and explicit nonnegative
linear combinations of the cell inequalities. The coverage tree uses only
`le_total`, so ties and other boundary cases are included.

`Physical.lean` combines the two statements. `Check.lean` restates the result
using six literal parameter arrays and includes a positive evaluation control
and a deliberate gate-deletion control at `(1,0,0,0,0)`.

## Reproduction and trust boundary

From the repository root:

```sh
python3 research/sN/max5_optimal_20261103/construction/nine_eleven/generate.py
python3 research/sN/max5_optimal_20261103/construction/nine_eleven/build.py
python3 research/sN/max5_optimal_20261103/construction/nine_eleven/receipt.py
```

The generator reuses `scripts/smalln/gen_lean.py` through a local subclass,
redirecting complete module identifiers and omitting its generic wider
first-layer compiler. An explicit ring conversion handles reverse-oriented
coordinate differences. All generated declarations are checked by Lean;
the generator and its geometric calculations are outside the trusted base.
There are no admitted propositions or external computation axioms. The
accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The build commands run under the repository's bounded Lean pool and write
owned artifacts only. `receipt.json`, once present with status `PASS`, records
the exact target checks, generator/input provenance, and hashes of the
transitive project-source closure. The claim remains an isolated research
theorem until included in a published checkpoint; production roots are
unchanged.
