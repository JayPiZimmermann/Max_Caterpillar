# Independent ordinary-network contract review

A separate read-only reviewer checked `Bounds.lean` and `Check.lean` against
the canonical definitions and the ordinary-to-affine bridge.

Result: PASS after correcting the introductory phrase “input-to-hidden” to
“input-to-second-hidden.” The original phrase was too broad: ordinary input
connections to the first hidden layer are required and present.

The review checked:

- `Network` has exactly the six sequential parameter arrays/scalars.
- `ofOrdinary` sets all three skip arrays to zero and preserves both widths.
- Exactness is quantified over every real input.
- The positive constant is chosen before dimension, widths, scale and network
  in the uniform theorem; the fixed-scale coefficient may depend on C.
- `max(1,C)` handles the entire range C>0, including C<1.
- Literal-array contracts match the evaluator and leave both hidden biases
  and the output bias unrestricted.
- The exact MAX3 control has a nonzero bias in an unused first-hidden neuron;
  its stated scope makes that fact explicit.
- Documentation discloses reuse of the explicit theorem in the existential
  proof and makes no claim of a separate simplified structural proof.

This review is semantic inspection. The separate receipt records the actual
Lean builds, exact-type consumers, source hashes and axiom audits.
