# Ordinary biased networks: existential and explicit quadratic bounds

`Bounds.lean` uses the repository's canonical `Network N h₁ h₂`:

    f(x) = Σₖ aₖ ReLU(Σⱼ Wₖⱼ ReLU(Σᵢ Aⱼᵢ xᵢ + bⱼ) + θₖ) + β.

All six parameter arrays/scalars are arbitrary real numbers. There are no
skip connections. Exactness means equality to MAX_N on every real input.

For N≥3 and every C>0, the explicit theorem is

    h₁ ≤ C N²  ⇒  h₂ ≥ N² / [175000 max(1,C)].

The existential statement chooses one absolute c>0 valid simultaneously
for all N, C and all such networks, with conclusion

    h₂ ≥ c N² / max(1,C).

The fixed-C corollary gives a positive c_C with h₂≥c_C N². Both hidden
bias arrays and the output bias remain unrestricted in every statement.

## Proof status and relation to the paper

These are exact specializations of the already verified stronger affine-skip
theorem. The ordinary-to-affine embedding puts all skip arrays to zero and
preserves the original two widths. The public signatures mention only the
ordinary network. The existential Lean theorem currently follows from the
explicit theorem; it is not an independent certificate-free proof and does
not establish that the separate proposed paper simplification is complete.

The independent `Check.lean` exposes the full six-array evaluator in the
expected theorem types. Its smallest-arity control is an actual MAX_3 network
at C=1 with a first-hidden bias equal to one, obtained by adding one unused
biased first neuron to the existing caterpillar construction. This checks
that the theorem statement has not acquired an accidental zero-bias premise.

## Verification

Run:

    python3 research/sN/clean_quadratic_20261103/ordinary/recheck.py --run

This checks that the previously verified dependency receipt and every one of
its source/control files remain unchanged, then compiles the two new modules
and checks their exact exported contracts and transitive axiom sets. It
records the entire local-source import closure and the new logs. This is an
extension check over the previously verified closure, not a claim that all
old dependencies were rebuilt during this command. A fresh checkout must
first run the baseline recheck command recorded in that dependency receipt.

The first diagnostic control build failed only because a natural-to-real
cast and a literal arithmetic equality were written incorrectly. Its log is
preserved separately; the mathematical hypotheses were not changed.
