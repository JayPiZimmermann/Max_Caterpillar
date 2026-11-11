# A larger cutoff improves the quadratic constant

`QuadraticCutoff.affine_quadratic` proves the unconditional bound

\[
h_2\ge \frac{N^2}{10000000},\qquad N\ge3,\quad h_1\le N^2.
\]

The model has arbitrary real weights, all first, second, and output biases,
and input-to-second, first-to-output, and input-to-output skips. It must
compute MAX on every real input. Here `h₁` is the **total** first hidden width.

This improves the original constant fortyfold, and improves the constant of
the newer feeding-width result fourfold when total width is quadratic. The
feeding-width tradeoff with constant `1/40000000` still permits arbitrary
numbers of output-only first neurons and remains a separate, broader result.
Neither theorem proves quadratic growth optimal or improves the exponent.

## Why the larger cutoff is allowed

The previously verified finite growing-matching transfer only requires
`4 ≤ K < m`; it does not require `K ≤ m/100`. Its local structural assumption
at `(k,q) = (5,2)` is already a theorem, supplied by the closed all-real
five-variable obstruction. Consequently this specialization is unconditional.

Normalize the original affine-skip network without changing either hidden
index type. A simultaneous actual half restriction gives a normalized MAX
network in `n = floor(N/2)` variables with

\[
4M\le h_1,\qquad 4L\le81h_1,
\]

where `M` counts all nonbraid first rows and `L` bounds their fourth descending
support moment. The new `NormalizedTotalHalf.exists_model` proves both
budgets for the same actual model, including first rows feeding only the
output.

For `N > 50000`, put `m = n−5` and choose `K = floor(m/25)`. Then
`m ≥ 20000`, `M ≤ 2m²`, `L ≤ 100m²`, and `m/26 ≤ K ≤ m/25`.
The exact bad-event bounds give

\[
\text{coverage}\ge 1-\frac8{25}-\frac{21}{125}-\frac{160}{m}
\ge\frac12.
\]

The actual per-neuron envelope, using the literal descending factorials and
the proved tail moment, is at most `1600/K²`. The exponential shift is at
most `1/10`; the elementary bound `exp(1/10) ≤ 10/9` suffices. Hence

\[
h_2\ge\frac{K^2}{3200}\ge\frac{m^2}{2163200}
\ge\frac{N^2}{10000000}.
\]

For `3 ≤ N ≤ 50000`, the existing skip-safe linear bound
`N ≤ 2h₂+2` already gives the conclusion. The small-dimension branch therefore
adds no computational certificate or exceptional hypothesis.

## Evidence

The canonical module is
`MaxCaterpillar/Frontier/RandomRestriction/QuadraticCutoff.lean`.
The independent checker expands the original nine-parameter network formula
and its total-width condition. Genuine caterpillar instances at `N = 3` and
`N = 50001` test both sides of the scalar branch without evaluating their
large second widths.

```sh
python3 research/sN/jensen_bound/quadratic_cutoff_recheck.py --run
```

The source-bound outcome is recorded in `quadratic_cutoff_receipt.json`.
It includes canonical build, exact contracts, seven transitive axiom audits,
the complete local Lean import closure, and build-control hashes.
