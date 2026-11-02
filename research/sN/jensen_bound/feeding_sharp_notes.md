# Sharper original-feeding-width constant

The new actual-network theorem is
`MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp.affine_feeding_tradeoff`:

\[
h_2\ge\frac{1}{40000000}\min\left(N^2,\frac{N^4}{h_1'}\right),\qquad N\ge1040.
\]

Here `h₁′` counts columns of the **original** first-to-second weight matrix
having a nonzero entry. All weights are real; all first and second biases,
input-to-second skips, first-to-output skips, input-to-output skips, and output
bias are allowed. Exactness is required on every real input. The direct
quadratic corollary assumes only `h₁′ ≤ N²`, so output-only first neurons may
be arbitrarily numerous.

This improves the previous full-scope constant tenfold. It changes no
geometric, certificate, matching, or probability argument. It does not improve
the exponent or prove that quadratic growth is optimal.

## Two elementary improvements

Write `n = floor(N/2)`, `m = n−5`, and let `A` be the already constructed
regularized fourth support moment, satisfying `4A ≤ 81h₁′`. Define

\[
Q=\min\left(\frac{m^2}{10000},\frac{m^4}{16A}\right).
\]

The existing actual counting theorem gives `0.42K² ≤ 400h₂` whenever
`K ≥ 4`, `K ≤ m/100`, and `16AK² ≤ m⁴`.

1. If `sqrt(Q) ≥ 100`, the integer cutoff `K = floor(sqrt(Q))` satisfies
   `K ≥ 0.99sqrt(Q)`. The count therefore implies `Q ≤ 975h₂`. For smaller
   `Q`, the existing skip-safe linear bound `N ≤ 2h₂+2`, together with
   `N ≥ 1040`, gives the same conclusion. This avoids a uniform factor-four
   loss from coarse integer rounding.
2. The exact half-arity relation `N ≤ 2n+1` and `n ≥ 520` give
   `45N ≤ 91m`, hence `N² ≤ 4.1m²`. Also `N⁴ ≤ 81m⁴`.
   Together with `4A ≤ 81h₁′`, these imply
   `min(N²,N⁴/h₁′) ≤ 41000Q`.

Finally, `41000 × 975 = 39975000 < 40000000`. The complementary regime
`1000h₁′ > N³` is again absorbed by the linear bound. The faithful affine
normalization and original-feeding lineage are reused unchanged.

The new scalar files and network wrappers are separate leaves, so the previous
verified theorem and its receipts remain unchanged. The independent checker
expands the nine-parameter network formula and the original nonzero-column
denominator. It also applies the quadratic conclusion to the actual
caterpillar construction at the boundary dimension `N = 1040`.

Reproduce the canonical build, exact contracts, closure scan, and standard
axiom checks with:

```sh
python3 research/sN/jensen_bound/feeding_sharp_recheck.py --run
```

The content-bound result is `feeding_sharp_receipt.json`. Its status, rather
than this prose, records whether the checked source closure currently passes.
