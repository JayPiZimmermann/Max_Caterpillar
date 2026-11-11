# An uncapped first-width tradeoff

The target declaration is `Tradeoff.affine_min_tradeoff` in `Min.lean`:
for every N≥3, an exact real affine-skip network computing MAX_N on every real
input satisfies

    h₂ ≥ min(N², N⁴/h₁) / 650000.

Here h₁ counts all original first hidden neurons. There is no quadratic-width
hypothesis, no positivity/integrality restriction on weights, and no structural
conjecture. The proof chooses the scale C=1 when h₁≤N² and C=h₁/N² otherwise,
then applies the actual scaled-width theorem. This arithmetic step is checked
in `ScalarMin.lean`, separately from the network and random-restriction proof.

The companion `affine_quadratic_of_first_cap` states h₂≥N²/650000 under h₁≤N².
It also handles h₁=0 without relying on a division convention. In the displayed
minimum formula, Lean's literal real division by zero equals zero, so that
formula is trivial at h₁=0. No infinite-denominator convention is assumed.

`MinCheck.lean` expands the affine evaluator into all nine real arrays/scalars,
retains universal quantification over real inputs, checks an arbitrary real
scale C≥1, and supplies an actual MAX3 network as a nonvacuity control. A cubic
first-width control confirms that C is allowed to grow with N.

Verification status is determined by `min_receipt.json`; this note alone is
not a verification claim. The scripts bind exact source hashes and standard
axiom reports. The theorem is an isolated research declaration until explicitly
integrated and published.
