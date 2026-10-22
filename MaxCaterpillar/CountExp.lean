import MaxCaterpillar.CountExp.Main

/-! # An exponential lower bound on the number of caterpillar face functions

Any expansion of the maximum of `N = r + 2` coordinates by normalized
caterpillar face functions `K` and an auxiliary remainder (a linear combination
of the neurons of the first hidden layer) satisfies `C(N, k) ≤ 6^k |K|` for every
`3 ≤ k ≤ N`, and hence `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N / (N + 1)`.

The proof (`research/sN/NOTE.md`, "MAIN ROUTE") is in `CountExp/`:
* `W1Functional`: the `k`-th mixed finite difference at the base point of a
  locality kills the auxiliary span, is `-(-1)^k δ` on the maximum, and is nonzero
  on a face function only if its preactivation vanishes there and condition (s)
  holds;
* `W2Digits`: a vanishing preactivation gives condition (a) (base-`B` digits);
* `W3Structure`: the functions `σ(y_i - y_j)` of a normalized key form a
  caterpillar forest, and passed tie sets are admissible and determined by their
  spine indices;
* `W4Orders`: the balanced orders with a fixed tie set number at most
  `k! (N - k)! / 2^{matchCount}`;
* `W5Generating`: the generating function along the spine is at most `1` at `1/6`;
* `Main`: assembly.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- **Exponential count, binomial form.** Any expansion of the maximum of
`N = r + 2` coordinates by normalized caterpillar face functions `K`, with an
auxiliary remainder, satisfies `C(N, k) ≤ 6^k |K|` for every `3 ≤ k ≤ N`. -/
theorem caterpillar_count_exponential (r : ℕ)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card :=
  CountExp.choose_le_six_pow_mul_card r K hK d a h hk hkN

/-- **Exponential count.** Any expansion of the maximum of `N = r + 2 ≥ 3`
coordinates by normalized caterpillar face functions `K`, with an auxiliary
remainder, satisfies `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N / (N + 1)`. -/
theorem caterpillar_count_exponential_pow (r : ℕ) (hr : 1 ≤ r)
    (K : Finset (Caterpillar.Corrections.RealKey (r + 1)))
    (hK : K ⊆ Caterpillar.Corrections.normalizedKeys r)
    (d : Caterpillar.Corrections.RealKey (r + 1) → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ k in K, d k * Caterpillar.Corrections.realUnitY k x + auxiliary a x) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card :=
  CountExp.seven_pow_le r hr K hK d a h

end MaxCaterpillar
