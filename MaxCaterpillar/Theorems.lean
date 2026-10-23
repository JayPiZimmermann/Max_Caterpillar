import MaxCaterpillar.OneBasis
import MaxCaterpillar.CountLower
import MaxCaterpillar.CountExp
import MaxCaterpillar.LowerBound

/-! # The public theorem interface

The objects are defined in `Definitions.lean`. The supporting development, the
Version 1 and Version 2 statements (`maximum_width`, `maximum_width_rational`,
`compilation`, …), and the internal names are in `Core.lean` and the files it
imports.

* `caterpillar_net`: the Caterpillar Net computes `max_N` with two hidden
  layers of widths `firstWidth N` and `secondWidth N`, rational weights, and
  zero biases.
* `caterpillar_expansion_choose_le`, `caterpillar_expansion_exponential`,
  `caterpillar_expansion_quadratic`: every caterpillar expansion of `max_N`
  uses at least `C(N,k)/6^k` (`3 ≤ k ≤ N`), hence `(7/6)^N/(N+1)`, and at least
  `N(N-1)/6` caterpillar functions.
* `caterpillarDim_ge`: `dim(V_N/A_N) ≥ (N-2)!`.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar

/-- **Caterpillar Net.** For every positive arity `N` there is a two-hidden-layer
ReLU network of widths `firstWidth N` and `secondWidth N` with rational weights
and zero biases computing `max_N` on all of `ℝ^N`. (Version 3 of
`maximum_width`; the rational coefficients come from one basis of the
caterpillar span, `OneBasis.lean`.) -/
theorem caterpillar_net (N : ℕ) [NeZero N] :
    ∃ net : Network N (firstWidth N) (secondWidth N),
      (∀ x, net.eval x = Maximum N x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases :=
  maximum_width_one_basis N

/-- Unfold a caterpillar expansion into the internal hypotheses. -/
theorem IsCaterpillarExpansion.unfold {r : ℕ} {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    K ⊆ Corrections.normalizedKeys r ∧
      ∃ (d : FaceKey r → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ),
        ∀ x, Maximum (r + 1 + 1) x =
          ∑ k in K, d k * Corrections.realUnitY k x + auxiliary a x :=
  hK

/-- **Exponential count, binomial form.** Every caterpillar expansion `K` of
`max_N`, `N = r + 2`, satisfies `C(N, k) ≤ 6^k |K|` for every `3 ≤ k ≤ N`. -/
theorem caterpillar_expansion_choose_le (r : ℕ) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ 6 ^ k * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_exponential r K hsub d a h hk hkN

/-- **Exponential count.** Every caterpillar expansion `K` of `max_N`,
`N = r + 2 ≥ 3`, satisfies `7^N ≤ (N + 1) 6^N |K|`, i.e. `|K| ≥ (7/6)^N/(N+1)`. -/
theorem caterpillar_expansion_exponential (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_exponential_pow r hr K hsub d a h

/-- **Quadratic count.** Every caterpillar expansion `K` of `max_N`,
`N = r + 2 ≥ 3`, satisfies `N(N - 1) ≤ 6 |K|`. -/
theorem caterpillar_expansion_quadratic (r : ℕ) (hr : 1 ≤ r) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    (r + 1 + 1) * (r + 1) ≤ 6 * K.card := by
  obtain ⟨hsub, d, a, h⟩ := hK.unfold
  exact caterpillar_count_lower r hr K hsub d a h

/-- The caterpillar span is the span of the dictionary. -/
theorem caterpillarSpan_eq (r : ℕ) : caterpillarSpan r = vocabularySpan r := by
  classical
  unfold caterpillarSpan vocabularySpan
  rw [dictionary_eq_range]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ (⟨k, hk, rfl⟩ | ⟨j, rfl⟩)
    · obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_image.mp hk
      apply Submodule.subset_span
      refine ⟨Sum.inl ⟨k₀, hk₀⟩, ?_⟩
      show Corrections.realUnitY k₀ = Corrections.realUnitY (Corrections.normalizedKey k₀)
      exact (Corrections.realUnitY_normalizedKey hk₀).symm
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl k =>
      apply Submodule.subset_span
      refine Or.inl ⟨Corrections.normalizedKey k.1, Finset.mem_image_of_mem _ k.2, ?_⟩
      exact Corrections.realUnitY_normalizedKey k.2
    | inr j => exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)

/-- `caterpillarDim` is the quotient dimension `q_N` of `Quotient.lean`. -/
theorem caterpillarDim_eq (r : ℕ) : caterpillarDim r = quotientDim r := by
  unfold caterpillarDim quotientDim
  rw [caterpillarSpan_eq]
  rfl

/-- **Dimension of the caterpillar span.** For `N = r + 2 ≥ 3`,
`dim(V_N / A_N) ≥ (N - 2)!`. -/
theorem caterpillarDim_ge (r : ℕ) (hr : 1 ≤ r) : r.factorial ≤ caterpillarDim r := by
  rw [caterpillarDim_eq]
  exact factorial_le_quotientDim r hr

end MaxCaterpillar
