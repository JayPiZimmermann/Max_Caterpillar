import MaxCaterpillar.Fiber.PositiveKink

/-! # A spurious positive crease requires a negative crease at the same wall

This is a local identity for arbitrary finite signed affine ReLU sums. The
negative term must actually bend at the same point: a zero output, a nonzero
intercept, or a zero input slope cannot cancel the positive crease.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators Filter Topology MaxCaterpillar.Frontier

private lemma relu_opposite_sum_pos (u : ℝ) (hu : u ≠ 0) :
    0 < relu u + relu (-u) := by
  rcases lt_or_gt_of_ne hu with h | h
  · rw [relu_of_nonpos h.le, relu_of_nonneg (neg_nonneg.mpr h.le)]
    linarith
  · rw [relu_of_nonneg h.le, relu_of_nonpos (neg_nonpos.mpr h.le)]
    linarith

/-- An affine function cannot contain an uncanceled positive crease. Any exact
cancellation supplies a negative-output gate vanishing there with nonzero slope. -/
theorem exists_negative_active_zero_gate {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ → (∑ i, c i * relu (a i * s + b i)) = l * s + γ)
    (j : ι) (hcj : 0 < c j) (hbj : b j = 0) (haj : a j ≠ 0) :
    ∃ i, c i < 0 ∧ b i = 0 ∧ a i ≠ 0 := by
  classical
  by_contra hn
  have hbad : ∀ i, c i < 0 → b i = 0 → a i = 0 := by
    intro i hci hbi
    by_contra hai
    exact hn ⟨i, hci, hbi, hai⟩
  have hsmall : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c i < 0 → relu (b i + a i * ε) + relu (b i - a i * ε) - 2 * relu (b i) = 0 := by
    intro i
    by_cases hci : c i < 0
    · by_cases hbi : b i = 0
      · have hai := hbad i hci hbi
        exact Filter.eventually_of_forall fun ε _ => by simp [hai]; ring
      · filter_upwards [eventually_small (a i) (abs_pos.mpr hbi)] with ε hε
        intro _
        apply relu_midpoint_eq_zero
        simpa only [mul_comm] using hε.le
    · exact Filter.eventually_of_forall fun _ hh => (hci hh).elim
  have hall := (Filter.eventually_all.mpr hsmall).and (Ioo_mem_nhdsWithin_Ioi (show (0 : ℝ) ∈ Set.Ico 0 δ from ⟨le_rfl, hδ⟩))
  obtain ⟨ε, hε, hε0, hεδ⟩ := hall.exists
  let D : ι → ℝ := fun i =>
    c i * (relu (b i + a i * ε) + relu (b i - a i * ε) - 2 * relu (b i))
  have hD : ∀ i, 0 ≤ D i := by
    intro i
    dsimp only [D]
    by_cases hci : c i < 0
    · rw [hε i hci, mul_zero]
    · exact mul_nonneg (le_of_not_gt hci) (relu_midpoint_nonneg _ _)
  have hDj : 0 < D j := by
    have hprod : a j * ε ≠ 0 := mul_ne_zero haj hε0.ne'
    have hp := relu_opposite_sum_pos (a j * ε) hprod
    dsimp only [D]
    rw [hbj]
    simp only [zero_add, zero_sub, show relu 0 = 0 from max_self 0, mul_zero, sub_zero]
    exact mul_pos hcj hp
  have hsumpos : 0 < ∑ i, D i :=
    lt_of_lt_of_le hDj (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ j))
  have hp := h ε (by rwa [abs_of_pos hε0])
  have hm := h (-ε) (by rwa [abs_neg, abs_of_pos hε0])
  have hz := h 0 (by simpa using hδ)
  simp only [mul_zero, zero_add, add_zero] at hz
  have he : (∑ i, D i) = (∑ i, c i * relu (a i * ε + b i)) +
      (∑ i, c i * relu (a i * -ε + b i)) - 2 * ∑ i, c i * relu (b i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [D]
    have he1 : b i + a i * ε = a i * ε + b i := by ring
    have he2 : b i - a i * ε = a i * -ε + b i := by ring
    rw [he1, he2]
    ring
  rw [he] at hsumpos
  nlinarith only [hp, hm, hz, hsumpos]

/-- The weaker sign consequence, convenient for residual gate lower bounds. -/
theorem exists_negative_output_of_spurious_positive_gate {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ → (∑ i, c i * relu (a i * s + b i)) = l * s + γ)
    (j : ι) (hcj : 0 < c j) (hbj : b j = 0) (haj : a j ≠ 0) :
    ∃ i, c i < 0 := by
  obtain ⟨i, hi, _, _⟩ := exists_negative_active_zero_gate a b c l γ δ hδ h j hcj hbj haj
  exact ⟨i, hi⟩

end MaxCaterpillar.Fiber
