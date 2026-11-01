import MaxCaterpillar.Frontier.Basic

/-! # A positive target crease needs a positive vanishing gate

The conclusion concerns arbitrary real coefficients and an identity on a
neighborhood of the target crease. No gate pattern is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators Filter Topology MaxCaterpillar.Frontier

theorem relu_midpoint_nonneg (b u : ℝ) :
    0 ≤ relu (b + u) + relu (b - u) - 2 * relu b := by
  rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg hb]
    have h1 : b + u ≤ relu (b + u) := le_max_right _ _
    have h2 : b - u ≤ relu (b - u) := le_max_right _ _
    linarith only [h1, h2]
  · rw [relu_of_nonpos hb]
    linarith only [relu_nonneg (b + u), relu_nonneg (b - u)]

theorem relu_midpoint_eq_zero (b u : ℝ) (hu : |u| ≤ |b|) :
    relu (b + u) + relu (b - u) - 2 * relu b = 0 := by
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb] at hu
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    rw [relu_of_nonneg hb, relu_of_nonneg (by linarith),
      relu_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos hb] at hu
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    rw [relu_of_nonpos hb, relu_of_nonpos (by linarith),
      relu_of_nonpos (by linarith)]
    ring

/-- An exact local expression of a positive hinge by signed affine ReLUs
must have a positive-output gate whose intercept vanishes at the hinge. -/
theorem exists_positive_active_zero_gate {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i)) :
    ∃ i, 0 < c i ∧ a i ≠ 0 ∧ b i = 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hsmall : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < c i → |a i * ε| ≤ |b i| := by
    intro i
    by_cases hi : 0 < c i
    · by_cases ha : a i = 0
      · exact Filter.eventually_of_forall (fun _ _ => by simp [ha])
      · filter_upwards [eventually_small (a i) (abs_pos.mpr (hn i hi ha))] with ε hε
        intro _
        simpa only [mul_comm] using hε.le
    · exact Filter.eventually_of_forall (fun _ hh => (hi hh).elim)
  have hall := (Filter.eventually_all.mpr hsmall).and
    (Ioo_mem_nhdsWithin_Ioi (show (0 : ℝ) ∈ Set.Ico 0 δ from ⟨le_rfl, hδ⟩))
  obtain ⟨ε, hε, hε0, hεδ⟩ := hall.exists
  have hplus := h ε (by rwa [abs_of_pos hε0])
  have hminus := h (-ε) (by rwa [abs_neg, abs_of_pos hε0])
  have hzero := h 0 (by simpa using hδ)
  rw [relu_of_nonneg hε0.le] at hplus
  rw [relu_of_nonpos (neg_nonpos.mpr hε0.le)] at hminus
  simp only [relu, max_self, mul_zero, zero_add] at hzero
  have hterm : ∀ i, c i *
      (relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i)) ≤ 0 := by
    intro i
    have he : relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i) =
        relu (b i + a i * ε) + relu (b i - a i * ε) - 2 * relu (b i) := by
      congr 2 <;> congr 1 <;> ring
    rw [he]
    by_cases hi : 0 < c i
    · rw [relu_midpoint_eq_zero _ _ (hε i hi), mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi)
        (relu_midpoint_nonneg _ _)
  have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hterm i)
  have hexpand : (∑ i, c i *
      (relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i))) =
      (∑ i, c i * relu (a i * ε + b i)) +
        (∑ i, c i * relu (a i * -ε + b i)) - 2 * ∑ i, c i * relu (b i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand] at hsum
  change 0 = γ + ∑ i, c i * relu (b i) at hzero
  nlinarith only [hplus, hminus, hzero, hsum, hε0]

theorem exists_positive_zero_gate {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i)) :
    ∃ i, 0 < c i ∧ b i = 0 := by
  obtain ⟨i, hi, _, hz⟩ := exists_positive_active_zero_gate a b c l γ δ hδ h
  exact ⟨i, hi, hz⟩

end MaxCaterpillar.Fiber
