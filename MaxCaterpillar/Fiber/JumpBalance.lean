import MaxCaterpillar.Fiber.PositiveKink

/-! # Exact signed balance of local ReLU creases

A local identity determines the sum of the signed crease amplitudes of all
neurons vanishing on the crease. Nonvanishing intercepts are eliminated by an
exact finite midpoint calculation at a sufficiently small positive radius.
No prescribed activation pattern, genericity, or differentiability is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open BigOperators Filter Topology MaxCaterpillar.Frontier

lemma relu_add_relu_neg_eq_abs (u : ℝ) : relu u + relu (-u) = |u| := by
  rcases le_total 0 u with hu | hu
  · rw [relu_of_nonneg hu, relu_of_nonpos (neg_nonpos.mpr hu), abs_of_nonneg hu]
    ring
  · rw [relu_of_nonpos hu, relu_of_nonneg (neg_nonneg.mpr hu), abs_of_nonpos hu]
    ring

lemma relu_zero_intercept_midpoint (a ε : ℝ) (hε : 0 ≤ ε) :
    relu (a * ε) + relu (a * -ε) - 2 * relu 0 = |a| * ε := by
  have hn : a * -ε = -(a * ε) := by ring
  rw [hn, relu_add_relu_neg_eq_abs, relu_of_nonpos (le_refl (0 : ℝ)),
    mul_zero, sub_zero, abs_mul, abs_of_nonneg hε]

/-- The signed second midpoint difference distributes exactly over the neurons. -/
lemma sum_relu_midpoint_expand {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (ε : ℝ) :
    (∑ i, c i * (relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i))) =
      (∑ i, c i * relu (a i * ε + b i)) +
        (∑ i, c i * relu (a i * -ε + b i)) - 2 * ∑ i, c i * relu (b i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact local crease balance, with arbitrary signed target amplitude. -/
theorem local_relu_jump_balance {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (τ l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      τ * relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i)) :
    (∑ i in Finset.univ.filter (fun i => b i = 0), c i * |a i|) = τ := by
  classical
  have hsmall : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), b i ≠ 0 → |a i * ε| ≤ |b i| := by
    intro i
    by_cases hb : b i = 0
    · exact Filter.eventually_of_forall (fun _ hh => (hh hb).elim)
    · filter_upwards [eventually_small (a i) (abs_pos.mpr hb)] with ε hε
      intro _
      simpa only [mul_comm] using hε.le
  have hall := (Filter.eventually_all.mpr hsmall).and
    (Ioo_mem_nhdsWithin_Ioi (show (0 : ℝ) ∈ Set.Ico 0 δ from ⟨le_rfl, hδ⟩))
  obtain ⟨ε, hε, hε0, hεδ⟩ := hall.exists
  have hplus := h ε (by rwa [abs_of_pos hε0])
  have hminus := h (-ε) (by rwa [abs_neg, abs_of_pos hε0])
  have hzero := h 0 (by simpa using hδ)
  rw [relu_of_nonneg hε0.le] at hplus
  rw [relu_of_nonpos (neg_nonpos.mpr hε0.le), mul_zero] at hminus
  simp only [relu, max_self, mul_zero, zero_add] at hzero
  change 0 = γ + ∑ i, c i * relu (b i) at hzero
  have hterm : ∀ i,
      c i * (relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i)) =
        (if b i = 0 then c i * |a i| else 0) * ε := by
    intro i
    by_cases hb : b i = 0
    · rw [if_pos hb, hb, add_zero, add_zero, relu_zero_intercept_midpoint _ _ hε0.le]
      ring
    · rw [if_neg hb]
      have he : relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i) =
          relu (b i + a i * ε) + relu (b i - a i * ε) - 2 * relu (b i) := by
        congr 2 <;> congr 1 <;> ring
      rw [he, relu_midpoint_eq_zero _ _ (hε i hb), mul_zero, zero_mul]
  have hsum :
      (∑ i, c i * (relu (a i * ε + b i) + relu (a i * -ε + b i) - 2 * relu (b i))) =
        (∑ i in Finset.univ.filter (fun i => b i = 0), c i * |a i|) * ε := by
    rw [Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [sum_relu_midpoint_expand a b c ε] at hsum
  have heq : ((∑ i in Finset.univ.filter (fun i => b i = 0), c i * |a i|) - τ) * ε = 0 := by
    linear_combination -hplus - hminus + 2 * hzero - hsum
  rcases mul_eq_zero.mp heq with hj | he
  · linarith
  · exact (ne_of_gt hε0 he).elim

/-- A unit target crease has total signed vanishing-gate amplitude exactly one. -/
theorem unit_relu_jump_balance {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i)) :
    (∑ i in Finset.univ.filter (fun i => b i = 0), c i * |a i|) = 1 := by
  apply local_relu_jump_balance a b c 1 l γ δ hδ
  simpa only [one_mul] using h

/-- An affine local target has zero total signed crease amplitude. -/
theorem affine_jump_balance {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ → l * s + γ = ∑ i, c i * relu (a i * s + b i)) :
    (∑ i in Finset.univ.filter (fun i => b i = 0), c i * |a i|) = 0 := by
  apply local_relu_jump_balance a b c 0 (-l) (-γ) δ hδ
  intro s hs
  have hx := h s hs
  simp only [zero_mul]
  linarith only [hx]

/-- If all other vanishing gates have nonpositive outputs, the distinguished
gate carries at least the whole positive crease amplitude. -/
theorem unique_positive_jump_amplitude_ge {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (τ l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      τ * relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i))
    (j : ι) (hj : b j = 0)
    (hother : ∀ i, b i = 0 → i ≠ j → c i ≤ 0) :
    τ ≤ c j * |a j| := by
  classical
  let S := Finset.univ.filter (fun i => b i = 0)
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hsum : (∑ i in S.erase j, c i * |a i|) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
    exact mul_nonpos_of_nonpos_of_nonneg
      (hother i (Finset.mem_filter.mp hiS).2 hne) (abs_nonneg (a i))
  have hbal := local_relu_jump_balance a b c τ l γ δ hδ h
  change (∑ i in S, c i * |a i|) = τ at hbal
  rw [← Finset.sum_erase_add S (fun i => c i * |a i|) hjS] at hbal
  linarith only [hsum, hbal]

/-- Unit-crease version used for a uniquely positive facet carrier. -/
theorem unique_positive_unit_jump_amplitude_ge_one {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (l γ δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℝ, |s| < δ →
      relu s = l * s + γ + ∑ i, c i * relu (a i * s + b i))
    (j : ι) (hj : b j = 0)
    (hother : ∀ i, b i = 0 → i ≠ j → c i ≤ 0) :
    1 ≤ c j * |a j| := by
  apply unique_positive_jump_amplitude_ge a b c 1 l γ δ hδ _ j hj hother
  simpa only [one_mul] using h

end MaxCaterpillar.Fiber
