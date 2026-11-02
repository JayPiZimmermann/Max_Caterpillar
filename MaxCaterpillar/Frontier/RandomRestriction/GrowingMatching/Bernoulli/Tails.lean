import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Mgf

/-! Explicit finite Bernoulli cardinality tails and a scalar rare-event estimate. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ}

theorem exp_half_le_five_thirds : Real.exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem exp_neg_half_le_five_eighths : Real.exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff (Real.exp_pos _)]
  nlinarith

theorem mass_card_gt_two_mean_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) =>
      2 * ((n : ℝ) * p) < (S.card : ℝ)) ≤ Real.exp (-((n : ℝ) * p) / 3) := by
  classical
  have h := mass_le_exp_markov p (1/2) ((n : ℝ) * p) hp0 hp1
    (Finset.univ.filter fun S : Finset (Fin n) =>
      2 * ((n : ℝ) * p) < (S.card : ℝ)) (by
        intro S hS
        have hS := (Finset.mem_filter.mp hS).2
        linarith)
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hmu : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hh := mul_le_mul_of_nonneg_left exp_half_le_five_thirds hmu
  linarith

theorem mass_card_le_three_fifths_mean_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass p (Finset.univ.filter fun S : Finset (Fin n) =>
      (S.card : ℝ) ≤ 3 * ((n : ℝ) * p) / 5) ≤
      Real.exp (-3 * ((n : ℝ) * p) / 40) := by
  classical
  have h := mass_le_exp_markov p (-(1/2)) (-3 * ((n : ℝ) * p) / 10) hp0 hp1
    (Finset.univ.filter fun S : Finset (Fin n) =>
      (S.card : ℝ) ≤ 3 * ((n : ℝ) * p) / 5) (by
        intro S hS
        have hS := (Finset.mem_filter.mp hS).2
        linarith)
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hmu : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hh := mul_le_mul_of_nonneg_left exp_neg_half_le_five_eighths hmu
  linarith

theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have he := Real.add_one_le_exp (2 * x)
  have hx : 0 ≤ 1 - x := by linarith
  have hm := mul_le_mul_of_nonneg_left he hx
  have hquad : 0 ≤ x * (1 - 2 * x) := mul_nonneg hx0 (by linarith)
  have hprod : 1 ≤ (1 - x) * Real.exp (2 * x) := by nlinarith
  have hneg : -2 * x = -(2 * x) := by ring
  rw [hneg, Real.exp_neg, inv_eq_one_div, div_le_iff (Real.exp_pos _)]
  exact hprod

theorem exp_neg_two_sum_le_prod_one_sub {ι : Type*} (J : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ J, 0 ≤ x i) (hx1 : ∀ i ∈ J, x i ≤ 1/2) :
    Real.exp (-2 * ∑ i in J, x i) ≤ ∏ i in J, (1 - x i) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact (Real.exp_pos _).le
  · intro i hi
    exact exp_neg_two_mul_le_one_sub (hx0 i hi) (hx1 i hi)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
