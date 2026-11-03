import Mathlib

/-! Exact scalar coverage after a falling-factorial half restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace MaxCaterpillar.OvernightConstants.Theta

private theorem falling_lower (m r : ℕ) (hr : r ≤ 6) :
    (m : ℝ)^r ≤ ((m + 5).descFactorial r : ℝ) := by
  have hb : m ≤ m + 5 + 1 - r := Nat.le_sub_of_add_le (by linarith only [hr])
  exact_mod_cast
    (Nat.pow_le_pow_left hb r).trans (Nat.pow_sub_le_descFactorial (m + 5) r)

/-- The two support budgets and an admissible cutoff imply coverage at least5/8. -/
theorem coverage (m K : ℕ) (hm : 20000 ≤ m) (hKu : (K : ℝ) ≤ (m : ℝ) / 10)
    (M L : ℝ) (hM : M ≤ 1 * (m : ℝ)^2) (hL : L ≤ 27 * (m : ℝ)^2) :
    (5 / 8 : ℝ) ≤ 1 - (1/16:ℝ) -
      M * 60 / ((m + 5).descFactorial 3 : ℝ) -
      L / ((m + 5).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)) +
          10 * (K : ℝ)) := by
  have hmR : (20000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith only [hmR]
  have hD3 := falling_lower m 3 (by decide)
  have hD4 := falling_lower m 4 (by decide)
  have hK10 : 10 * (K : ℝ) ≤ (m : ℝ) := by linarith only [hKu]
  have hKsq : 100 * (K : ℝ)^2 ≤ (m : ℝ)^2 := by
    have hh := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 10 * (K : ℝ)) hK10
    nlinarith only [hh]
  have hKfrac : (K : ℝ) / (m : ℝ) ≤ 1 / 10 :=
    (div_le_iff hm0).mpr (by linarith only [hK10])
  have hB1 : M * 60 / ((m + 5).descFactorial 3 : ℝ) ≤ 60 / (m : ℝ) := by
    calc
      _ ≤ (1 * (m : ℝ)^2 * 60) / (m : ℝ)^3 :=
        div_le_div (by positivity)
          (mul_le_mul_of_nonneg_right hM (by norm_num)) (by positivity) hD3
      _ = _ := by field_simp [hm0.ne']; ring
  have hLR : L / ((m + 5).descFactorial 4 : ℝ) ≤ 27 / (m : ℝ)^2 := by
    calc
      _ ≤ (27 * (m : ℝ)^2) / (m : ℝ)^4 :=
        div_le_div (by positivity) hL (by positivity) hD4
      _ = _ := by field_simp [hm0.ne']; ring
  have hden : 0 < 1 - (K : ℝ) / (m : ℝ) := by linarith only [hKfrac]
  have hfive : (5 : ℝ) / (m : ℝ) ≤ 1 / 4000 :=
    (div_le_iff hm0).mpr (by linarith only [hmR])
  have hratio : (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)) ≤ 139 / 125 :=
    (div_le_iff hden).mpr (by linarith only [hKfrac, hfive])
  have hAnonneg : 0 ≤ (K : ℝ)^2 *
      ((1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ))) := by positivity
  have hA : L / ((m + 5).descFactorial 4 : ℝ) *
      ((K : ℝ)^2 * (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ))) ≤ 3753 / 12500 := by
    calc
      _ = L / ((m + 5).descFactorial 4 : ℝ) *
          ((K : ℝ)^2 * ((1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)))) := by ring
      _ ≤ (27 / (m : ℝ)^2) * ((K : ℝ)^2 * (139 / 125)) :=
        mul_le_mul hLR (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
          hAnonneg (by positivity)
      _ = (3753 / 125) * (K : ℝ)^2 / (m : ℝ)^2 := by ring
      _ ≤ 3753 / 12500 := (div_le_iff (pow_pos hm0 2)).mpr (by nlinarith only [hKsq])
  have hC : L / ((m + 5).descFactorial 4 : ℝ) * (10 * (K : ℝ)) ≤ 27 / (m : ℝ) := by
    calc
      _ ≤ (27 / (m : ℝ)^2) * (10 * ((m : ℝ) / 10)) :=
        mul_le_mul hLR (mul_le_mul_of_nonneg_left hKu (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by field_simp [hm0.ne']; ring
  have hsmall : 60 / (m : ℝ) + 27 / (m : ℝ) ≤ 1 / 200 := by
    rw [← add_div]
    apply (div_le_iff hm0).mpr
    linarith only [hmR]
  rw [mul_add]
  linarith only [hB1, hA, hC, hsmall]

#print axioms coverage
end MaxCaterpillar.OvernightConstants.Theta
