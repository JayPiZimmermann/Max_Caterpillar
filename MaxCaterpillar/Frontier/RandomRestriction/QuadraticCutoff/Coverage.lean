import Mathlib

/-! Coverage for the five-coordinate obstruction with a larger rank cutoff.
The two support budgets are expressed directly in the retained tail size.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff

private theorem falling_lower (m r : ℕ) (hr : r ≤ 6) :
    (m : ℝ)^r ≤ ((m + 5).descFactorial r : ℝ) := by
  have hb : m ≤ m + 5 + 1 - r := Nat.le_sub_of_add_le (by linarith only [hr])
  exact_mod_cast
    (Nat.pow_le_pow_left hb r).trans (Nat.pow_sub_le_descFactorial (m + 5) r)

/-- The literal coverage expression is at least one half. No support-count
or bad-event estimate is assumed beyond the two numerical moment budgets. -/
theorem coverage (m K : ℕ) (hm : 20000 ≤ m) (hKu : (K : ℝ) ≤ (m : ℝ) / 25)
    (M L : ℝ) (hM : M ≤ 2 * (m : ℝ)^2) (hL : L ≤ 100 * (m : ℝ)^2) :
    (1 / 2 : ℝ) ≤ 1 - 8 * (K : ℝ) / (m : ℝ) -
      M * 60 / ((m + 5).descFactorial 3 : ℝ) -
      L / ((m + 5).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)) +
          10 * (K : ℝ)) := by
  have hmR : (20000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith only [hmR]
  have hD3 := falling_lower m 3 (by decide)
  have hD4 := falling_lower m 4 (by decide)
  have hK25 : 25 * (K : ℝ) ≤ (m : ℝ) := by linarith only [hKu]
  have hKsq : 625 * (K : ℝ)^2 ≤ (m : ℝ)^2 := by
    have hh := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 25 * (K : ℝ)) hK25
    nlinarith only [hh]
  have hKfrac : (K : ℝ) / (m : ℝ) ≤ 1 / 25 :=
    (div_le_iff hm0).mpr (by linarith only [hK25])
  have hQ : 8 * (K : ℝ) / (m : ℝ) ≤ 8 / 25 :=
    (div_le_iff hm0).mpr (by linarith only [hK25])
  have hB1 : M * 60 / ((m + 5).descFactorial 3 : ℝ) ≤ 120 / (m : ℝ) := by
    calc
      _ ≤ (2 * (m : ℝ)^2 * 60) / (m : ℝ)^3 :=
        div_le_div (by positivity)
          (mul_le_mul_of_nonneg_right hM (by norm_num)) (by positivity) hD3
      _ = _ := by field_simp [hm0.ne']; ring
  have hLR : L / ((m + 5).descFactorial 4 : ℝ) ≤ 100 / (m : ℝ)^2 := by
    calc
      _ ≤ (100 * (m : ℝ)^2) / (m : ℝ)^4 :=
        div_le_div (by positivity) hL (by positivity) hD4
      _ = _ := by field_simp [hm0.ne']; ring
  have hden : 0 < 1 - (K : ℝ) / (m : ℝ) := by linarith only [hKfrac]
  have hfive : (5 : ℝ) / (m : ℝ) ≤ 1 / 125 :=
    (div_le_iff hm0).mpr (by linarith only [hmR])
  have hratio : (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)) ≤ 21 / 20 :=
    (div_le_iff hden).mpr (by linarith only [hKfrac, hfive])
  have hAnonneg : 0 ≤ (K : ℝ)^2 *
      ((1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ))) := by positivity
  have hA : L / ((m + 5).descFactorial 4 : ℝ) *
      ((K : ℝ)^2 * (1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ))) ≤ 21 / 125 := by
    calc
      _ = L / ((m + 5).descFactorial 4 : ℝ) *
          ((K : ℝ)^2 * ((1 + 5 / (m : ℝ)) / (1 - (K : ℝ) / (m : ℝ)))) := by ring
      _ ≤ (100 / (m : ℝ)^2) * ((K : ℝ)^2 * (21 / 20)) :=
        mul_le_mul hLR (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
          hAnonneg (by positivity)
      _ = 105 * (K : ℝ)^2 / (m : ℝ)^2 := by ring
      _ ≤ 21 / 125 := (div_le_iff (pow_pos hm0 2)).mpr (by nlinarith only [hKsq])
  have hC : L / ((m + 5).descFactorial 4 : ℝ) * (10 * (K : ℝ)) ≤ 40 / (m : ℝ) := by
    calc
      _ ≤ (100 / (m : ℝ)^2) * (10 * ((m : ℝ) / 25)) :=
        mul_le_mul hLR (mul_le_mul_of_nonneg_left hKu (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by field_simp [hm0.ne']; ring
  have hsmall : 120 / (m : ℝ) + 40 / (m : ℝ) ≤ 1 / 125 := by
    rw [← add_div]
    apply (div_le_iff hm0).mpr
    linarith only [hmR]
  rw [mul_add]
  linarith only [hQ, hB1, hA, hC, hsmall]

#print axioms coverage
end MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
