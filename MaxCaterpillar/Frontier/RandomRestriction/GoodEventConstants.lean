import Mathlib

/-! # Scalar assembly for the full-permutation good-event count -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent

theorem good_event_coefficient_le (m K : ℝ) (hm : 400 ≤ m)
    (hKlow : 4 ≤ K) (hKhigh : K ≤ m / 100) :
    (1 + 5 / m) / (1 - K / m) + 10 / K ≤ (155 : ℝ) / 44 := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKlow
  have hq : K / m ≤ 1 / 100 := by
    apply (div_le_iff hmpos).mpr
    linarith only [hKhigh]
  have hden : (99 : ℝ) / 100 ≤ 1 - K / m := by linarith only [hq]
  have hdenpos : 0 < 1 - K / m := lt_of_lt_of_le (by norm_num) hden
  have hnum : 1 + 5 / m ≤ (81 : ℝ) / 80 := by
    have hh : 5 / m ≤ (1 : ℝ) / 80 := by
      apply (div_le_iff hmpos).mpr
      linarith only [hm]
    linarith only [hh]
  have hfirst : (1 + 5 / m) / (1 - K / m) ≤ (45 : ℝ) / 44 := by
    apply (div_le_iff hdenpos).mpr
    linarith only [hnum, hden]
  have hsecond : 10 / K ≤ (5 : ℝ) / 2 := by
    apply (div_le_iff hKpos).mpr
    linarith only [hKlow]
  linarith only [hfirst, hsecond]

theorem good_event_numerator_le (m K : ℝ) (hm : 400 ≤ m)
    (hKlow : 4 ≤ K) (hKhigh : K ≤ m / 100) :
    K ^ 2 * (1 + 5 / m) / (1 - K / m) + 10 * K ≤ 4 * K ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKlow
  have hc := good_event_coefficient_le m K hm hKlow hKhigh
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg K)
  have heq : K ^ 2 * ((1 + 5 / m) / (1 - K / m) + 10 / K) =
      K ^ 2 * (1 + 5 / m) / (1 - K / m) + 10 * K := by
    field_simp [hKpos.ne']
    <;> ring
  rw [heq] at hh
  nlinarith only [hh, sq_nonneg K]

theorem fifth_prefix_descFactorial_four (m : ℕ) :
    ((m + 5).descFactorial 4 : ℝ) =
      ((m : ℝ) + 5) * ((m : ℝ) + 4) * ((m : ℝ) + 3) * ((m : ℝ) + 2) := by
  simp only [Nat.descFactorial, Nat.sub_zero, mul_one, Nat.sub_sub]
  norm_num [Nat.add_sub_assoc] <;> ring

theorem fifth_prefix_descFactorial_four_ge (m : ℕ) :
    (m : ℝ) ^ 4 ≤ ((m + 5).descFactorial 4 : ℝ) := by
  rw [fifth_prefix_descFactorial_four]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ)^2 ≤ ((m : ℝ)+5) * ((m : ℝ)+4) := by nlinarith only [hm]
  have h2 : (m : ℝ)^2 ≤ ((m : ℝ)+3) * ((m : ℝ)+2) := by nlinarith only [hm]
  have hh := mul_le_mul h1 h2 (sq_nonneg (m : ℝ))
    (by positivity : 0 ≤ ((m : ℝ)+5) * ((m : ℝ)+4))
  nlinarith only [hh]

/-- The common four-role denominator comes from a single actual uniform
full permutation of m+5 vertices, rather than separate selected/tail laws. -/
theorem full_permutation_good_event_scalar_le
    (m : ℕ) (K R : ℝ) (hm : 400 ≤ m) (hKlow : 4 ≤ K)
    (hKhigh : K ≤ (m : ℝ) / 100) (hR : 0 ≤ R) :
    R / ((m + 5).descFactorial 4 : ℝ) *
        (K ^ 2 * (1 + 5 / (m : ℝ)) / (1 - K / (m : ℝ)) + 10 * K) ≤
      4 * R * K ^ 2 / (m : ℝ) ^ 4 := by
  have hmR : (400 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmR
  have hden := fifth_prefix_descFactorial_four_ge m
  have hdenpos : (0 : ℝ) < ((m + 5).descFactorial 4 : ℝ) :=
    lt_of_lt_of_le (pow_pos hmpos 4) hden
  have hn := good_event_numerator_le (m : ℝ) K hmR hKlow hKhigh
  calc
    _ ≤ R / ((m + 5).descFactorial 4 : ℝ) * (4 * K ^ 2) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hR hdenpos.le)
    _ = (4 * R * K ^ 2) / ((m + 5).descFactorial 4 : ℝ) := by ring
    _ ≤ _ := div_le_div_of_le_left (by positivity) (pow_pos hmpos 4) hden

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
