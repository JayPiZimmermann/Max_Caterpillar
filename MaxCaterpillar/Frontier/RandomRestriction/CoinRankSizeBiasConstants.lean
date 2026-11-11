import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBias
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # The scalar constant 400 for matching-based neuron counting

These are scalar inequalities. The actual random-permutation coupling,
conditional coin rank, and local graph witness count are separate bridges.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators

/-- The familiar exponential maximum follows from the exponential tangent
inequality by squaring, without a separate optimization argument. -/
theorem square_mul_exp_neg_le (y : ℝ) (hy : 0 ≤ y) :
    y ^ 2 * Real.exp (-y) ≤ 4 * Real.exp (-2) := by
  have ht : y / 2 ≤ Real.exp (y / 2 - 1) := by
    have hh := Real.add_one_le_exp (y / 2 - 1)
    linarith only [hh]
  have hs := mul_self_le_mul_self (show (0 : ℝ) ≤ y / 2 by positivity) ht
  have he : Real.exp (y / 2 - 1) * Real.exp (y / 2 - 1) = Real.exp (y - 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  have hsq : y ^ 2 ≤ 4 * Real.exp (y - 2) := by nlinarith only [hs]
  calc
    _ ≤ (4 * Real.exp (y - 2)) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
    _ = 4 * Real.exp (-2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

theorem exp_ninety_nine_fiftieths_lower :
    (1728 : ℝ) / 245 ≤ Real.exp (99 / 50) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 50) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith only [hh]

/-- The complete dimensionless estimate, with a deliberately rounded
shift of 1/50 instead of its sharper value 707/48000. -/
theorem shifted_square_exp_le_four_hundred (y d : ℝ) (hy : 0 ≤ y)
    (hd : d ≤ 1 / 50) :
    (34560 : ℝ) / 49 * y ^ 2 * Real.exp (d - y) ≤ 400 := by
  have ht : y / 2 ≤ Real.exp (y / 2 - 1) := by
    have hh := Real.add_one_le_exp (y / 2 - 1)
    linarith only [hh]
  have hs := mul_self_le_mul_self (show (0 : ℝ) ≤ y / 2 by positivity) ht
  have he : Real.exp (y / 2 - 1) * Real.exp (y / 2 - 1) = Real.exp (y - 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  have hsq : y ^ 2 ≤ 4 * Real.exp (y - 2) := by nlinarith only [hs]
  have hshift : y ^ 2 * Real.exp (d - y) ≤ 4 * Real.exp (d - 2) := by
    calc
      _ ≤ (4 * Real.exp (y - 2)) * Real.exp (d - y) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
      _ = 4 * Real.exp (d - 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
  have hdexp : Real.exp (d - 2) ≤ Real.exp (-(99 / 50)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hd]
  have hnum : (138240 : ℝ) / 49 * Real.exp (-(99 / 50)) ≤ 400 := by
    rw [Real.exp_neg]
    change (138240 : ℝ) / 49 / Real.exp (99 / 50) ≤ 400
    apply (div_le_iff (Real.exp_pos _)).mpr
    have hh := exp_ninety_nine_fiftieths_lower
    nlinarith only [hh]
  calc
    _ = (34560 : ℝ) / 49 * (y ^ 2 * Real.exp (d - y)) := by ring
    _ ≤ (34560 : ℝ) / 49 * (4 * Real.exp (d - 2)) :=
      mul_le_mul_of_nonneg_left hshift (by norm_num)
    _ ≤ (138240 : ℝ) / 49 * Real.exp (-(99 / 50)) := by
      have hh := mul_le_mul_of_nonneg_left hdexp (by norm_num : (0 : ℝ) ≤ 138240 / 49)
      nlinarith only [hh]
    _ ≤ 400 := hnum

/-- The shift caused by removing five vertices stays below 1/50. -/
theorem deletion_shift_le_one_fiftieth (m K : ℝ) (hm : 400 ≤ m)
    (hK : K ≤ m / 100) :
    ((35 : ℝ) / 24 * K * (m + 4)) / m ^ 2 ≤ 1 / 50 := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  apply (div_le_iff (sq_pos_of_pos hmpos)).mpr
  have hK' : 100 * K ≤ m := by linarith only [hK]
  have hm4 : m + 4 ≤ (101 : ℝ) / 100 * m := by linarith only [hm]
  have h1 := mul_le_mul_of_nonneg_right hK' (show 0 ≤ m + 4 by linarith only [hm])
  have h2 := mul_le_mul_of_nonneg_left hm4 hmpos.le
  nlinarith only [h1, h2]

/-- Scalar assembly after the actual matching Laplace estimate and local
two-edge union bound. It contains no assumed network conclusion. -/
theorem matching_counting_expression_le_four_hundred
    (m K η : ℝ) (hm : 400 ≤ m) (hKpos : 0 < K) (hK : K ≤ m / 100)
    (hη : 0 ≤ η) :
    60 * η ^ 2 / m ^ 4 *
        Real.exp (-((7 : ℝ) / 24) * K * (η - 5 * (m + 4)) / m ^ 2) ≤
      400 / K ^ 2 := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  let y : ℝ := ((7 : ℝ) / 24 * K * η) / m ^ 2
  let d : ℝ := ((35 : ℝ) / 24 * K * (m + 4)) / m ^ 2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hd : d ≤ 1 / 50 := deletion_shift_le_one_fiftieth m K hm hK
  have hh := shifted_square_exp_le_four_hundred y d hy hd
  have hexp : -((7 : ℝ) / 24) * K * (η - 5 * (m + 4)) / m ^ 2 = d - y := by
    dsimp [d, y]
    ring
  have heq : K ^ 2 * (60 * η ^ 2 / m ^ 4 * Real.exp (d - y)) =
      (34560 : ℝ) / 49 * y ^ 2 * Real.exp (d - y) := by
    dsimp [y]
    field_simp [hmpos.ne']
    <;> ring
  apply (le_div_iff (sq_pos_of_pos hKpos)).mpr
  rw [hexp]
  have hresult : K ^ 2 * (60 * η ^ 2 / m ^ 4 * Real.exp (d - y)) ≤ 400 := by
    rw [heq]
    exact hh
  nlinarith only [hresult]

end MaxCaterpillar.Frontier.RandomRestriction
