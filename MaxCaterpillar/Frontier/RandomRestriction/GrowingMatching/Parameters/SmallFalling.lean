import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Falling
import Mathlib.Tactic

/-! Lower bounds for the literal third and fourth descending factorials. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

private theorem lower_power_desc (n r : ℕ) (hr : r ≤ n+1) :
    ((n : ℝ)+1-(r : ℝ))^r ≤ (n.descFactorial r : ℝ) := by
  have hh : (((n+1-r : ℕ) : ℝ)^r) ≤ (n.descFactorial r : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial n r
  simpa only [Nat.cast_sub hr,Nat.cast_add,Nat.cast_one] using hh

theorem descFactorial_three_lower (n : ℕ) (hn : 12 ≤ n) :
    (n : ℝ)^3/2 ≤ (n.descFactorial 3 : ℝ) := by
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hscale : (5*(n : ℝ)/6) ≤ (n : ℝ)-2 := by linarith only [hnR]
  calc
    (n : ℝ)^3/2 ≤ (5*(n : ℝ)/6)^3 := by nlinarith only [pow_nonneg hp 3]
    _ ≤ ((n : ℝ)-2)^3 := pow_le_pow_left (by positivity) hscale 3
    _ ≤ (n.descFactorial 3 : ℝ) := by
      convert lower_power_desc n 3 (by linarith only [hn]) using 1 <;> norm_num <;> ring

theorem descFactorial_four_lower (n : ℕ) (hn : 12 ≤ n) :
    (n : ℝ)^4/4 ≤ (n.descFactorial 4 : ℝ) := by
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hscale : (3*(n : ℝ)/4) ≤ (n : ℝ)-3 := by linarith only [hnR]
  calc
    (n : ℝ)^4/4 ≤ (3*(n : ℝ)/4)^4 := by nlinarith only [pow_nonneg hp 4]
    _ ≤ ((n : ℝ)-3)^4 := pow_le_pow_left (by positivity) hscale 4
    _ ≤ (n.descFactorial 4 : ℝ) := by
      convert lower_power_desc n 4 (by linarith only [hn]) using 1 <;> norm_num <;> ring

#print axioms descFactorial_three_lower
#print axioms descFactorial_four_lower
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
