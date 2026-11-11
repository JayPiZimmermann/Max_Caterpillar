import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean

/-! # Integer square-root choice for the explicit conditional braid bound

The selected matching order is a genuine natural floor. Its positivity and
quadratic size bound follow from the exact integer square-root inequalities.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters

def braidSqrtMatching (n : ℕ) : ℕ := Nat.sqrt n / 400

/-- The finite-q corollary applies to this explicit integer square-root choice. -/
theorem braidSqrtMatching_bounds (n : ℕ) (hN : 160000 ≤ n) :
    1 ≤ braidSqrtMatching n ∧ 160000 * (braidSqrtMatching n)^2 ≤ n := by
  have hs : 400 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by norm_num; exact hN)
  have hq : 1 ≤ braidSqrtMatching n := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 400)).mpr
    simpa only [one_mul] using hs
  have hdiv : braidSqrtMatching n * 400 ≤ Nat.sqrt n := Nat.div_mul_le_self (Nat.sqrt n) 400
  have hp := Nat.pow_le_pow_left hdiv 2
  have hsize : 160000 * (braidSqrtMatching n)^2 ≤ n := by
    calc
      160000 * (braidSqrtMatching n)^2 = (braidSqrtMatching n * 400)^2 := by ring
      _ ≤ (Nat.sqrt n)^2 := hp
      _ ≤ n := Nat.sqrt_le' n
  exact ⟨hq,hsize⟩

private lemma floor_real_sqrt_eq_nat_sqrt (n : ℕ) :
    Nat.floor (Real.sqrt (n : ℝ)) = Nat.sqrt n := by
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg _)).mpr
  refine ⟨Real.nat_sqrt_le_real_sqrt,?_⟩
  apply (Real.sqrt_lt (Nat.cast_nonneg n) (by positivity)).mpr
  exact_mod_cast Nat.lt_succ_sqrt' n

/-- The integer definition agrees exactly with the real square-root floor. -/
theorem braidSqrtMatching_eq_floor (n : ℕ) :
    braidSqrtMatching n = Nat.floor (Real.sqrt (n : ℝ) / 400) := by
  have hdiv := Nat.floor_div_nat (Real.sqrt (n : ℝ)) 400
  rw [floor_real_sqrt_eq_nat_sqrt] at hdiv
  exact hdiv.symm

#check @braidSqrtMatching_bounds
#check @braidSqrtMatching_eq_floor
#print axioms braidSqrtMatching_bounds
#print axioms braidSqrtMatching_eq_floor
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
