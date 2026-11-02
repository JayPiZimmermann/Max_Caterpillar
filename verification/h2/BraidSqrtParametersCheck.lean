import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Sqrt

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
example (n : ℕ) (hN : 160000 ≤ n) :
    1 ≤ braidSqrtMatching n ∧ 160000 * (braidSqrtMatching n)^2 ≤ n :=
  braidSqrtMatching_bounds n hN
example (n : ℕ) : braidSqrtMatching n = Nat.floor (Real.sqrt (n : ℝ) / 400) :=
  braidSqrtMatching_eq_floor n
example (n : ℕ) (hN : 160000 ≤ n) :
    1 ≤ Nat.floor (Real.sqrt (n : ℝ) / 400) ∧
      160000 * (Nat.floor (Real.sqrt (n : ℝ) / 400))^2 ≤ n := by
  rw [← braidSqrtMatching_eq_floor]
  exact braidSqrtMatching_bounds n hN

#check @braidSqrtMatching_bounds
#check @braidSqrtMatching_eq_floor
#print axioms braidSqrtMatching_bounds
#print axioms braidSqrtMatching_eq_floor
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
