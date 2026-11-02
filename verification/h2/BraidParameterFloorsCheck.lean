import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters.Floors

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
variable {n q : ℕ}

example (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) : BraidParameterBounds n q :=
  braid_parameter_bounds n q hq hsize
example (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    braidArity q ≤ braidTail n q ∧
      100*braidRanks n q ≤ braidTail n q ∧ n ≤ 400*braidRanks n q :=
  ⟨(braid_parameter_bounds n q hq hsize).arity_le_tail,
    (braid_parameter_bounds n q hq hsize).ranks_upper,
    (braid_parameter_bounds n q hq hsize).ranks_lower_total⟩
example (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    braidTail n q + braidArity q = n ∧ 400 ≤ braidTail n q ∧
      4 ≤ braidRanks n q ∧ braidRanks n q < braidTail n q :=
  ⟨(braid_parameter_bounds n q hq hsize).total_eq,
    (braid_parameter_bounds n q hq hsize).tail_four_hundred,
    (braid_parameter_bounds n q hq hsize).ranks_lower,
    (braid_parameter_bounds n q hq hsize).ranks_lt_tail⟩
example (hq : 1 ≤ q) (hsize : 160000*q^2 ≤ n) :
    (n : ℝ)-1 ≤ 3*((braidTail n q : ℝ)-1) := braid_shift_real n q hq hsize

-- The hypotheses are attained at the first stated integer level.
example : BraidParameterBounds 160000 1 :=
  braid_parameter_bounds 160000 1 (by decide) (by decide)
example : braidArity 1 = 5 ∧ braidTail 160000 1 = 159995 ∧
    braidRanks 160000 1 = 1599 := by decide

#check @braid_parameter_bounds
#check @braidArity_le_half_real
#check @braidRanks_upper_real
#check @braidRanks_lower_real
#check @braid_shift_real
#print axioms braid_parameter_bounds
#print axioms braidArity_le_half_real
#print axioms braidRanks_upper_real
#print axioms braidRanks_lower_real
#print axioms braid_shift_real
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Parameters
