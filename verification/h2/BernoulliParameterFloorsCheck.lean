import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Floors

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
variable {n d : ℕ}

example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) : ParameterBounds n d :=
  parameter_bounds n d hd hn
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    bernoulliMean n d/9 ≤ (matchingOrder n d : ℝ) ∧
      (matchingOrder n d : ℝ) ≤ bernoulliMean n d/8 ∧
      (minimumArity n d : ℝ) ≤ 3*bernoulliMean n d/5 :=
  ⟨(parameter_bounds n d hd hn).order_lower,(parameter_bounds n d hd hn).order_upper,
    (parameter_bounds n d hd hn).arity_upper⟩
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    400 ≤ minimumTail n d ∧ n ≤ 2*minimumTail n d ∧
      100*rankCount n d ≤ minimumTail n d :=
  ⟨(parameter_bounds n d hd hn).tail_lower400,
    (parameter_bounds n d hd hn).total_le_twice_tail,
    (parameter_bounds n d hd hn).hundred_ranks_le_tail⟩
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    delta d*(n : ℝ)/2 ≤ (rankCount n d : ℝ) ∧
      (rankCount n d : ℝ) ≤ delta d*(n : ℝ) :=
  ⟨(parameter_bounds n d hd hn).ranks_real_lower,(parameter_bounds n d hd hn).ranks_real_upper⟩
example (hn : 0 < n) (hd : 1 ≤ d) :
    selectionProbability n d*(n : ℝ)=bernoulliMean n d := probability_mul_total n d hn hd
example (hn : 0 < n) (hd : 1 ≤ d) :
    (selectionProbability n d)^2*(n : ℝ)=(alpha d)^2 := probability_sq_mul_total n d hn hd
example (n d : ℕ) : (bernoulliMean n d)^2=(alpha d)^2*(n : ℝ) := mean_sq n d
example (n d : ℕ) : rankCount n d=Nat.floor ((n : ℝ)/(1000*(d : ℝ)^2)) :=
  rankCount_eq_floor n d

#check @parameter_bounds
#check @probability_mul_total
#check @probability_sq_mul_total
#check @mean_sq
#check @alpha_sq
#check @rankCount_eq_floor
#print axioms parameter_bounds
#print axioms probability_mul_total
#print axioms probability_sq_mul_total
#print axioms mean_sq
#print axioms alpha_sq
#print axioms rankCount_eq_floor
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
