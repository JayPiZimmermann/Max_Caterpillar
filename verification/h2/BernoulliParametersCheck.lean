import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
variable {n d : ℕ}

example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) : ParameterBounds n d :=
  parameter_bounds n d hd hn
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    100 ≤ bernoulliMean n d ∧ bernoulliMean n d/9 ≤ (matchingOrder n d:ℝ) ∧
      (minimumArity n d:ℝ) ≤ 3*bernoulliMean n d/5 ∧
      n ≤ 2*minimumTail n d ∧ 400 ≤ minimumTail n d ∧
      4 ≤ rankCount n d ∧ 100*rankCount n d ≤ minimumTail n d := by
  have B := parameter_bounds n d hd hn
  exact ⟨B.mean_lower,B.order_lower,B.arity_upper,B.total_le_twice_tail,
    B.tail_lower400,B.ranks_lower,B.hundred_ranks_le_tail⟩
example (n d : ℕ) : NeZero (minimumArity n d) := inferInstance
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ (d:ℝ)^2*(n:ℝ)^2) :
    supportBudget n d L ≤ (1/1000:ℝ) := supportBudget_le hd hn hL0 hL
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    8*(rankCount n d:ℝ)/(minimumTail n d:ℝ) ≤ (16/1000:ℝ) := shortQ_budget_le hd hn
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) :
    ((selectionProbability n d)^2/baseRate n d)^(matchingOrder n d)*
      Real.exp (baseRate n d*(selectedCap n d:ℝ)*((n:ℝ)-1)) ≤
        Real.exp (-(3*bernoulliMean n d/8)) := neuronEnvelope_le hd hn
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) (M : ℝ)
    (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    0 < Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3) :=
  admissible_denominator_pos hd hn M hM
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) (M : ℝ)
    (hM : M ≤ (d:ℝ)^2*(n:ℝ)^2) :
    Real.exp (-3*bernoulliMean n d/40) /
      (Real.exp (-2*M*(selectionProbability n d)^3)-Real.exp (-bernoulliMean n d/3)) ≤
        (1/100:ℝ) := conditioned_size_ratio_le hd hn M hM
example (hd : 1 ≤ d) (hn : 10000000000*d^2 ≤ n) (h₂ : ℕ)
    (hfinite : (9/10:ℝ) ≤ (h₂:ℝ)*neuronEnvelope n d) :
    (1/2:ℝ)*Real.exp (3*Real.sqrt (n:ℝ)/(8000*(d:ℝ))) ≤ (h₂:ℝ) :=
  conditional_width_bound hd hn h₂ hfinite

#check @parameter_bounds
#check @coverage_from_explicit_budgets
#check @conditional_width_bound
#print axioms parameter_bounds
#print axioms supportBudget_le
#print axioms shortQ_budget_le
#print axioms neuronEnvelope_le_strong
#print axioms neuronEnvelope_le
#print axioms noInternalExponent_le
#print axioms admissible_denominator_lower
#print axioms conditioned_size_ratio_le
#print axioms coverage_from_explicit_budgets
#print axioms conditional_width_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
