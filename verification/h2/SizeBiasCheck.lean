import MaxCaterpillar.Frontier.RandomRestriction.CoinRankSizeBiasConstants

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.SizeBiasCheck
open BigOperators

/-- Exact public analytic type: the hypotheses are a genuine finite
size-bias identity and a bounded coupling, not a concentration conclusion. -/
example {Ω : Type*} [Fintype Ω] (p X Y : Ω → ℝ) (μ c : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    (hμ : 0 ≤ μ) (hc : 0 < c)
    (hsize : FiniteSizeBiasIdentity p X Y μ)
    (hupper : ∀ ω, Y ω ≤ X ω + c) (t : ℝ) (ht : t ≤ 0) :
    finiteLaplace p X t ≤ Real.exp ((μ / c) * (Real.exp (c * t) - 1)) :=
  finiteLaplace_le_of_bounded_size_bias p X Y μ c hp hp_one hμ hc hsize hupper t ht

/-- Exact scalar expression obtained after the matching coupling and
two-disjoint-edge union count have been justified. -/
example (m K η : ℝ) (hm : 400 ≤ m) (hKpos : 0 < K) (hK : K ≤ m / 100)
    (hη : 0 ≤ η) :
    60 * η ^ 2 / m ^ 4 *
        Real.exp (-((7 : ℝ) / 24) * K * (η - 5 * (m + 4)) / m ^ 2) ≤
      400 / K ^ 2 :=
  matching_counting_expression_le_four_hundred m K η hm hKpos hK hη

/-- Nonvacuity with positive mean: a constant-one random variable is its
own size-biased variable on a one-state normalized finite space. -/
example : FiniteSizeBiasIdentity (fun _ : Unit => 1)
    (fun _ => 1) (fun _ => 1) 1 := by
  intro f
  simp

example : (∀ _ : Unit, (0 : ℝ) ≤ 1) ∧ (∑ ω : Unit, (1 : ℝ)) = 1 ∧
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) < 3 ∧
    FiniteSizeBiasIdentity (fun _ : Unit => 1) (fun _ => 1) (fun _ => 1) 1 ∧
    (∀ _ : Unit, (1 : ℝ) ≤ 1 + 3) := by
  refine ⟨fun _ => by norm_num, by simp, by norm_num, by norm_num, ?_, fun _ => by norm_num⟩
  intro f
  simp

#check @finiteLaplace
#check @FiniteSizeBiasIdentity
#check @hasDerivAt_finiteLaplace
#check @finiteLaplace_derivative_lower
#check @finiteLaplace_le_of_bounded_size_bias
#check @finite_geometric_le_of_size_bias_three
#check @square_mul_exp_neg_le
#check @exp_ninety_nine_fiftieths_lower
#check @shifted_square_exp_le_four_hundred
#check @deletion_shift_le_one_fiftieth
#check @matching_counting_expression_le_four_hundred

#print axioms hasDerivAt_finiteLaplace
#print axioms finiteLaplace_derivative_lower
#print axioms finiteLaplace_le_of_bounded_size_bias
#print axioms finite_geometric_le_of_size_bias_three
#print axioms square_mul_exp_neg_le
#print axioms exp_ninety_nine_fiftieths_lower
#print axioms shifted_square_exp_le_four_hundred
#print axioms deletion_shift_le_one_fiftieth
#print axioms matching_counting_expression_le_four_hundred

end MaxCaterpillar.Frontier.RandomRestriction.SizeBiasCheck
