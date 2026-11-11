import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Arity
import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.SupportMoment
import MaxCaterpillar.Frontier.RandomRestriction.NewCountingTradeoff

/-! # Scalar transfer from actual half models to the original network -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
variable {N n h₁ h₂ : ℕ}

lemma descFactorial_three_real (hn : 2≤n) :
    (n.descFactorial 3 : ℝ)=(n : ℝ)*((n : ℝ)-1)*((n : ℝ)-2) := by
  have h1 : 1≤n := (by decide : 1≤2).trans hn
  rw [Nat.descFactorial_succ n 2, Nat.descFactorial_succ n 1,
    Nat.descFactorial_succ n 0]
  simp only [Nat.descFactorial_zero,
    Nat.sub_zero, mul_one, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_sub h1,
    Nat.cast_ofNat]
  ring

lemma half_model_count_budget (hN : 1040≤N)
    (hwidth : 1000*(h₁ : ℝ)≤(N : ℝ)^3)
    (net : NormalizedNetwork (N/2) h₁ h₂)
    (hcount : 4*ActualHalfRestriction.nonBraidCount net≤h₁) :
    240*ActualHalfRestriction.nonBraidCount net≤(N/2).descFactorial 3 := by
  have hc : 4*(ActualHalfRestriction.nonBraidCount net : ℝ)≤(h₁ : ℝ) := by
    exact_mod_cast hcount
  have hh := WeightedTradeoff.half_restriction_count_budget
    (N : ℝ) (N/2 : ℕ) (h₁ : ℝ) (ActualHalfRestriction.nonBraidCount net : ℝ)
    (Nat.cast_nonneg _) (half_arity_ge_real hN) (half_arity_rounding_real N) hwidth hc
  rw [←descFactorial_three_real ((by decide : 2≤520).trans (half_arity_ge hN))] at hh
  exact_mod_cast hh

/-- The scalar optimizer uses the original second width and the actual
half-model moment. The only remaining input here is the combinatorial count. -/
theorem tradeoff_of_actual_half_counting [NeZero N] (hN : 1040≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (model : NormalizedNetwork (N/2) h₁ h₂)
    (hmoment : 4*regularizedMoment model≤81*h₁)
    (hcount : NewCountingTradeoff.CountingPrerequisite 400
      ((N/2 : ℕ)-5) (regularizedMoment model : ℝ) (h₂ : ℝ)) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  apply NewCountingTradeoff.four_hundred_tradeoff (N : ℝ) (N/2 : ℕ)
    (h₁ : ℝ) (regularizedMoment model : ℝ) (h₂ : ℝ)
    (Nat.cast_nonneg _) (half_arity_ge_real hN) (half_arity_three_real hN)
  · exact_mod_cast one_le_regularizedMoment model
  · exact_mod_cast hmoment
  · exact actual_second_width_ge_one hN net hnet
  · exact hcount

theorem tradeoff_of_large_first_width [NeZero N] (hN : 1040≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (hwidth : (N : ℝ)^3<1000*(h₁ : ℝ)) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  apply NewCountingTradeoff.linear_absorption (N : ℝ) (h₁ : ℝ) (h₂ : ℝ)
    (by exact_mod_cast hN) hwidth
  have hh : (N : ℝ)≤2*(h₂ : ℝ) := by exact_mod_cast second_width_half net hnet
  linarith only [hh]

#print axioms half_model_count_budget
#print axioms tradeoff_of_actual_half_counting
#print axioms tradeoff_of_large_first_width
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
