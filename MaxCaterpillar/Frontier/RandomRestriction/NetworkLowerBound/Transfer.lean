import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Counting

/-! # Transfer from the finite coefficient certificate to ordinary networks -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
variable {N h₁ h₂ : ℕ}

/-- All geometric, genericity, support-budget and counting hypotheses are
derived from the actual network. The finite star identity is isolated here
so that the public theorem can discharge it with its independent certificate. -/
theorem actual_network_tradeoff_of_coefficients [NeZero N]
    (hcoeff : StructuralWitness.ClosedStarCoefficientIdentity)
    (hN : 1040≤N) (net : Network N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  by_cases hwidth : 1000*(h₁ : ℝ)≤(N : ℝ)^3
  · letI : NeZero (N/2) := ⟨Nat.ne_of_gt
      (Nat.div_pos (le_trans (by decide : 2≤1040) hN) (by decide : 0<2))⟩
    obtain ⟨S,_hS,model,hmax,hnorm,_hraw,hM,hreg⟩ :=
      ActualHalfRestriction.exists_actual_half_model hN net hnet
    have hbudget := half_model_count_budget hN hwidth model hM
    have hcount := model_counting_of_coefficients hcoeff model hnorm hmax
      (half_arity_ge hN) hbudget
    exact tradeoff_of_actual_half_counting hN net hnet model hreg hcount
  · exact tradeoff_of_large_first_width hN net hnet (lt_of_not_ge hwidth)

#print axioms actual_network_tradeoff_of_coefficients
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
