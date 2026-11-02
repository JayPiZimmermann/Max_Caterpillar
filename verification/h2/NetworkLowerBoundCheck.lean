import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound

/-! Independent contracts for the ordinary-network headline. In particular,
the raw-array contract supplies no normalization, bias, support, certificate,
genericity or probabilistic premise. -/
set_option autoImplicit false
namespace NetworkLowerBoundCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction NetworkLowerBound

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) :=
  second_width_tradeoff hN net hnet

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (W₁ : Fin h₁ → Fin N → ℝ) (b₁ : Fin h₁ → ℝ)
    (W₂ : Fin h₂ → Fin h₁ → ℝ) (b₂ : Fin h₂ → ℝ)
    (w₃ : Fin h₂ → ℝ) (b₃ : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k,w₃ k*max 0 ((∑ j,W₂ k j*max 0 ((∑ i,W₁ j i*x i)+b₁ j))+b₂ k))+b₃
        =Finset.univ.sup' ⟨⟨0,Nat.pos_of_ne_zero (NeZero.ne N)⟩,Finset.mem_univ _⟩ x) :
    (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  let net : Network N h₁ h₂ := ⟨W₁,b₁,W₂,b₂,w₃,b₃⟩
  exact second_width_tradeoff hN net hmax

example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (hwidth : (h₁ : ℝ)≤(N : ℝ)^2) :
    (1/400000000 : ℝ)*(N : ℝ)^2≤(h₂ : ℝ) :=
  second_width_quadratic hN net hnet hwidth

-- A genuine ordinary network satisfies the headline's hypotheses at the
-- boundary arity. This uses the independently proved caterpillar construction.
example : ∃ net : Network 1040 (firstWidth 1040) (secondWidth 1040),
    (∀ x,net.eval x=Maximum 1040 x) ∧
    (1/400000000 : ℝ)*min ((1040 : ℝ)^2)
      ((1040 : ℝ)^4/(firstWidth 1040 : ℝ))≤(secondWidth 1040 : ℝ) := by
  obtain ⟨net,hmax,_hzero,_hweights⟩ := caterpillar_net 1040
  exact ⟨net,hmax,second_width_tradeoff (by decide) net hmax⟩

#check @second_width_tradeoff
#check @second_width_quadratic
#print axioms actual_neuron_event_cover
#print axioms model_counting_of_coefficients
#print axioms half_model_count_budget
#print axioms actual_network_tradeoff_of_coefficients
#print axioms second_width_tradeoff
#print axioms second_width_quadratic
end NetworkLowerBoundCheck
