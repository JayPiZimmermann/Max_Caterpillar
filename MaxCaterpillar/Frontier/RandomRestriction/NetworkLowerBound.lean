import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Transfer
import MaxCaterpillar.Frontier.StarCertificate.StarObstruction

/-! # A quadratic second-width tradeoff for ordinary MAX networks

All parameters and biases are arbitrary real numbers. The input is the
ordinary two-hidden-layer network and its identity on every real input.
The finite star certificate and actual-network counting estimates are proved
dependencies, rather than assumptions of either theorem below.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
variable {N h₁ h₂ : ℕ}

/-- Every ordinary exact MAX network with N≥1040 satisfies the second-width
tradeoff. Positivity of the input arity is derived from the numeric bound. -/
theorem second_width_tradeoff (hN : 1040≤N) (net : Network N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt
      (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,net.eval x=Maximum N x) →
      (1/400000000 : ℝ)*min ((N : ℝ)^2) ((N : ℝ)^4/(h₁ : ℝ))≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  exact actual_network_tradeoff_of_coefficients StarCertificate.starAnova_all_real hN net hnet

/-- In particular, at most N² first-hidden-layer neurons force a quadratic
number of second-hidden-layer neurons, with an explicit uniform constant. -/
theorem second_width_quadratic (hN : 1040≤N) (net : Network N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt
      (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,net.eval x=Maximum N x) → (h₁ : ℝ)≤(N : ℝ)^2 →
      (1/400000000 : ℝ)*(N : ℝ)^2≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet hwidth
  have hpos : (0 : ℝ)<h₁ := by
    have hh : (1 : ℝ)≤h₁ := by
      exact_mod_cast ActualHalfRestriction.actual_first_width_pos net hnet
    linarith only [hh]
  have hdiv : (N : ℝ)^2≤(N : ℝ)^4/(h₁ : ℝ) := by
    apply (le_div_iff hpos).mpr
    calc
      (N : ℝ)^2*(h₁ : ℝ)≤(N : ℝ)^2*(N : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hwidth (sq_nonneg _)
      _ = (N : ℝ)^4 := by ring
  have hh := second_width_tradeoff hN net hnet
  rwa [min_eq_left hdiv] at hh

#print axioms second_width_tradeoff
#print axioms second_width_quadratic
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
