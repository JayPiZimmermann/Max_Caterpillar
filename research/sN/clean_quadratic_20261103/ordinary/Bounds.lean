import research.sN.overnight_20261103.constants.tradeoff_theta.Scaled

/-!
Ordinary two-hidden-layer networks, with arbitrary real weights and biases.

The public statements use the canonical six-parameter `Network`: there are
no input-to-second-hidden, input-to-output, or first-hidden-to-output connections.
The explicit bound is a specialization of the stronger verified theorem.
The existential theorem below currently reuses that proof; it does not claim
an independent simplification of the five-input obstruction or event count.
-/
set_option autoImplicit false
namespace MaxCaterpillar.CleanQuadratic.Ordinary
open Frontier.RandomRestriction
open AffineSkipExtension

variable {N h₁ h₂ : ℕ} [NeZero N]

/-- The explicit constant for ordinary biased networks and scales at least one. -/
theorem explicit_quadratic_ge_one (hN : 3 ≤ N) (net : Network N h₁ h₂)
    (C : ℝ) (hC : 1 ≤ C)
    (hmax : ∀ x, net.eval x = Maximum N x)
    (hwidth : (h₁ : ℝ) ≤ C * (N : ℝ)^2) :
    (N : ℝ)^2 / (175000 * C) ≤ (h₂ : ℝ) := by
  exact OvernightConstants.TradeoffTheta.affine_scaled hN (ofOrdinary net) C hC
    (fun x => (eval_ofOrdinary net x).trans (hmax x)) hwidth

/-- The explicit constant for every positive first-width scale. All hidden
and output biases remain unrestricted; exactness holds on every real input. -/
theorem explicit_quadratic (hN : 3 ≤ N) (net : Network N h₁ h₂)
    (C : ℝ) (_hC : 0 < C)
    (hmax : ∀ x, net.eval x = Maximum N x)
    (hwidth : (h₁ : ℝ) ≤ C * (N : ℝ)^2) :
    (N : ℝ)^2 / (175000 * max 1 C) ≤ (h₂ : ℝ) := by
  apply explicit_quadratic_ge_one hN net (max 1 C) (le_max_left _ _) hmax
  exact hwidth.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

/-- One absolute positive constant works for every dimension, both hidden
widths, every positive scale, and every ordinary biased exact MAX network.
This proof is presently a corollary of the explicit verified estimate. -/
theorem exists_uniform_quadratic_constant :
    ∃ c : ℝ, 0 < c ∧
      ∀ {N h₁ h₂ : ℕ} [NeZero N], 3 ≤ N →
        ∀ (net : Network N h₁ h₂) (C : ℝ), 0 < C →
          (∀ x, net.eval x = Maximum N x) →
          (h₁ : ℝ) ≤ C * (N : ℝ)^2 →
          c * (N : ℝ)^2 / max 1 C ≤ (h₂ : ℝ) := by
  refine ⟨1 / 175000, by norm_num, ?_⟩
  intro N h₁ h₂ _ hN net C hC hmax hwidth
  have h := explicit_quadratic hN net C hC hmax hwidth
  convert h using 1
  ring

/-- The usual asymptotic formulation: each fixed positive quadratic-width
coefficient admits a positive quadratic lower-bound coefficient. -/
theorem exists_quadratic_constant_for_scale (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {N h₁ h₂ : ℕ} [NeZero N], 3 ≤ N →
        ∀ net : Network N h₁ h₂,
          (∀ x, net.eval x = Maximum N x) →
          (h₁ : ℝ) ≤ C * (N : ℝ)^2 →
          c * (N : ℝ)^2 ≤ (h₂ : ℝ) := by
  obtain ⟨a, ha, h⟩ := exists_uniform_quadratic_constant
  have hscale : 0 < max (1 : ℝ) C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨a / max 1 C, div_pos ha hscale, ?_⟩
  intro N h₁ h₂ _ hN net hmax hwidth
  have hh := h hN net C hC hmax hwidth
  convert hh using 1
  ring

#check @explicit_quadratic_ge_one
#check @explicit_quadratic
#check @exists_uniform_quadratic_constant
#check @exists_quadratic_constant_for_scale
#print axioms explicit_quadratic_ge_one
#print axioms explicit_quadratic
#print axioms exists_uniform_quadratic_constant
#print axioms exists_quadratic_constant_for_scale
end MaxCaterpillar.CleanQuadratic.Ordinary
