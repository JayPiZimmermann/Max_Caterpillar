import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows.Budgets

/-! # A conditional general-row bound for original affine-skip MAX networks

The original TOTAL first width is at most C N², with integer C≥1. The
normalization, one actual half restriction, and both all-first support
budgets are proved. No braid condition or support assumption is imposed.
The growing-order local obstruction H(4q+1,q) remains explicit.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
open BigOperators NormalizedNetwork ActualHalfRestriction AffineSkipExtension
variable {N h₁ h₂ : ℕ}

local instance arityNeZero (q : ℕ) : NeZero (Parameters.braidArity q) :=
  ⟨Nat.succ_ne_zero (4*q)⟩

/-- Finite conditional superpolynomial route for arbitrary original first
covectors, arbitrary affine skips and biases, and TOTAL h1≤C N².
Here n=floor(N/2) and d=20C; the original second width is unchanged. -/
theorem conditional_affine_quadratic_width_lower_bound
    (C q : ℕ) (hC : 1≤C) (hq : 1≤q)
    (hsize : 8000*(quadraticParameter C)^2≤N/2)
    (hcube : 1000*(quadraticParameter C)^2*q^3≤N/2)
    (H : LocalMatchingObstruction (Parameters.braidArity q) q)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalDimension_neZero N C hC hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    (1/2:ℝ)*(((N/2:ℕ):ℝ)/(400000*(quadraticParameter C : ℝ)*(q : ℝ)^2))^q≤(h₂:ℝ) := by
  letI := originalDimension_neZero N C hC hsize
  letI := halfDimension_neZero N C hC hsize
  obtain ⟨S,_hS,model,hmax,hnorm,hmoment,_hcount⟩ :=
    exists_affine_half_model (n:=N/2) net hnet (by linarith only [Nat.mul_div_le N 2])
  have hbudget := fourthMoment_le_quadratic_budget C hC
    (half_positive N C hC hsize) hwidth model hmoment
  obtain ⟨hM,hL⟩ := general_rows_budgets_of_fourthMoment C model hbudget
  exact conditional_general_rows (N/2) (quadraticParameter C) q
    (quadraticParameter_pos C hC) hq hsize hcube H model hnorm hmax hM hL

#check @conditional_affine_quadratic_width_lower_bound
#print axioms conditional_affine_quadratic_width_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
