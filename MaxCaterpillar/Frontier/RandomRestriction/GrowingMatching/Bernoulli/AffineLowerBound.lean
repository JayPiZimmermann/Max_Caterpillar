import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.AffineHalf
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.LowerBound

/-! # Conditional square-root exponential bounds for raw affine MAX networks

The original total first width is at most C N². Arbitrary real first
covectors, biases, and affine skips are permitted. Normalization, a same-width
half model and both support budgets are derived. Only the displayed
growing-order local obstruction H remains a structural hypothesis.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Affine
open BigOperators NormalizedNetwork ActualHalfRestriction AffineSkipExtension AffineGeneralRows
variable {N h₁ h₂ : ℕ}

local instance explicitArityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

/-- The literal parameter's two divisions equal the displayed single
division, including zero denominators under Lean's field convention. -/
lemma matchingOrder_eq_sqrt_floor (n d : ℕ) :
    Parameters.matchingOrder n d=Nat.floor (Real.sqrt (n : ℝ)/(8000*(d : ℝ))) := by
  unfold Parameters.matchingOrder Parameters.bernoulliMean
  congr 1
  rw [div_div]
  congr 1
  ring

/-- The raw nine-array conditional Bernoulli result at original total
h1≤C N². Both hidden-layer widths remain the original indices. -/
theorem conditional_affine_sqrt_lower_bound (C : ℕ) (hC : 1≤C)
    (hsize : 10000000000*(quadraticParameter C)^2≤N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (quadraticParameter C))
      (Parameters.matchingOrder (N/2) (quadraticParameter C)))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := bernoulliOriginalDimension_neZero N C hC hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    (1/2:ℝ)*Real.exp (3*Real.sqrt ((N/2:ℕ):ℝ)/(8000*(quadraticParameter C : ℝ)))≤(h₂:ℝ) := by
  letI := bernoulliOriginalDimension_neZero N C hC hsize
  letI := bernoulliHalfDimension_neZero N C hC hsize
  obtain ⟨_S,_hS,model,hmax,hnorm,hM,hL⟩ :=
    exists_affine_quadratic_half_budgets C hC hsize net hnet hwidth
  exact conditional_sqrt_lower_bound (quadraticParameter_pos C hC) hsize H
    model hnorm hmax hM hL

/-- Fully explicit original-network statement. Set n=floor(N/2) and
q=floor(sqrt(n)/(160000 C)); the only unproved premise is H(4q+1,q).
This theorem does not establish that premise at growing q. -/
theorem conditional_affine_sqrt_lower_bound_explicit (C : ℕ) (hC : 1≤C)
    (hsize : 10000000000*(20*C)^2≤N/2)
    (H : LocalMatchingObstruction
      (4*Nat.floor (Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))+1)
      (Nat.floor (Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := bernoulliOriginalDimension_neZero N C hC hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    (1/2:ℝ)*Real.exp (3*Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))≤(h₂:ℝ) := by
  have hden : (8000:ℝ)*(quadraticParameter C : ℝ)=160000*(C : ℝ) := by
    simp only [quadraticParameter,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hq : Parameters.matchingOrder (N/2) (quadraticParameter C)=
      Nat.floor (Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ))) := by
    rw [matchingOrder_eq_sqrt_floor,hden]
  have hH : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (quadraticParameter C))
      (Parameters.matchingOrder (N/2) (quadraticParameter C)) := by
    simpa only [Parameters.minimumArity,hq] using H
  have hh := conditional_affine_sqrt_lower_bound C hC hsize hH net hnet hwidth
  simpa only [hden] using hh

#check @conditional_affine_sqrt_lower_bound_explicit
#print axioms matchingOrder_eq_sqrt_floor
#print axioms conditional_affine_sqrt_lower_bound
#print axioms conditional_affine_sqrt_lower_bound_explicit
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Affine
