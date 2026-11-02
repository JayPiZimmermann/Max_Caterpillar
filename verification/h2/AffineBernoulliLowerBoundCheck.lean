import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.AffineLowerBound

/-! Independent original-array contract for the conditional sqrt bound.
The arity, matching order, floor and every numerical constant are explicit.
There is no normalized-model, probability, survival, or rank premise.
-/
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Bernoulli GrowingMatching.Bernoulli.Affine
open AffineSkipExtension
variable {N h₁ h₂ : ℕ}
local instance checkArityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

example (C : ℕ) (hC : 1≤C) (hsize : 10000000000*(20*C)^2≤N/2)
    (H : LocalMatchingObstruction
      (4*Nat.floor (Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))+1)
      (Nat.floor (Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))))
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N) (θ : Fin h₂ → ℝ)
    (outerCoeff : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (hnet : letI := bernoulliOriginalDimension_neZero N C hC hsize;
      ∀ x : Point N,
        (∑ k,outerCoeff k*relu ((∑ j,W k j*relu ((∑ i,A j i*x i)+b j))+
          (∑ i,U k i*x i)+θ k))+
        ((∑ j,B j*relu ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    (1/2:ℝ)*Real.exp (3*Real.sqrt ((N/2:ℕ):ℝ)/(160000*(C : ℝ)))≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,outerCoeff,B,L,β⟩
  exact conditional_affine_sqrt_lower_bound_explicit C hC hsize H net hnet hwidth

-- Symbolic floor identity only: no expensive concrete sqrt reduction or
-- numerical approximation appears in the proof or contract.
example (n d : ℕ) :
    Parameters.matchingOrder n d=Nat.floor (Real.sqrt (n : ℝ)/(8000*(d : ℝ))) :=
  matchingOrder_eq_sqrt_floor n d

#check @conditional_affine_sqrt_lower_bound_explicit
#print axioms exists_affine_quadratic_half_budgets
#print axioms matchingOrder_eq_sqrt_floor
#print axioms conditional_affine_sqrt_lower_bound
#print axioms conditional_affine_sqrt_lower_bound_explicit
