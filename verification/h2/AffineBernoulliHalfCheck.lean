import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.AffineHalf
import MaxCaterpillar.Frontier.Constructions

/-! Raw-nine-array contract for the same-width half model and its two
all-first-row budgets. This checker invokes no Bernoulli theorem or H.
-/
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open NormalizedNetwork GrowingMatching GrowingMatching.AffineGeneralRows
open GrowingMatching.Bernoulli.Affine AffineSkipExtension ActualHalfRestriction
variable {N h₁ h₂ : ℕ}

example (C : ℕ) (hC : 1≤C) (hsize : 10000000000*(20*C)^2≤N/2)
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N) (θ : Fin h₂ → ℝ)
    (d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (hnet : letI := bernoulliOriginalDimension_neZero N C hC hsize;
      ∀ x : Point N,
        (∑ k,d k*relu ((∑ j,W k j*relu ((∑ i,A j i*x i)+b j))+
          (∑ i,U k i*x i)+θ k))+
        ((∑ j,B j*relu ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    letI := bernoulliHalfDimension_neZero N C hC hsize;
    ∃ S : Finset (Fin N),S.card=N/2 ∧ ∃ model : NormalizedNetwork (N/2) h₁ h₂,
      (∀ x,model.eval x=Maximum (N/2) x) ∧
      ((∀ j,∑ i,model.A j i=0) ∧ (∀ k,∑ i,model.U k i=0) ∧ (∑ i,model.L i)=1) ∧
      ((Finset.univ.filter fun j => 3≤(rowSupport (model.A j)).card).card : ℝ)≤
        ((20*C:ℕ):ℝ)^2*((N/2:ℕ):ℝ)^2 ∧
      (∑ j,((rowSupport (model.A j)).card.descFactorial 4 : ℝ))≤
        ((20*C:ℕ):ℝ)^2*((N/2:ℕ):ℝ)^2 := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact exists_affine_quadratic_half_budgets C hC hsize net hnet hwidth

-- The restriction underlying the stronger size regime is itself nonvacuous
-- at odd arity, independently of the large-size hypothesis or unknown H.
example : ∃ S : Finset (Fin 3),S.card=1 ∧ ∃ model : NormalizedNetwork 1 4 3,
    (∀ x,model.eval x=Maximum 1 x) ∧ model.TranslationNormalized ∧
    4*fourthMoment model≤81*4 ∧ 4*nonBraidCount model≤4 := by
  exact exists_affine_half_model (AffineSkipExtension.ofOrdinary maxThreeNet)
    (fun x => (eval_ofOrdinary maxThreeNet x).trans (maxThreeNet_eval x)) (by decide)

#check @exists_affine_quadratic_half_budgets
#print axioms exists_affine_quadratic_half_budgets
