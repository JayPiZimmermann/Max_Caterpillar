import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
import MaxCaterpillar.Frontier.Constructions

/-! Independent raw-array contract for the conditional general-row theorem.
All original first neurons are charged, including output-only rows.
-/
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open NormalizedNetwork GrowingMatching GrowingMatching.AffineGeneralRows
open AffineSkipExtension ActualHalfRestriction
variable {N n h₁ h₂ : ℕ}
local instance checkArityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

-- The numeral20, Nat floor N/2, both size hypotheses, total first-width
-- budget and all nine raw arrays are explicit in this contract.
example (C q : ℕ) (hC : 1≤C) (hq : 1≤q)
    (hsize : 8000*(20*C)^2≤N/2) (hcube : 1000*(20*C)^2*q^3≤N/2)
    (H : LocalMatchingObstruction (4*q+1) q)
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N) (θ : Fin h₂ → ℝ)
    (d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (hnet : letI := originalDimension_neZero N C hC hsize;
      ∀ x : Point N,
        (∑ k,d k*relu ((∑ j,W k j*relu ((∑ i,A j i*x i)+b j))+
          (∑ i,U k i*x i)+θ k))+
        ((∑ j,B j*relu ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    (1/2:ℝ)*(((N/2:ℕ):ℝ)/(400000*((20*C:ℕ):ℝ)*(q : ℝ)^2))^q≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact conditional_affine_quadratic_width_lower_bound C q hC hq hsize hcube H net hnet hwidth

example [NeZero N] [NeZero n] (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,AffineSkipExtension.eval net x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧
      ((∀ j,∑ i,model.A j i=0) ∧ (∀ k,∑ i,model.U k i=0) ∧ (∑ i,model.L i)=1) ∧
      4*(∑ j,if 3≤(rowSupport (model.A j)).card
        then (rowSupport (model.A j)).card^4 else 0)≤81*h₁ ∧
      4*(Finset.univ.filter fun j => 3≤(rowSupport (model.A j)).card).card≤h₁ :=
  exists_affine_half_model net hnet hpair

example (C : ℕ) (hC : 1≤C) (hn : 0<N/2) (hwidth : h₁≤C*N^2)
    (model : NormalizedNetwork (N/2) h₁ h₂)
    (hbudget : 4*fourthMoment model≤81*h₁) :
    fourthMoment model≤(20*C)^2*(N/2)^2 :=
  fourthMoment_le_quadratic_budget C hC hn hwidth model hbudget

-- Genuine odd arity: the half model computes MAX1 with the SAME (4,3)
-- hidden indices as the exact nonlinear MAX3 source. No input is merged.
example : ∃ S : Finset (Fin 3),S.card=1 ∧ ∃ model : NormalizedNetwork 1 4 3,
    (∀ x,model.eval x=Maximum 1 x) ∧ model.TranslationNormalized ∧
    4*fourthMoment model≤81*4 ∧ 4*nonBraidCount model≤4 := by
  exact exists_affine_half_model (AffineSkipExtension.ofOrdinary maxThreeNet)
    (fun x => (eval_ofOrdinary maxThreeNet x).trans (maxThreeNet_eval x)) (by decide)

-- A literal odd N and integer C sanity-check the scalar transfer separately
-- from the open structural premise; symbolic model statistics are retained.
example (model : NormalizedNetwork (7/2) 10 3)
    (hbudget : 4*fourthMoment model≤81*10) :
    fourthMoment model≤(20*1)^2*(7/2)^2 := by
  exact fourthMoment_le_quadratic_budget (N:=7) 1 (by decide) (by decide)
    (by decide : 10≤1*7^2) model hbudget

#check @conditional_affine_quadratic_width_lower_bound
#print axioms exists_normalized_half_model
#print axioms exists_affine_half_model
#print axioms fourthMoment_le_quadratic_budget
#print axioms general_rows_budgets_of_fourthMoment
#print axioms conditional_affine_quadratic_width_lower_bound
