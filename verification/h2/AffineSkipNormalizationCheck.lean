import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization
import MaxCaterpillar.Frontier.Constructions

/-! Independent contracts spell out the original nine arrays, all-real
evaluation, exact retained coefficients and feeding lineage. -/
set_option autoImplicit false
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
variable {N h₁ h₂ : ℕ}

example [NeZero N]
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N) (θ : Fin h₂ → ℝ)
    (d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (h : ∀ x : Point N,
      (∑ k,d k*relu ((∑ j,W k j*relu ((∑ i,A j i*x i)+b j))+
        (∑ i,U k i*x i)+θ k))+
      ((∑ j,B j*relu ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x) :
    ∃ model : NormalizedNetwork N h₁ h₂,
      (∀ x : Point N,
        (∑ i,model.L i*x i)+(∑ j,model.B j*relu (∑ i,model.A j i*x i))+
        (∑ k,model.d k*relu ((∑ i,model.U k i*x i)+
          ∑ j,model.W k j*relu (∑ i,model.A j i*x i)))=Maximum N x) ∧
      ((∀ j,∑ i,model.A j i=0) ∧ (∀ k,∑ i,model.U k i=0) ∧ (∑ i,model.L i)=1) ∧
      (∀ j,model.A j=if b j=0 ∧ (∑ i,A j i)=0 then A j else 0) ∧
      (∀ j,(∃ k,model.W k j≠0)→∃ k,W k j≠0) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact exists_normalizedModel net h

example (net : AffineSkipNetwork N h₁ h₂) (x : Point N) :
    ∃ ε : ℝ,0<ε ∧ eval net (ε • x)=eval net 0+ε*(homogeneousModel net).eval x :=
  homogeneousModel_exact_direction net x

example (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁) :
    (normalizedModel net).A j=
      if net.b j=0 ∧ (∑ i,net.A j i)=0 then net.A j else 0 :=
  normalizedModel_first_row net j

example (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁)
    (hj : ∃ k,(normalizedModel net).W k j≠0) : ∃ k,net.W k j≠0 :=
  normalizedModel_feeding_original net j hj

/-- Genuine affine biases, input skips, and an original feeding coefficient
are present, while the output is the one-coordinate maximum. -/
def biasedSkipWitness : AffineSkipNetwork 1 1 1 where
  A := fun _ _ => 2
  b := fun _ => 7
  W := fun _ _ => 5
  U := fun _ _ => 3
  θ := fun _ => -2
  d := fun _ => 0
  B := fun _ => 0
  L := fun _ => 1
  β := 0

lemma biasedSkipWitness_max (x : Point 1) : eval biasedSkipWitness x=Maximum 1 x := by
  have hm : Maximum 1 x=x 0 := by
    apply Maximum_eq_of x (x 0) 0 rfl
    intro i
    fin_cases i
    exact le_refl _
  rw [hm]
  simp [eval,outputSkip,biasedSkipWitness,Fin.sum_univ_one]

example : ∃ model : NormalizedNetwork 1 1 1,
    (∀ x,model.eval x=Maximum 1 x) ∧ model.TranslationNormalized ∧
    (∀ j,model.A j=if biasedSkipWitness.b j=0 ∧ (∑ i,biasedSkipWitness.A j i)=0
      then biasedSkipWitness.A j else 0) ∧
    (∀ j,model.Feeding j→∃ k,biasedSkipWitness.W k j≠0) :=
  exists_normalizedModel biasedSkipWitness biasedSkipWitness_max

example : (normalizedModel biasedSkipWitness).A 0=0 := by
  rw [normalizedModel_first_row]
  simp [biasedSkipWitness]

-- A genuinely nonlinear target also satisfies the complete normalization
-- contract, with the original first and second widths exactly (4,3).
example : ∃ model : NormalizedNetwork 3 4 3,
    (∀ x,model.eval x=Maximum 3 x) ∧ model.TranslationNormalized ∧
    (∀ j,model.A j=if (ofOrdinary maxThreeNet).b j=0 ∧
      (∑ i,(ofOrdinary maxThreeNet).A j i)=0 then (ofOrdinary maxThreeNet).A j else 0) ∧
    (∀ j,model.Feeding j→∃ k,(ofOrdinary maxThreeNet).W k j≠0) := by
  exact exists_normalizedModel (ofOrdinary maxThreeNet)
    (fun x => (eval_ofOrdinary maxThreeNet x).trans (maxThreeNet_eval x))

#check @exists_normalizedModel
#print axioms homogeneousExtension_eval
#print axioms homogeneousModel_exact_direction
#print axioms homogeneousModel_computes_max
#print axioms homogeneousModel_first_row
#print axioms homogeneousModel_feeding_original
#print axioms diagonalModel_computes_max
#print axioms normalizedModel_computes_max
#print axioms normalizedModel_translation_normalized
#print axioms normalizedModel_first_row
#print axioms normalizedModel_feeding_original
#print axioms exists_normalizedModel
#print axioms biasedSkipWitness_max
