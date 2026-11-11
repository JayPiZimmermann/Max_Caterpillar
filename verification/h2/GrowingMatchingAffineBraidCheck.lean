import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineBraid
import MaxCaterpillar.Frontier.Constructions

/-! Raw nine-array contract: the only structural premise is H(4q+1,q).
No normalized model, analytic estimate, or sample-space bound is supplied.
-/
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open NormalizedNetwork GrowingMatching GrowingMatching.AffineBraid
open AffineSkipExtension
variable {N h₁ h₂ : ℕ}

example (q : ℕ) (hq : 1≤q) (hsize : 160000*q^2≤N)
    (H : LocalMatchingObstruction (4*q+1) q)
    (A : Fin h₁ → Point N) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Point N) (θ : Fin h₂ → ℝ)
    (d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ) (L : Point N) (β : ℝ)
    (hnet : letI := BraidCorollary.braidDimension_neZero N q hq hsize;
      ∀ x : Point N,
        (∑ k,d k*relu ((∑ j,W k j*relu ((∑ i,A j i*x i)+b j))+
          (∑ i,U k i*x i)+θ k))+
        ((∑ j,B j*relu ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x)
    (hbraid : ∀ j,(∑ i,A j i)=0 →
      (Finset.univ.filter fun i => A j i≠0).card≤2) :
    (23/25:ℝ)*4^q≤(h₂:ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  exact conditional_affine_braid_integer_q_lower_bound q hq hsize H net hnet hbraid

example (net : AffineSkipNetwork N h₁ h₂)
    (hbraid : ∀ j,(∑ i,net.A j i)=0 →
      (Finset.univ.filter fun i => net.A j i≠0).card≤2) :
    ∀ j,(Finset.univ.filter fun i => (normalizedModel net).A j i≠0).card≤2 :=
  normalizedModel_support_le_two net hbraid

-- A dense first covector with nonzero sum and nonzero bias is allowed by
-- the original braid condition and is actually removed by normalization.
def denseBiasedWitness : AffineSkipNetwork 3 1 0 where
  A := fun _ _ => 1
  b := fun _ => 7
  W := fun k => Fin.elim0 k
  U := fun k => Fin.elim0 k
  θ := fun k => Fin.elim0 k
  d := fun k => Fin.elim0 k
  B := fun _ => 0
  L := 0
  β := 0

example : BraidFirstLayer denseBiasedWitness := by
  intro j hj
  have : (3:ℝ)=0 := by simpa [denseBiasedWitness,Fin.sum_univ_succ] using hj
  norm_num at this

example : (normalizedModel denseBiasedWitness).A 0=0 := by
  rw [normalizedModel_first_row]
  simp [denseBiasedWitness]

-- The braid and exact-MAX conditions are jointly nonvacuous: this is the
-- existing nonlinear MAX3 network, with no hypothesis on growing-order H.
example : (∀ x,AffineSkipExtension.eval (AffineSkipExtension.ofOrdinary maxThreeNet) x=Maximum 3 x) ∧
    BraidFirstLayer (AffineSkipExtension.ofOrdinary maxThreeNet) := by
  constructor
  · intro x
    exact (eval_ofOrdinary maxThreeNet x).trans (maxThreeNet_eval x)
  · intro j hj
    have hu : (Finset.univ : Finset (Fin 3))={0,1,2} := by decide
    fin_cases j <;>
      norm_num [AffineSkipExtension.ofOrdinary,maxThreeNet,rowSupport,Fin.sum_univ_succ,hu,
        Finset.filter_insert,Finset.filter_singleton] at hj ⊢
    all_goals decide

#check @conditional_affine_braid_integer_q_lower_bound
#print axioms normalizedModel_support_le_two
#print axioms conditional_affine_braid_integer_q_lower_bound
