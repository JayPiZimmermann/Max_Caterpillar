import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
import MaxCaterpillar.Frontier.StarCertificate.StarObstruction

/-! A feeding-only dictionary and tagged absorption of output-only terms.
These algebraic adapters preserve the exact original outer-neuron index. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
open BigOperators NormalizedNetwork
variable {N h₁ h₂ : ℕ}

noncomputable def core (net : NormalizedNetwork N h₁ h₂) : NormalizedNetwork N h₁ h₂ := by
  classical
  exact {net with A := fun j => if net.Feeding j then net.A j else 0,B := 0}

lemma weight_zero_of_not_feeding (net : NormalizedNetwork N h₁ h₂)
    (j : Fin h₁) (hj : ¬net.Feeding j) (k : Fin h₂) : net.W k j=0 := by
  by_contra hh
  exact hj ⟨k,hh⟩

theorem core_inner (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (x : Point N) :
    (core net).inner k x=net.inner k x := by
  classical
  unfold NormalizedNetwork.inner
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : net.Feeding j
  · simp only [core,if_pos hj]
  · simp only [core,if_neg hj,weight_zero_of_not_feeding net j hj k,zero_mul]

theorem core_normalized (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized) :
    (core net).TranslationNormalized := by
  classical
  refine ⟨?_,hn.2⟩
  intro j
  by_cases hj : net.Feeding j
  · simpa only [core,if_pos hj] using hn.1 j
  · simp only [core,if_neg hj,Pi.zero_apply,Finset.sum_const_zero]

theorem core_edgeWeight (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (a b : Fin N) :
    braidEdgeWeight (core net).A ((core net).W k) a b=braidEdgeWeight net.A (net.W k) a b := by
  classical
  unfold braidEdgeWeight braidEdgeRows
  rw [Finset.sum_filter,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : net.Feeding j
  · simp only [core,if_pos hj]
  · simp only [core,if_neg hj,weight_zero_of_not_feeding net j hj k,zero_mul,ite_self]

def outerEquiv (h₂ h₁ : ℕ) : Fin h₂ ⊕ Fin h₁ ≃ Fin (h₂+h₁) := finSumFinEquiv
def original (k : Fin h₂) : Fin (h₂+h₁) := outerEquiv h₂ h₁ (.inl k)
def auxiliary (j : Fin h₁) : Fin (h₂+h₁) := outerEquiv h₂ h₁ (.inr j)

noncomputable def absorb (net : NormalizedNetwork N h₁ h₂) : NormalizedNetwork N h₁ (h₂+h₁) where
  A := (core net).A
  U s := Sum.elim net.U net.A ((outerEquiv h₂ h₁).symm s)
  W s := Sum.elim net.W (fun _ => 0) ((outerEquiv h₂ h₁).symm s)
  L := net.L
  B := 0
  d s := Sum.elim net.d net.B ((outerEquiv h₂ h₁).symm s)

theorem absorb_inner_original (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (x : Point N) :
    (absorb net).inner (original k) x=net.inner k x := by
  simpa only [NormalizedNetwork.inner,absorb,original,Equiv.symm_apply_apply,Sum.elim_inl,core] using core_inner net k x

theorem absorb_inner_auxiliary (net : NormalizedNetwork N h₁ h₂) (j : Fin h₁) (x : Point N) :
    (absorb net).inner (auxiliary j) x=lin (net.A j) x := by
  simp only [NormalizedNetwork.inner,absorb,auxiliary,Equiv.symm_apply_apply,Sum.elim_inr,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]

theorem absorb_eval (net : NormalizedNetwork N h₁ h₂) (x : Point N) :
    (absorb net).eval x=net.eval x := by
  have he : (∑ s,(absorb net).d s*relu ((absorb net).inner s x))=
      (∑ k,net.d k*relu (net.inner k x))+(∑ j,net.B j*relu (lin (net.A j) x)) := by
    calc
      _ = ∑ s : Fin h₂ ⊕ Fin h₁,
          (absorb net).d (outerEquiv h₂ h₁ s)*relu ((absorb net).inner (outerEquiv h₂ h₁ s) x) :=
        (Fintype.sum_equiv (outerEquiv h₂ h₁) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [Fintype.sum_sum_type]
        apply congrArg₂ (fun a b : ℝ => a+b)
        · apply Finset.sum_congr rfl
          intro k _
          change (absorb net).d (original k)*relu ((absorb net).inner (original k) x)=_
          rw [absorb_inner_original]
          simp only [absorb,original,Equiv.symm_apply_apply,Sum.elim_inl]
        · apply Finset.sum_congr rfl
          intro j _
          change (absorb net).d (auxiliary j)*relu ((absorb net).inner (auxiliary j) x)=_
          rw [absorb_inner_auxiliary]
          simp only [absorb,auxiliary,Equiv.symm_apply_apply,Sum.elim_inr]
  change lin net.L x+(∑ j,(0 : ℝ)*relu (lin ((core net).A j) x))+
    (∑ s,(absorb net).d s*relu ((absorb net).inner s x))=net.eval x
  rw [he]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,NormalizedNetwork.eval]
  ring

theorem absorb_normalized (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized) :
    (absorb net).TranslationNormalized := by
  refine ⟨(core_normalized net hn).1,?_,hn.2.2⟩
  intro s
  rcases hs : (outerEquiv h₂ h₁).symm s with k|j
  · simpa only [absorb,hs,Sum.elim_inl] using hn.2.1 k
  · simpa only [absorb,hs,Sum.elim_inr] using hn.1 j

theorem absorb_support_le_two (net : NormalizedNetwork N h₁ h₂)
    (hs : ∀ j,net.Feeding j → (rowSupport (net.A j)).card≤2) :
    ∀ j,(rowSupport ((absorb net).A j)).card≤2 := by
  classical
  intro j
  by_cases hj : net.Feeding j
  · simpa only [absorb,core,if_pos hj] using hs j hj
  · simp only [absorb,core,if_neg hj,rowSupport_zero,Finset.card_empty,Nat.zero_le]

theorem absorb_original_edgeWeight (net : NormalizedNetwork N h₁ h₂)
    (k : Fin h₂) (a b : Fin N) :
    braidEdgeWeight (absorb net).A ((absorb net).W (original k)) a b=
      braidEdgeWeight net.A (net.W k) a b := by
  simpa only [absorb,original,Equiv.symm_apply_apply,Sum.elim_inl,core] using core_edgeWeight net k a b

theorem absorb_auxiliary_edgeWeight (net : NormalizedNetwork N h₁ h₂)
    (j : Fin h₁) (a b : Fin N) :
    braidEdgeWeight (absorb net).A ((absorb net).W (auxiliary j)) a b=0 := by
  simp only [braidEdgeWeight,absorb,auxiliary,Equiv.symm_apply_apply,Sum.elim_inr,
    Pi.zero_apply,zero_mul,Finset.sum_const_zero,neg_zero]

#print axioms core_inner
#print axioms core_edgeWeight
#print axioms absorb_eval
#print axioms absorb_normalized
end MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
