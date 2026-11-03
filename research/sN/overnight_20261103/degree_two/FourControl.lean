import research.sN.overnight_20261103.degree_two.GlobalComponents
import MaxCaterpillar.Frontier.Constructions

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo.Check
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork

lemma lin_unit_sub {n : ℕ} (i j : Fin n) (x : Point n) :
    lin (unitVec i-unitVec j) x=x i-x j := by
  simp [lin,unitVec,sub_mul,Finset.sum_sub_distrib]

/-- A literal four-input exact model with two first units and one second unit. -/
def fourNet : NormalizedNetwork 4 2 1 where
  A := fun j => if j=0 then unitVec 0-unitVec 1 else unitVec 2-unitVec 3
  U := fun _ => unitVec 1-unitVec 3
  W := fun _ j => if j=0 then 1 else -1
  L := unitVec 3
  B := fun j => if j=0 then 0 else 1
  d := fun _ => 1

lemma fourNet_normalized : fourNet.TranslationNormalized := by
  constructor
  · intro j
    by_cases hj : j=0 <;> simp [fourNet,hj,unitVec,Finset.sum_sub_distrib]
  constructor
  · intro k
    simp [fourNet,unitVec,Finset.sum_sub_distrib]
  · simp [fourNet,unitVec]

lemma root_support_card {n : ℕ} (a b : Fin n) :
    (rowSupport (unitVec a-unitVec b)).card≤2 := by
  have hs : rowSupport (unitVec a-unitVec b)⊆{a,b} := by
    intro i hi
    by_cases ha : i=a
    · simp [ha]
    by_cases hb : i=b
    · simp [hb]
    · have hz : (unitVec a-unitVec b) i=0 := by simp [unitVec,ha,hb]
      exact False.elim (((mem_rowSupport _ _).mp hi) hz)
  exact (Finset.card_le_of_subset hs).trans (by by_cases h:a=b <;> norm_num [h])

lemma fourNet_braid : ∀ j,(rowSupport (fourNet.A j)).card≤2 := by
  intro j
  by_cases hj : j=0
  · simpa [fourNet,hj] using root_support_card (0:Fin 4) 1
  · simpa [fourNet,hj] using root_support_card (2:Fin 4) 3

lemma lin_unit_left {n : ℕ} (i : Fin n) (x : Point n) : lin (unitVec i) x=x i := by
  simp [lin,unitVec]

lemma fourNet_max (x : Point 4) : fourNet.eval x=Maximum 4 x := by
  simp only [eval,NormalizedNetwork.inner,fourNet,Fin.sum_univ_two,
    Fin.sum_univ_one,ite_true,show (1:Fin 2)≠0 from by decide,ite_false,
    zero_mul,one_mul,neg_one_mul,zero_add,lin_unit_sub,lin_unit_left]
  rw [Maximum_four]
  have h01 : x 1+relu (x 0-x 1)=max (x 0) (x 1) := by
    rw [add_comm,relu_sub_add,max_comm]
  have h23 : x 3+relu (x 2-x 3)=max (x 2) (x 3) := by
    rw [add_comm,relu_sub_add,max_comm]
  have he : x 1-x 3+(relu (x 0-x 1)+ -relu (x 2-x 3))=
      max (x 0) (x 1)-max (x 2) (x 3) := by
    linarith only [h01,h23]
  rw [he,h23,add_comm,relu_sub_add,max_comm]

#print axioms fourNet_normalized
#print axioms fourNet_braid
#print axioms fourNet_max
end MaxCaterpillar.Overnight.DegreeTwo.Check
