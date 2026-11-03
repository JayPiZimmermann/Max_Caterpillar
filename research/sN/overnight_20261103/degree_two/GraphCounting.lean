import Mathlib

/-! Finite counting for sets with at most two connected pieces.
The graph-specific connected-set bound is supplied separately. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators
variable {α : Type*} [DecidableEq α]

/-- Complementary positive-size pieces, retaining their order. -/
def orderedSplits (C : ℕ → Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  (Finset.Ico 1 m).biUnion fun k => (C k).product (C (m-k))

lemma orderedSplits_card_le (C : ℕ → Finset (Finset α)) (m B : ℕ)
    (hC : ∀ k, 0<k → (C k).card≤B) :
    (orderedSplits C m).card≤(m-1)*B^2 := by
  calc
    (orderedSplits C m).card ≤ ∑ k in Finset.Ico 1 m, ((C k).product (C (m-k))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k in Finset.Ico 1 m, B^2 := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1,hkm⟩ := Finset.mem_Ico.mp hk
      have hprod : ((C k).product (C (m-k))).card =
          (C k).card * (C (m-k)).card := Finset.card_product (C k) (C (m-k))
      rw [hprod,pow_two]
      exact Nat.mul_le_mul (hC k hk1) (hC (m-k) (Nat.sub_pos_of_lt hkm))
    _ = (m-1)*B^2 := by simp

/-- A lower fiber bound needs only two distinct displayed preimages. -/
lemma two_mul_card_le_of_two_preimages {β : Type*} [DecidableEq β]
    (D : Finset α) (E : Finset β) (f : α→β)
    (h : ∀ y∈E, ∃ p∈D, ∃ q∈D, p≠q ∧ f p=y ∧ f q=y) :
    2*E.card≤D.card := by
  classical
  let D' := D.filter fun p => f p∈E
  have htwo : ∀ y∈E, 2≤(D'.filter fun p => f p=y).card := by
    intro y hy
    obtain ⟨p,hp,q,hq,hpq,hpy,hqy⟩ := h y hy
    have hsub : ({p,q} : Finset α)⊆D'.filter (fun p => f p=y) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp [D',hp,hpy,hy]
      · have hzq := Finset.mem_singleton.mp hz
        subst z
        simp [D',hq,hqy,hy]
    have hc := Finset.card_le_of_subset hsub
    simpa [hpq] using hc
  exact (Finset.mul_card_image_le_card_of_maps_to
    (fun p hp => (Finset.mem_filter.mp hp).2) 2 htwo).trans (Finset.card_filter_le D _)

/-- Two nonempty disjoint pieces give two distinct ordered decompositions. -/
lemma two_pieces_card_bound (C : ℕ→Finset (Finset α)) (E : Finset (Finset α))
    (m B : ℕ) (hC : ∀ k, 0<k → (C k).card≤B)
    (hE : ∀ S∈E, ∃ A B : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      A∈C A.card ∧ B∈C B.card ∧ S=A∪B ∧ S.card=m) :
    2*E.card≤(m-1)*B^2 := by
  have hpre : ∀ S∈E, ∃ p∈orderedSplits C m, ∃ q∈orderedSplits C m,
      p≠q ∧ p.1∪p.2=S ∧ q.1∪q.2=S := by
    intro S hS
    obtain ⟨A,B,hA,hB,hd,hAC,hBC,hS,hcard⟩ := hE S hS
    have hAp : 0<A.card := Finset.card_pos.mpr hA
    have hBp : 0<B.card := Finset.card_pos.mpr hB
    have hsum : A.card+B.card=m := by rw [←Finset.card_union_eq hd,←hS,hcard]
    have hAm : A.card<m := by linarith
    have hBm : B.card<m := by linarith
    have hmA : m-A.card=B.card := by rw [←hsum,Nat.add_sub_cancel_left]
    have hmB : m-B.card=A.card := by rw [←hsum,Nat.add_sub_cancel]
    have hAB : A≠B := by
      intro heq
      obtain ⟨b,hb⟩ := hB
      exact (Finset.disjoint_left.mp hd) (heq.symm ▸ hb) hb
    refine ⟨(A,B),?_,(B,A),?_,?_,hS.symm,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨A.card,Finset.mem_Ico.mpr ⟨hAp,hAm⟩,?_⟩
      rw [hmA]
      exact Finset.mem_product.mpr ⟨hAC,hBC⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨B.card,Finset.mem_Ico.mpr ⟨hBp,hBm⟩,?_⟩
      rw [hmB]
      exact Finset.mem_product.mpr ⟨hBC,hAC⟩
    · intro heq
      exact hAB (congrArg Prod.fst heq)
    · rw [Finset.union_comm]
      exact hS.symm
  exact (two_mul_card_le_of_two_preimages (orderedSplits C m) E
    (fun p => p.1∪p.2) hpre).trans (orderedSplits_card_le C m B hC)

/-- If every counted set is connected or has a disjoint two-piece
representation, a uniform connected-piece budget gives the full capacity. -/
theorem at_most_two_capacity (C : ℕ→Finset (Finset α)) (E : Finset (Finset α))
    (m N : ℕ) (hm : 0<m) (hC : ∀ k, 0<k → (C k).card≤2*N)
    (hE : ∀ S∈E, S∈C m ∨ ∃ A B : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      A∈C A.card ∧ B∈C B.card ∧ S=A∪B ∧ S.card=m) :
    E.card≤2*N+2*(m-1)*N^2 := by
  classical
  let D := E.filter fun S => S∉C m
  have hD : 2*D.card≤(m-1)*(2*N)^2 := by
    apply two_pieces_card_bound C D m (2*N) hC
    intro S hS
    obtain ⟨hSE,hSC⟩ := Finset.mem_filter.mp hS
    exact (hE S hSE).resolve_left hSC
  have hsub : E⊆C m∪D := by
    intro S hS
    by_cases hSC : S∈C m
    · exact Finset.mem_union.mpr (Or.inl hSC)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hS,hSC⟩))
  have hcard := (Finset.card_le_of_subset hsub).trans (Finset.card_union_le (C m) D)
  have hCm := hC m hm
  have hD' : D.card≤2*(m-1)*N^2 := by nlinarith only [hD]
  exact hcard.trans (Nat.add_le_add hCm hD')

#print axioms at_most_two_capacity
end MaxCaterpillar.Overnight.DegreeTwo
