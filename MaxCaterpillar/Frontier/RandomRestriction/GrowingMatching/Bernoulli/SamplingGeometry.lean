import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.SetRealization

/-! # Actual selected-set and complement enumerations for Bernoulli sampling

The enumerations are literal aliases of the existing faithful restriction
and actual dominant-gap complement embeddings. No distributional or local
structural conclusion is built into them. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
open BigOperators
variable {n : ℕ}

abbrev selectedCount (S : Finset (Fin n)) := S.card
abbrev tailCount (S : Finset (Fin n)) := ((Finset.univ : Finset (Fin n)) \ S).card

noncomputable def keep (S : Finset (Fin n)) : Fin (selectedCount S) ↪ Fin n :=
  NormalizedNetwork.selectedEmbedding S
noncomputable def tail (S : Finset (Fin n)) : Fin (tailCount S) ↪ Fin n :=
  DominantGap.complementEmbedding S

lemma keep_image (S : Finset (Fin n)) : Finset.univ.image (keep S)=S :=
  NormalizedNetwork.selectedEmbedding_image S
lemma tail_image (S : Finset (Fin n)) :
    Finset.univ.image (tail S)=(Finset.univ : Finset (Fin n)) \ S :=
  DominantGap.complementEmbedding_image S

lemma keep_mem (S : Finset (Fin n)) (i : Fin (selectedCount S)) : keep S i ∈ S :=
  (S.equivFin.symm i).property
lemma tail_mem_complement (S : Finset (Fin n)) (j : Fin (tailCount S)) :
    tail S j ∈ (Finset.univ : Finset (Fin n)) \ S :=
  ((Finset.univ \ S).equivFin.symm j).property
lemma tail_not_mem (S : Finset (Fin n)) (j : Fin (tailCount S)) : tail S j ∉ S :=
  (Finset.mem_sdiff.mp (tail_mem_complement S j)).2

noncomputable def keepIndex (S : Finset (Fin n)) (v : Fin n) (hv : v∈S) :
    Fin (selectedCount S) := S.equivFin ⟨v,hv⟩
noncomputable def tailIndex (S : Finset (Fin n)) (v : Fin n) (hv : v∉S) :
    Fin (tailCount S) :=
  (Finset.univ \ S).equivFin ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩

lemma keep_keepIndex (S : Finset (Fin n)) (v : Fin n) (hv : v∈S) :
    keep S (keepIndex S v hv)=v := by
  exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨v,hv⟩)
lemma tail_tailIndex (S : Finset (Fin n)) (v : Fin n) (hv : v∉S) :
    tail S (tailIndex S v hv)=v := by
  exact congrArg Subtype.val ((Finset.univ \ S).equivFin.symm_apply_apply
    ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩)
lemma keepIndex_keep (S : Finset (Fin n)) (i : Fin (selectedCount S)) :
    keepIndex S (keep S i) (keep_mem S i)=i := S.equivFin.apply_symm_apply i
lemma tailIndex_tail (S : Finset (Fin n)) (j : Fin (tailCount S)) :
    tailIndex S (tail S j) (tail_not_mem S j)=j := (Finset.univ \ S).equivFin.apply_symm_apply j

lemma keep_range (S : Finset (Fin n)) (v : Fin n) : (∃ i,keep S i=v) ↔ v∈S := by
  constructor
  · rintro ⟨i,rfl⟩; exact keep_mem S i
  · intro hv; exact ⟨keepIndex S v hv,keep_keepIndex S v hv⟩
lemma tail_range (S : Finset (Fin n)) (v : Fin n) : (∃ j,tail S j=v) ↔ v∉S := by
  constructor
  · rintro ⟨j,rfl⟩; exact tail_not_mem S j
  · intro hv; exact ⟨tailIndex S v hv,tail_tailIndex S v hv⟩

lemma selectedCount_le (S : Finset (Fin n)) : selectedCount S≤n := by
  simpa only [Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_of_subset (Finset.subset_univ S)
lemma card_total (S : Finset (Fin n)) : tailCount S+selectedCount S=n := by
  change ((Finset.univ : Finset (Fin n)) \ S).card+S.card=n
  rw [DominantGap.complement_card]
  exact Nat.sub_add_cancel (selectedCount_le S)

lemma selected_sum (S : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i : Fin (selectedCount S),f (keep S i))=∑ v in S,f v := by
  have h := Equiv.sum_comp S.equivFin.symm (fun v : ↥S => f v.val)
  simpa only [keep,NormalizedNetwork.selectedEmbedding,Finset.sum_coe_sort] using h
lemma tail_sum (S : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ j : Fin (tailCount S),f (tail S j))=∑ v in Finset.univ \ S,f v :=
  selected_sum (Finset.univ \ S) f
lemma sum_labels (S : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ v,f v)=(∑ i : Fin (selectedCount S),f (keep S i))+
      ∑ j : Fin (tailCount S),f (tail S j) := by
  rw [selected_sum,tail_sum]
  exact (Finset.sum_sdiff (Finset.subset_univ S)).symm.trans (add_comm _ _)

lemma collapsedRow_none (S : Finset (Fin n)) (w : Point n) :
    DominantGap.collapsedRow (tail S) w none=∑ v in S,w v := by
  change (∑ v in Finset.univ.filter (fun v : Fin n => v∉Finset.univ.image (tail S)),w v)=_
  have h : Finset.univ.filter (fun v : Fin n => v∉Finset.univ.image (tail S))=S := by
    ext v
    rw [tail_image]
    simp
  rw [h]
lemma collapsedRow_tail (S : Finset (Fin n)) (w : Point n) (j : Fin (tailCount S)) :
    DominantGap.collapsedRow (tail S) w (some j)=w (tail S j) := rfl

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
