import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling

set_option autoImplicit false
noncomputable section
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling

example {n : ℕ} (S : Finset (Fin n)) : keep S=NormalizedNetwork.selectedEmbedding S := rfl
example {n : ℕ} (S : Finset (Fin n)) : tail S=DominantGap.complementEmbedding S := rfl
example {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    (∃ j,tail S j=v) ↔ v∉S := tail_range S v
example {n : ℕ} (S : Finset (Fin n)) (v : Fin n) (hv : v∉S) :
    tail S (tailIndex S v hv)=v := tail_tailIndex S v hv
example {n : ℕ} (S : Finset (Fin n)) : tailCount S+S.card=n := card_total S
example {n : ℕ} (S : Finset (Fin n)) (w : Point n) :
    DominantGap.collapsedRow (tail S) w none=∑ v in S,w v := collapsedRow_none S w
example {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ v,f v)=(∑ i : Fin S.card,f (keep S i))+
      ∑ j : Fin ((Finset.univ : Finset (Fin n)) \ S).card,f (tail S j) := sum_labels S f
example {n : ℕ} (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ) :
    actualPoint S p T=DominantGap.actualGapPoint (DominantGap.complementEmbedding S) p T := rfl
example {n h₁ h₂ : ℕ} (net : NormalizedNetwork n h₁ h₂) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T → 0<T ∧
      ∀ S : Finset (Fin n),∀ p : Cartesian.RawConfig ((Finset.univ : Finset (Fin n)) \ S).card,
        DominantGap.GenericNetworkPoint net (DominantGap.complementEmbedding S) p T :=
  exists_common_gap_threshold net
example {n : ℕ} (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (j : Fin (tailCount S)) :
    (fullPermutation S τ).symm (tailPosition S j)=tail S (τ j) := fullPermutation_tail S τ j
example {n : ℕ} (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S)))
    (i : Fin S.card) :
    (fullPermutation S τ).symm (selectedPosition S i)=keep S i := fullPermutation_selected S τ i
example {n : ℕ} (S : Finset (Fin n)) (τ : Equiv.Perm (Fin (tailCount S))) :
    GoodEvent.smallRankGaps (fullPermutation S τ) S.card=S := fullPermutation_selectedLabels S τ
example {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (RawConfig S)=((Finset.univ : Finset (Fin n)) \ S).card.factorial^2 :=
  rawConfig_card S

-- Empty and full selected blocks are literal actual sample instances.
example : tailCount (∅ : Finset (Fin 5))=5 := by
  simp only [tailCount,Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin]
example : tailCount (Finset.univ : Finset (Fin 5))=0 := by
  simp only [tailCount,Finset.sdiff_self,Finset.card_empty]
example : Nonempty (Sample 0) := ⟨⟨∅,(Equiv.refl _,Equiv.refl _)⟩⟩
example : Nonempty (NormalizedNetwork 1 1 1) :=
  ⟨{A:=0,U:=0,W:=0,L:=0,B:=0,d:=0}⟩
example (p : RawConfig (Finset.univ : Finset (Fin 3))) :
    actualPoint Finset.univ p 1=0 := by
  funext v
  exact actualPoint_selected_zero Finset.univ p 1 v (Finset.mem_univ v)

#check @tail
#check @tailIndex
#check @Sample
#check @exists_common_gap_threshold
#check @fullPermutation_tail
#print axioms keep_image
#print axioms tail_image
#print axioms keep_keepIndex
#print axioms tail_tailIndex
#print axioms keepIndex_keep
#print axioms tailIndex_tail
#print axioms keep_range
#print axioms tail_range
#print axioms card_total
#print axioms selected_sum
#print axioms tail_sum
#print axioms sum_labels
#print axioms collapsedRow_none
#print axioms actualPoint_selected_zero
#print axioms actualPoint_tail_negative
#print axioms exists_common_gap_threshold
#print axioms labelsEquiv
#print axioms selectedPosition_val
#print axioms tailPosition_val
#print axioms fullPermutation_selected
#print axioms fullPermutation_tail
#print axioms fullPermutation_selectedLabels
#print axioms rawConfig_card
#print axioms average_rawConfig
#print axioms sum_samples
#print axioms card_samples
