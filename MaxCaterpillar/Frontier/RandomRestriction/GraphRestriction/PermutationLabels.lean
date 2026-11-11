import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesFiveTail
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.Deletion

/-! # Actual selected and tail vertex labels under a full rank permutation

The permutation sends labels to positions. Its inverse reads the vertex label
at each prefix or tail position. Both ranges and the induced tail graph are
proved from those actual embeddings, without a supplied range hypothesis.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

variable {m : ℕ}

def selectedLabelEmbedding (τ : Equiv.Perm (Fin (m+5))) : Fin 5 ↪ Fin (m+5) :=
  (GoodEvent.selectedPosition m).trans τ.symm.toEmbedding

def tailLabelEmbedding (τ : Equiv.Perm (Fin (m+5))) : Fin m ↪ Fin (m+5) :=
  (GoodEvent.tailPosition m).trans τ.symm.toEmbedding

@[simp] theorem selectedLabelEmbedding_apply (τ : Equiv.Perm (Fin (m+5))) (i : Fin 5) :
    selectedLabelEmbedding τ i=τ.symm (GoodEvent.selectedPosition m i) := rfl

@[simp] theorem tailLabelEmbedding_apply (τ : Equiv.Perm (Fin (m+5))) (j : Fin m) :
    tailLabelEmbedding τ j=τ.symm (GoodEvent.tailPosition m j) := rfl

@[simp] theorem selectedLabelEmbedding_rank (τ : Equiv.Perm (Fin (m+5))) (i : Fin 5) :
    τ (selectedLabelEmbedding τ i)=GoodEvent.selectedPosition m i :=
  τ.apply_symm_apply (GoodEvent.selectedPosition m i)

@[simp] theorem tailLabelEmbedding_rank (τ : Equiv.Perm (Fin (m+5))) (j : Fin m) :
    τ (tailLabelEmbedding τ j)=GoodEvent.tailPosition m j :=
  τ.apply_symm_apply (GoodEvent.tailPosition m j)

/-- Exactly the first five actual labels occur in the prefix embedding. -/
theorem selectedLabelEmbedding_range (τ : Equiv.Perm (Fin (m+5))) (v : Fin (m+5)) :
    (∃ i,selectedLabelEmbedding τ i=v) ↔ v∈GoodEvent.smallRankGaps τ 5 := by
  constructor
  · rintro ⟨i,rfl⟩
    apply (GoodEvent.mem_smallRankGaps τ _).mpr
    rw [selectedLabelEmbedding_rank]
    exact i.isLt
  · intro hv
    have hi : (τ v).val<5 := (GoodEvent.mem_smallRankGaps τ v).mp hv
    refine ⟨⟨(τ v).val,hi⟩,?_⟩
    apply τ.injective
    rw [selectedLabelEmbedding_rank]
    exact Fin.ext rfl

/-- Every unselected actual label occurs exactly in the tail embedding. -/
theorem tailLabelEmbedding_range (τ : Equiv.Perm (Fin (m+5))) (v : Fin (m+5)) :
    (∃ j,tailLabelEmbedding τ j=v) ↔ v∉GoodEvent.smallRankGaps τ 5 := by
  constructor
  · rintro ⟨j,rfl⟩
    rw [GoodEvent.mem_smallRankGaps,tailLabelEmbedding_rank]
    exact Nat.not_lt.mpr (Nat.le_add_left 5 j.val)
  · intro hv
    have hj : 5≤(τ v).val := Nat.le_of_not_lt
      (fun h => hv ((GoodEvent.mem_smallRankGaps τ v).mpr h))
    have hlt : (τ v).val-5<m := by
      have he := Nat.sub_add_cancel hj
      have hb := (τ v).isLt
      linarith only [he,hb]
    refine ⟨⟨(τ v).val-5,hlt⟩,?_⟩
    apply τ.injective
    rw [tailLabelEmbedding_rank]
    exact Fin.ext (Nat.sub_add_cancel hj)

theorem selectedLabels_card (τ : Equiv.Perm (Fin (m+5))) :
    (GoodEvent.smallRankGaps τ 5).card=5 :=
  GoodEvent.card_smallRankGaps (Nat.le_add_left 5 m) τ

/-- The actual tail graph retains all but at most five full vertex degrees.
The complement range and selected-set cardinality are discharged here. -/
theorem tailGraph_edge_lower_bound (G : SimpleGraph (Fin (m+5)))
    [DecidableRel G.Adj] (τ : Equiv.Perm (Fin (m+5))) :
    (G.edgeFinset.card : ℝ)-5*((m : ℝ)+4) ≤
      ((G.comap (tailLabelEmbedding τ)).edgeFinset.card : ℝ) :=
  five_vertex_deletion_lower_bound G (GoodEvent.smallRankGaps τ 5)
    (selectedLabels_card τ) (tailLabelEmbedding τ) (tailLabelEmbedding_range τ)

#check @selectedLabelEmbedding_range
#check @tailLabelEmbedding_range
#check @tailGraph_edge_lower_bound
#print axioms selectedLabelEmbedding_range
#print axioms tailLabelEmbedding_range
#print axioms selectedLabels_card
#print axioms tailGraph_edge_lower_bound
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
