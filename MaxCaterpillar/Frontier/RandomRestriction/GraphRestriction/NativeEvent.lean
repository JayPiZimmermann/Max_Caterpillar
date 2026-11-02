import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.Bounds
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.Intersecting
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.PermutationLabels

/-! # The native selected-graph obstruction has the actual event bound

The graph on the five selected input labels is an actual comap of the same
ambient graph used in the tail-deletion estimate. Its failure of pairwise
edge intersection is proved equivalent to two disjoint selected edges.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

variable {m : ℕ} (G : SimpleGraph (Fin (m+5))) [DecidableRel G.Adj]

theorem selected_graph_not_pairwise_iff (τ : Equiv.Perm (Fin (m+5))) :
    ¬StarCertificate.PairwiseIntersectingEdges
        (G.comap (selectedLabelEmbedding τ)) ↔
      hasTwoDisjointSelectedEdges G τ :=
  not_pairwiseIntersecting_comap_iff G τ (selectedLabelEmbedding τ)
    (selectedLabelEmbedding_range τ)

noncomputable def selectedGraphBadEvent : Finset (Equiv.Perm (Fin (m+5))) := by
  classical
  exact Finset.univ.filter fun τ =>
    ¬StarCertificate.PairwiseIntersectingEdges (G.comap (selectedLabelEmbedding τ))

@[simp] theorem mem_selectedGraphBadEvent (τ : Equiv.Perm (Fin (m+5))) :
    τ∈selectedGraphBadEvent G ↔
      ¬StarCertificate.PairwiseIntersectingEdges
        (G.comap (selectedLabelEmbedding τ)) := by
  classical
  simp only [selectedGraphBadEvent,Finset.mem_filter,Finset.mem_univ,true_and]

theorem selectedGraphBadEvent_eq_twoEdgesEvent :
    selectedGraphBadEvent G=twoEdgesEvent G := by
  classical
  ext τ
  rw [mem_selectedGraphBadEvent,mem_twoEdgesEvent,selected_graph_not_pairwise_iff G τ]

/-- The native local-graph obstruction has the same ordinary uniform
permutation probability as the explicit two-disjoint-edge event. -/
theorem selectedGraphBadEvent_fraction_le :
    ((selectedGraphBadEvent G).card : ℝ)/
        (Fintype.card (Equiv.Perm (Fin (m+5))) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/((m+5).descFactorial 4 : ℝ) := by
  rw [selectedGraphBadEvent_eq_twoEdgesEvent]
  exact twoEdgesEvent_fraction_le G (Nat.le_add_left 5 m)

theorem selectedGraphBadEvent_fraction_le_tail (hm : 0<m) :
    ((selectedGraphBadEvent G).card : ℝ)/
        (Fintype.card (Equiv.Perm (Fin (m+5))) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/(m : ℝ)^4 := by
  rw [selectedGraphBadEvent_eq_twoEdgesEvent]
  exact twoEdgesEvent_fraction_le_tail G hm

#check @selected_graph_not_pairwise_iff
#print axioms selected_graph_not_pairwise_iff
#print axioms selectedGraphBadEvent_eq_twoEdgesEvent
#print axioms selectedGraphBadEvent_fraction_le_tail
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
