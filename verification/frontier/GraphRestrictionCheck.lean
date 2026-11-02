import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

set_option autoImplicit false
open MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

example {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (hN : 5≤N) :
    ((twoEdgesEvent G).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/(N.descFactorial 4 : ℝ) :=
  twoEdgesEvent_fraction_le G hN

-- The native obstruction is an actual graph property, not an assumed
-- inclusion in the already-counted bad event.
example {m : ℕ} (G : SimpleGraph (Fin (m+5))) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin (m+5))) :
    ¬StarCertificate.PairwiseIntersectingEdges (G.comap (selectedLabelEmbedding τ)) ↔
      hasTwoDisjointSelectedEdges G τ := selected_graph_not_pairwise_iff G τ

example {m : ℕ} (G : SimpleGraph (Fin (m+5))) [DecidableRel G.Adj] (hm : 0<m) :
    ((selectedGraphBadEvent G).card : ℝ)/
        (Fintype.card (Equiv.Perm (Fin (m+5))) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/(m : ℝ)^4 :=
  selectedGraphBadEvent_fraction_le_tail G hm

-- This is the complementary graph from the same original permutation and G.
example {m : ℕ} (G : SimpleGraph (Fin (m+5))) [DecidableRel G.Adj]
    (τ : Equiv.Perm (Fin (m+5))) :
    (G.edgeFinset.card : ℝ)-5*((m : ℝ)+4) ≤
      ((G.comap (tailLabelEmbedding τ)).edgeFinset.card : ℝ) :=
  tailGraph_edge_lower_bound G τ

example {m : ℕ} (τ : Equiv.Perm (Fin (m+5))) (v : Fin (m+5)) :
    (∃ i,selectedLabelEmbedding τ i=v) ↔ v∈GoodEvent.smallRankGaps τ 5 :=
  selectedLabelEmbedding_range τ v

example {m : ℕ} (τ : Equiv.Perm (Fin (m+5))) (v : Fin (m+5)) :
    (∃ i,tailLabelEmbedding τ i=v) ↔ v∉GoodEvent.smallRankGaps τ 5 :=
  tailLabelEmbedding_range τ v

example {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (S : Finset (Fin N)) :
    G.edgeFinset.card≤(retainedEdges G S).card+S.card*(N-1) :=
  edge_card_le_retained_add G S

#print axioms selectedFourSetEvent_fraction
#print axioms twoEdgesEvent_card_mul_le
#print axioms twoEdgesEvent_fraction_le
#print axioms edge_card_le_retained_add
#print axioms comap_edge_card_eq_retained
#print axioms induce_edge_card_eq_retained
#print axioms five_vertex_deletion_lower_bound
#print axioms selectedLabelEmbedding_range
#print axioms tailLabelEmbedding_range
#print axioms tailGraph_edge_lower_bound
#print axioms not_pairwiseIntersecting_comap_iff
#print axioms selected_graph_not_pairwise_iff
#print axioms selectedGraphBadEvent_eq_twoEdgesEvent
#print axioms selectedGraphBadEvent_fraction_le
#print axioms selectedGraphBadEvent_fraction_le_tail
