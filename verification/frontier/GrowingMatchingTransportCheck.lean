import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Transport

set_option autoImplicit false
namespace GrowingMatchingTransportCheck
attribute [local instance] Classical.propDecidable
open MaxCaterpillar.Frontier.RandomRestriction
open GrowingMatching
variable {m n k q : ℕ}

/-- Expanded ordinary-edge matching witness after an actual comap embedding. -/
theorem exact_transport_contract (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m)))
    (hB : B ∈ matchings (G.comap f) q) :
    ∃ C : Finset (Sym2 (Fin n)), C ⊆ G.edgeFinset ∧ C.card=q ∧
      (∀ e∈C,∀ e'∈C,e≠e' →
        Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices e')) ∧
      GraphRestriction.pairVertices C ⊆ Finset.univ.image f := by
  obtain ⟨C,hC,hr⟩ := transport_matching G f B hB
  obtain ⟨hs,hc,hd⟩ := (mem_matchings G C).mp hC
  exact ⟨C,hs,hc,hd,hr⟩

/-- Exact selected-event consumer retains the actual permutation argument. -/
theorem exact_event_contract (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m)))
    (hB : B ∈ matchings (G.comap f) q) (σ : Equiv.Perm (Fin n))
    (hf : ∀ i, (σ (f i)).val < k) : σ ∈ selectedEvent G k q := by
  apply selectedEvent_of_comap_matching G f B hB σ
  intro i
  exact (GoodEvent.mem_smallRankGaps σ (f i)).mpr (hf i)

/-- Identity embeddings preserve every actual edge set, not just its size. -/
theorem identity_transport (B : Finset (Sym2 (Fin n))) :
    mapMatching (Equiv.refl (Fin n)).toEmbedding B = B := by
  classical
  change B.image (Sym2.map id) = B
  rw [Sym2.map_id,Finset.image_id]

#check @exact_transport_contract
#check @exact_event_contract
#print axioms exact_transport_contract
#print axioms exact_event_contract
#print axioms identity_transport
#print axioms GrowingMatching.edgeVertices_map
#print axioms GrowingMatching.mapMatching_card
#print axioms GrowingMatching.mapMatchingVertices
#print axioms GrowingMatching.mapped_edge_mem
#print axioms GrowingMatching.mapMatching_mem
#print axioms GrowingMatching.mapMatchingVertices_subset_range
#print axioms GrowingMatching.transport_matching
#print axioms GrowingMatching.selectedEvent_of_comap_matching
end GrowingMatchingTransportCheck
