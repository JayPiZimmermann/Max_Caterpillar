import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected

/-! Matching witnesses transport through actual injective induced-graph
embeddings. Their edge count and all endpoints are preserved. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
variable {m n k q : ℕ}

theorem edgeVertices_map (f : Fin m ↪ Fin n) (e : Sym2 (Fin m)) :
    GraphRestriction.edgeVertices (Sym2.map f e) =
      (GraphRestriction.edgeVertices e).image f := by
  classical
  ext v
  simp only [GraphRestriction.mem_edgeVertices,Sym2.mem_map,Finset.mem_image]

noncomputable def mapMatching (f : Fin m ↪ Fin n)
    (B : Finset (Sym2 (Fin m))) : Finset (Sym2 (Fin n)) := by
  classical
  exact B.image (Sym2.map f)

theorem mapMatching_card (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m))) :
    (mapMatching f B).card = B.card := by
  classical
  exact Finset.card_image_of_injective B (Sym2.map.injective f.injective)

theorem mapMatchingVertices (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m))) :
    matchingVertices (mapMatching f B) = (matchingVertices B).image f := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    rw [edgeVertices_map] at hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨u,Finset.mem_biUnion.mpr ⟨a,ha,hu⟩,rfl⟩
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,hu⟩ := Finset.mem_biUnion.mp hu
    apply Finset.mem_biUnion.mpr
    refine ⟨Sym2.map f e,Finset.mem_image.mpr ⟨e,he,rfl⟩,?_⟩
    rw [edgeVertices_map]
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩

theorem mapped_edge_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (e : Sym2 (Fin m))
    (he : e ∈ (G.comap f).edgeFinset) : Sym2.map f e ∈ G.edgeFinset := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_pair_eq,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.mem_edgeSet (G.comap f)).mp (SimpleGraph.mem_edgeFinset.mp he)

/-- The actual image of every local q-matching is an ambient q-matching. -/
theorem mapMatching_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m)))
    (hB : B ∈ matchings (G.comap f) q) : mapMatching f B ∈ matchings G q := by
  classical
  obtain ⟨hsub,hcard,hd⟩ := (mem_matchings (G.comap f) B).mp hB
  apply (mem_matchings G _).mpr
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact mapped_edge_mem G f a (hsub ha)
  · rw [mapMatching_card,hcard]
  · intro e he g hg heg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
    rw [edgeVertices_map,edgeVertices_map,Finset.disjoint_image f.injective]
    apply hd a ha b hb
    intro hab
    exact heg (congrArg (Sym2.map f) hab)

/-- All transported endpoints lie in the genuine embedding range. -/
theorem mapMatchingVertices_subset_range (f : Fin m ↪ Fin n)
    (B : Finset (Sym2 (Fin m))) :
    matchingVertices (mapMatching f B) ⊆ Finset.univ.image f := by
  classical
  rw [mapMatchingVertices]
  exact Finset.image_subset_image (Finset.subset_univ _)

/-- Existential form suitable for an actual induced-graph matching witness. -/
theorem transport_matching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m)))
    (hB : B ∈ matchings (G.comap f) q) :
    ∃ C ∈ matchings G q, matchingVertices C ⊆ Finset.univ.image f :=
  ⟨mapMatching f B,mapMatching_mem G f B hB,mapMatchingVertices_subset_range f B⟩

/-- If a local embedding uses selected labels, every actual local matching
is a witness in the literal ambient selected-permutation event. -/
theorem selectedEvent_of_comap_matching (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : Fin m ↪ Fin n) (B : Finset (Sym2 (Fin m)))
    (hB : B ∈ matchings (G.comap f) q) (σ : Equiv.Perm (Fin n))
    (hf : ∀ i, f i ∈ GoodEvent.smallRankGaps σ k) : σ ∈ selectedEvent G k q := by
  apply (mem_selectedEvent G σ).mpr
  refine ⟨mapMatching f B,mapMatching_mem G f B hB,?_⟩
  intro v hv
  obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp (mapMatchingVertices_subset_range f B hv)
  exact hf i

#check @transport_matching
#check @selectedEvent_of_comap_matching
#print axioms edgeVertices_map
#print axioms mapMatchingVertices
#print axioms mapMatching_mem
#print axioms transport_matching
#print axioms selectedEvent_of_comap_matching
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
