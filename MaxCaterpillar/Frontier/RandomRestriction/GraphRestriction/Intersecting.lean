import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.TwoEdges.Basic
import MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraph

/-! # Pairwise intersection and the literal selected two-edge event

An arbitrary embedding onto the selected labels identifies the local graph's
failure of pairwise intersection with two disjoint actual ambient edges.
The local vertex type needs neither finiteness nor nonemptiness.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

variable {N : ℕ}

/-- An endpoint description of the event retains actual graph adjacency and
the literal selection of all four ambient labels. -/
theorem hasTwoDisjointSelectedEdges_iff_endpoints
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N)) :
    hasTwoDisjointSelectedEdges G τ ↔
      ∃ a b c d : Fin N,G.Adj a b ∧ G.Adj c d ∧
        ¬(a=c ∨ a=d ∨ b=c ∨ b=d) ∧
        ({a,b,c,d} : Finset (Fin N)) ⊆ GoodEvent.smallRankGaps τ 5 := by
  classical
  constructor
  · rintro ⟨e,he,f,hf,hef,hd,hsel⟩
    revert he hf hef hd hsel
    refine Sym2.inductionOn₂ e f ?_
    intro a b c d he hf _hef hd hsel
    have hab : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp he)
    have hcd : G.Adj c d := (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp hf)
    rw [edgeVertices_mk,edgeVertices_mk] at hd hsel
    have hcross : ¬(a=c ∨ a=d ∨ b=c ∨ b=d) := by
      intro h
      rcases h with h | h | h | h
      · exact Finset.disjoint_left.mp hd (show a∈({a,b} : Finset (Fin N)) by simp) (by simp [h])
      · exact Finset.disjoint_left.mp hd (show a∈({a,b} : Finset (Fin N)) by simp) (by simp [h])
      · exact Finset.disjoint_left.mp hd (show b∈({a,b} : Finset (Fin N)) by simp) (by simp [h])
      · exact Finset.disjoint_left.mp hd (show b∈({a,b} : Finset (Fin N)) by simp) (by simp [h])
    refine ⟨a,b,c,d,hab,hcd,hcross,?_⟩
    intro v hv
    apply hsel
    simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_union] at hv ⊢
    tauto
  · rintro ⟨a,b,c,d,hab,hcd,hcross,hsel⟩
    have hd : Disjoint (edgeVertices (⟦(a,b)⟧ : Sym2 (Fin N)))
        (edgeVertices (⟦(c,d)⟧ : Sym2 (Fin N))) := by
      rw [edgeVertices_mk,edgeVertices_mk]
      apply Finset.disjoint_left.mpr
      intro v hv hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with h | h
      · exact hcross (Or.inl h)
      · exact hcross (Or.inr (Or.inl h))
      · exact hcross (Or.inr (Or.inr (Or.inl h)))
      · exact hcross (Or.inr (Or.inr (Or.inr h)))
    have hne : (⟦(a,b)⟧ : Sym2 (Fin N)) ≠ ⟦(c,d)⟧ := by
      intro heq
      have ha : a∈edgeVertices (⟦(a,b)⟧ : Sym2 (Fin N)) := by rw [edgeVertices_mk]; simp
      have ha' : a∈edgeVertices (⟦(c,d)⟧ : Sym2 (Fin N)) := heq ▸ ha
      exact Finset.disjoint_left.mp hd ha ha'
    refine ⟨⟦(a,b)⟧,SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hab),
      ⟦(c,d)⟧,SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hcd),hne,hd,?_⟩
    rw [edgeVertices_mk,edgeVertices_mk]
    intro v hv
    apply hsel
    simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_union] at hv ⊢
    tauto

/-- Exact transport for any embedding onto the selected vertex set.
There is no finiteness or nonemptiness assumption on the local vertex type. -/
theorem not_pairwiseIntersecting_comap_iff {V : Type*}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N))
    (r : V ↪ Fin N)
    (hrange : ∀ v,(∃ u,r u=v) ↔ v∈GoodEvent.smallRankGaps τ 5) :
    ¬StarCertificate.PairwiseIntersectingEdges (G.comap r) ↔
      hasTwoDisjointSelectedEdges G τ := by
  classical
  constructor
  · intro h
    change ¬(∀ a b c d : V,G.Adj (r a) (r b) → G.Adj (r c) (r d) →
      a=c ∨ a=d ∨ b=c ∨ b=d) at h
    push_neg at h
    obtain ⟨a,b,c,d,hab,hcd,hac,had,hbc,hbd⟩ := h
    apply (hasTwoDisjointSelectedEdges_iff_endpoints G τ).mpr
    refine ⟨r a,r b,r c,r d,hab,hcd,?_,?_⟩
    · intro h
      rcases h with h | h | h | h
      · exact hac (r.injective h)
      · exact had (r.injective h)
      · exact hbc (r.injective h)
      · exact hbd (r.injective h)
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact (hrange (r a)).mp ⟨a,rfl⟩
      · exact (hrange (r b)).mp ⟨b,rfl⟩
      · exact (hrange (r c)).mp ⟨c,rfl⟩
      · exact (hrange (r d)).mp ⟨d,rfl⟩
  · intro h hPI
    obtain ⟨a,b,c,d,hab,hcd,hcross,hsel⟩ :=
      (hasTwoDisjointSelectedEdges_iff_endpoints G τ).mp h
    obtain ⟨a',ha'⟩ := (hrange a).mpr (hsel (by simp))
    obtain ⟨b',hb'⟩ := (hrange b).mpr (hsel (by simp))
    obtain ⟨c',hc'⟩ := (hrange c).mpr (hsel (by simp))
    obtain ⟨d',hd'⟩ := (hrange d).mpr (hsel (by simp))
    have hab' : (G.comap r).Adj a' b' := by
      change G.Adj (r a') (r b')
      rwa [ha',hb']
    have hcd' : (G.comap r).Adj c' d' := by
      change G.Adj (r c') (r d')
      rwa [hc',hd']
    apply hcross
    rcases hPI a' b' c' d' hab' hcd' with h | h | h | h
    · exact Or.inl (by simpa only [ha',hc'] using congrArg r h)
    · exact Or.inr (Or.inl (by simpa only [ha',hd'] using congrArg r h))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [hb',hc'] using congrArg r h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [hb',hd'] using congrArg r h)))

/-- The positive form directly discharges a local pairwise-intersection
hypothesis when the literal ambient disjoint-edge event is absent. -/
theorem pairwiseIntersecting_comap_iff_not_two_edges {V : Type*}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N))
    (r : V ↪ Fin N)
    (hrange : ∀ v,(∃ u,r u=v) ↔ v∈GoodEvent.smallRankGaps τ 5) :
    StarCertificate.PairwiseIntersectingEdges (G.comap r) ↔
      ¬hasTwoDisjointSelectedEdges G τ := by
  classical
  simpa only [not_not] using not_congr (not_pairwiseIntersecting_comap_iff G τ r hrange)

/-- In particular, use the ordinary induced graph on the actual selected
subtype, with no chosen labeling or cardinality hypothesis. -/
theorem not_pairwiseIntersecting_selected_induce_iff
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (τ : Equiv.Perm (Fin N)) :
    ¬StarCertificate.PairwiseIntersectingEdges
      (G.induce (↑(GoodEvent.smallRankGaps τ 5) : Set (Fin N))) ↔
      hasTwoDisjointSelectedEdges G τ := by
  apply not_pairwiseIntersecting_comap_iff G τ (Function.Embedding.subtype _)
  intro v
  constructor
  · rintro ⟨u,hu⟩
    exact hu ▸ u.property
  · intro hv
    exact ⟨⟨v,hv⟩,rfl⟩

#check @not_pairwiseIntersecting_comap_iff
#check @pairwiseIntersecting_comap_iff_not_two_edges
#check @not_pairwiseIntersecting_selected_induce_iff
#print axioms hasTwoDisjointSelectedEdges_iff_endpoints
#print axioms not_pairwiseIntersecting_comap_iff
#print axioms pairwiseIntersecting_comap_iff_not_two_edges
#print axioms not_pairwiseIntersecting_selected_induce_iff
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
