import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Braid
import MaxCaterpillar.Frontier.StarCertificate.StarObstruction

/-! The proven five-variable obstruction calibrates the actual growing-arity
structural hypothesis at (k,q)=(5,2), without any new assumption. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators NormalizedNetwork MaxCaterpillar.Frontier.StarCertificate
attribute [local instance] Classical.propDecidable

lemma hasMatchingOn_two_of_twoDisjoint {N : ℕ} (G : SimpleGraph (Fin N))
    (h : HasTwoDisjointEdgesOn G Finset.univ) : HasMatchingOn G 2 Finset.univ := by
  classical
  obtain ⟨a,b,c,d,_,_,_,_,hab,hcd,hac,had,hbc,hbd⟩ := h
  let e : Sym2 (Fin N) := ⟦(a,b)⟧
  let f : Sym2 (Fin N) := ⟦(c,d)⟧
  have he : e∈G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hab)
  have hf : f∈G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hcd)
  have hef : e≠f := by
    intro heq
    have hva : a∈GraphRestriction.edgeVertices e := by
      rw [show e=⟦(a,b)⟧ from rfl,GraphRestriction.edgeVertices_mk]
      simp
    rw [heq,show f=⟦(c,d)⟧ from rfl,GraphRestriction.edgeVertices_mk] at hva
    simp only [Finset.mem_insert,Finset.mem_singleton] at hva
    exact hva.elim hac had
  have hd : Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f) := by
    rw [show e=⟦(a,b)⟧ from rfl,show f=⟦(c,d)⟧ from rfl,
      GraphRestriction.edgeVertices_mk,GraphRestriction.edgeVertices_mk]
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hv'
    rcases hv with rfl|rfl <;> rcases hv' with hh|hh
    · exact hac hh
    · exact had hh
    · exact hbc hh
    · exact hbd hh
  have hm : {e,f}∈matchings G 2 :=
    GraphRestriction.pair_mem_disjointEdgePairs G e f he hf hef hd
  exact ⟨{e,f},hm,Finset.subset_univ _⟩

/-- H(5,2) follows from the independently closed all-real star certificate and
the actual Max5 braid-model Möbius obstruction. -/
theorem localMatchingObstruction_five_two : LocalMatchingObstruction 5 2 := by
  classical
  intro h₁ h₂ model hn hs hmax
  let pairs := BraidModel.rowPairs model hn hs
  obtain ⟨r,hr⟩ := StructuralWitness.exists_inner_not_pairwiseIntersecting_of_coefficients
    starAnova_all_real model hn hs hmax
  let G := quadraticInteractionGraph (BraidModel.innerQuadratic model pairs r)
  have hg : G=braidInteractionGraph model hn r := by
    apply SimpleGraph.ext
    funext a b
    apply propext
    change (a≠b ∧ effectiveInteraction (BraidModel.innerQuadratic model pairs r) a b≠0) ↔
      (a≠b ∧ braidEdgeWeight model.A (model.W r) a b≠0)
    by_cases hab : a=b
    · subst b
      simp only [ne_self_iff_false,false_and]
    · rw [BraidModel.inner_interaction_eq_braidEdgeWeight model pairs r a b hab]
  have htwo : HasTwoDisjointEdgesOn G Finset.univ :=
    (hasTwoDisjointEdgesOn_univ_iff G).mpr hr
  refine ⟨r,hasMatchingOn_two_of_twoDisjoint _ ?_⟩
  rwa [←hg]

#print axioms localMatchingObstruction_five_two
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
