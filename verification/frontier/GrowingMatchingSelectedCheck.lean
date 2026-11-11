import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected

set_option autoImplicit false
namespace GrowingMatchingSelectedCheck
attribute [local instance] Classical.propDecidable
open MaxCaterpillar.Frontier.RandomRestriction
open GrowingMatching
variable {n k q : ℕ}

/-- Independent expanded cardinal contract, including the factorial. -/
theorem exact_card_contract (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hkn : k ≤ n) :
    q.factorial * ((selectedEvent G k q).card * n.descFactorial (2*q)) ≤
      G.edgeFinset.card^q *
        (k.descFactorial (2*q) * Fintype.card (Equiv.Perm (Fin n))) :=
  selectedEvent_card_mul_factorial_le G hkn

/-- Independent exact probability type, with no positivity or nonempty
matching premise. In particular no event bound is assumed. -/
theorem exact_fraction_contract (G : SimpleGraph (Fin n)) [hG : DecidableRel G.Adj]
    (hkn : k ≤ n) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ∃ B : Finset (Sym2 (Fin n)), B ⊆ G.edgeFinset ∧ B.card=q ∧
        (∀ e∈B,∀ f∈B,e≠f →
          Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f)) ∧
        GraphRestriction.pairVertices B ⊆ GoodEvent.smallRankGaps σ k).card : ℝ) /
          Fintype.card (Equiv.Perm (Fin n)) ≤
      ((G.edgeFinset.card : ℝ)^q / (q.factorial : ℝ)) *
        ((k.descFactorial (2*q) : ℝ) / (n.descFactorial (2*q) : ℝ)) := by
  classical
  letI : DecidableRel G.Adj := hG
  have he : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ∃ B : Finset (Sym2 (Fin n)), B ⊆ G.edgeFinset ∧ B.card=q ∧
        (∀ e∈B,∀ f∈B,e≠f →
          Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f)) ∧
        GraphRestriction.pairVertices B ⊆ GoodEvent.smallRankGaps σ k) =
        selectedEvent G k q := by
    ext σ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_selectedEvent,
      hasSelectedMatching,mem_matchings,matchingVertices]
    constructor
    · rintro ⟨B,hB,hcard,hd,hs⟩
      exact ⟨B,⟨hB,hcard,hd⟩,hs⟩
    · rintro ⟨B,⟨hB,hcard,hd⟩,hs⟩
      exact ⟨B,hB,hcard,hd,hs⟩
  have hp := congrArg (fun B : Finset (Equiv.Perm (Fin n)) =>
    (B.card : ℝ) / Fintype.card (Equiv.Perm (Fin n))) he
  exact hp.le.trans (selectedEvent_fraction_le (q:=q) (k:=k) G hkn)

/-- Nondegenerate control: one edge, one requested edge, all labels selected.
The event is genuinely nonempty for every permutation. -/
theorem one_edge_full_prefix :
    selectedEvent (⊤ : SimpleGraph (Fin 2)) 2 1 = Finset.univ := by
  classical
  ext σ
  simp only [mem_selectedEvent,Finset.mem_univ,iff_true]
  refine ⟨{(⟦((0 : Fin 2),1)⟧ : Sym2 (Fin 2))},?_,?_⟩
  · rw [mem_matchings]
    refine ⟨?_,by simp,?_⟩
    · intro e he
      have heq := Finset.mem_singleton.mp he
      subst e
      simp [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    · intro e he f hf hne
      exact False.elim (hne ((Finset.mem_singleton.mp he).trans
        (Finset.mem_singleton.mp hf).symm))
  · intro v _
    exact (GoodEvent.mem_smallRankGaps σ v).mpr (σ v).isLt

theorem empty_ground_zero_request :
    selectedEvent (⊥ : SimpleGraph (Fin 0)) 0 0 = Finset.univ :=
  selectedEvent_zero _

theorem oversized_request :
    selectedEvent (⊤ : SimpleGraph (Fin 2)) 2 2 = ∅ :=
  selectedEvent_empty_of_prefix_lt _ (by decide) (by decide)

#check @exact_card_contract
#check @exact_fraction_contract
#print axioms exact_card_contract
#print axioms exact_fraction_contract
#print axioms one_edge_full_prefix
#print axioms empty_ground_zero_request
#print axioms oversized_request
#print axioms GrowingMatching.containment_card_mul_descFactorial
#print axioms GrowingMatching.matchingVertices_card
#print axioms GrowingMatching.selectedEvent_card_mul_le_matchings
#print axioms GrowingMatching.selectedEvent_card_mul_le_choose
#print axioms GrowingMatching.selectedEvent_fraction_le_choose
#print axioms GrowingMatching.selectedEvent_fraction_le
end GrowingMatchingSelectedCheck
