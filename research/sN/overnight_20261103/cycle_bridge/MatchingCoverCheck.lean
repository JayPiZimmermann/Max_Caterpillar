import research.sN.overnight_20261103.cycle_bridge.MatchingCover

set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.CycleBridge.Check
open Frontier.RandomRestriction GrowingMatching

theorem exact_matching_cover_type {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C)
    (B : Finset (Sym2 (Fin n)))
    (hsub : B ⊆ G.edgeFinset) (hcard : B.card=q)
    (hdisj : ∀ e∈B,∀ f∈B,e≠f →
      Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f)) :
    q≤C.card := by
  exact matching_card_le_cover G C hC B
    ((mem_matchings G B).mpr ⟨hsub,hcard,hdisj⟩)

/-- The complete two-vertex graph is a nonempty covered graph with an
attained one-edge matching. The inequality is sharp on this control. -/
theorem nonempty_sharp_control :
    let G : SimpleGraph (Fin 2) := ⊤
    let C : Finset (Fin 2) := {0}
    let B : Finset (Sym2 (Fin 2)) := {⟦((0 : Fin 2),1)⟧}
    (∀ a b, G.Adj a b → a∈C ∨ b∈C) ∧ B∈matchings G 1 ∧ C.card=1 := by
  classical
  dsimp only
  refine ⟨?_,?_,by simp⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · apply (mem_matchings _ _).mpr
    refine ⟨?_,by simp,?_⟩
    · intro e he
      have heq := Finset.mem_singleton.mp he
      rw [heq]
      apply SimpleGraph.mem_edgeFinset.mpr
      apply (SimpleGraph.mem_edgeSet _).mpr
      exact (SimpleGraph.top_adj _ _).mpr (by decide)
    · intro e he f hf hne
      exact False.elim (hne ((Finset.mem_singleton.mp he).trans
        (Finset.mem_singleton.mp hf).symm))

#check @exact_matching_cover_type
#print axioms exact_matching_cover_type
#print axioms nonempty_sharp_control
end MaxCaterpillar.ExponentialPush.CycleBridge.Check
