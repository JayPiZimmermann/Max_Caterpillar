import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Finite graph preliminaries for forest matching / vertex-cover duality.
The graph remains on the original vertex type when endpoints are deleted. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.ForestMatching
open MaxCaterpillar.Frontier.RandomRestriction
open GrowingMatching
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Delete every edge incident to either specified vertex. -/
def eraseEndpoints (G : SimpleGraph (Fin n)) (v w : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ a ≠ w ∧ b ≠ v ∧ b ≠ w
  symm := by
    rintro a b ⟨hab,hav,haw,hbv,hbw⟩
    exact ⟨hab.symm,hbv,hbw,hav,haw⟩
  loopless := by
    intro a ha
    exact G.loopless a ha.1

lemma eraseEndpoints_le (G : SimpleGraph (Fin n)) (v w : Fin n) :
    eraseEndpoints G v w ≤ G := fun _ _ h => h.1

lemma acyclic_of_le {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hG : G.IsAcyclic) :
    H.IsAcyclic := by
  intro a p hp
  exact hG (p.mapLe h) (hp.mapLe h)

lemma eraseEndpoints_acyclic (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) (v w : Fin n) :
    (eraseEndpoints G v w).IsAcyclic := acyclic_of_le (eraseEndpoints_le G v w) hG

lemma edgeFinset_subset_of_le {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : H ≤ G) : H.edgeFinset ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    apply SimpleGraph.mem_edgeFinset.mpr
    apply (SimpleGraph.mem_edgeSet G).mpr
    exact h ((SimpleGraph.mem_edgeSet H).mp (SimpleGraph.mem_edgeFinset.mp he))

lemma eraseEndpoints_card_lt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (hvw : G.Adj v w) :
    (eraseEndpoints G v w).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨edgeFinset_subset_of_le (eraseEndpoints_le G v w), ?_⟩
  intro heq
  have he : (⟦(v,w)⟧ : Sym2 (Fin n)) ∈ G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hvw)
  rw [← heq] at he
  have hadj := (SimpleGraph.mem_edgeSet (eraseEndpoints G v w)).mp
    (SimpleGraph.mem_edgeFinset.mp he)
  exact hadj.2.1 rfl

/-- Literal endpoint cover, on original graph vertices. -/
def IsVertexCover (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : Prop :=
  ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C

lemma insert_neighbor_covers (G : SimpleGraph (Fin n)) (v w : Fin n)
    (hleaf : ∀ u, G.Adj v u → u = w) (C : Finset (Fin n))
    (hC : IsVertexCover (eraseEndpoints G v w) C) :
    IsVertexCover G (insert w C) := by
  classical
  intro a b hab
  by_cases haw : a = w
  · exact Or.inl (by simp [haw])
  by_cases hbw : b = w
  · exact Or.inr (by simp [hbw])
  have hav : a ≠ v := by
    intro hav
    subst a
    exact hbw (hleaf b hab)
  have hbv : b ≠ v := by
    intro hbv
    subst b
    exact haw (hleaf a hab.symm)
  rcases hC a b ⟨hab,hav,haw,hbv,hbw⟩ with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

lemma matching_mono {G H : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : H ≤ G) {M : Finset (Sym2 (Fin n))} {q : ℕ}
    (hM : M ∈ matchings H q) : M ∈ matchings G q := by
  classical
  obtain ⟨hsub,hcard,hdisj⟩ := (mem_matchings H M).mp hM
  exact (mem_matchings G M).mpr ⟨hsub.trans (edgeFinset_subset_of_le h),hcard,hdisj⟩

lemma erased_edge_avoids (G : SimpleGraph (Fin n)) (v w : Fin n)
    (e : Sym2 (Fin n)) (he : e ∈ (eraseEndpoints G v w).edgeFinset) :
    v ∉ GraphRestriction.edgeVertices e ∧ w ∉ GraphRestriction.edgeVertices e := by
  classical
  induction e using Sym2.ind with
  | h a b =>
    have hadj := (SimpleGraph.mem_edgeSet (eraseEndpoints G v w)).mp
      (SimpleGraph.mem_edgeFinset.mp he)
    rw [GraphRestriction.edgeVertices_mk]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact ⟨fun h => h.elim (fun h => hadj.2.1 h.symm) (fun h => hadj.2.2.2.1 h.symm),
      fun h => h.elim (fun h => hadj.2.2.1 h.symm) (fun h => hadj.2.2.2.2 h.symm)⟩

lemma insert_leaf_edge_matching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (hvw : G.Adj v w) (M : Finset (Sym2 (Fin n)))
    (hM : M ∈ matchings (eraseEndpoints G v w) M.card) :
    insert (⟦(v,w)⟧ : Sym2 (Fin n)) M ∈ matchings G (M.card + 1) := by
  classical
  obtain ⟨hsub,_,hdisj⟩ := (mem_matchings (eraseEndpoints G v w) M).mp hM
  have hnot : (⟦(v,w)⟧ : Sym2 (Fin n)) ∉ M := by
    intro he
    have h := (erased_edge_avoids G v w _ (hsub he)).1
    apply h
    rw [GraphRestriction.edgeVertices_mk]
    simp
  have hedge : (⟦(v,w)⟧ : Sym2 (Fin n)) ∈ G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hvw)
  have hfresh : ∀ e ∈ M, Disjoint (GraphRestriction.edgeVertices (⟦(v,w)⟧ : Sym2 (Fin n)))
      (GraphRestriction.edgeVertices e) := by
    intro e he
    obtain ⟨hv,hw⟩ := erased_edge_avoids G v w e (hsub he)
    rw [GraphRestriction.edgeVertices_mk,Finset.disjoint_left]
    intro x hx hxe
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv hxe
    · have hxw := Finset.mem_singleton.mp hx
      subst x
      exact hw hxe
  apply (mem_matchings G _).mpr
  refine ⟨?_,Finset.card_insert_of_not_mem hnot,?_⟩
  · exact Finset.insert_subset hedge (hsub.trans (edgeFinset_subset_of_le (eraseEndpoints_le G v w)))
  · intro e he f hf hne
    rcases Finset.mem_insert.mp he with rfl | he <;>
      rcases Finset.mem_insert.mp hf with rfl | hf
    · exact False.elim (hne rfl)
    · exact hfresh f hf
    · exact (hfresh e he).symm
    · exact hdisj e he f hf hne

#print axioms insert_leaf_edge_matching
end MaxCaterpillar.ExponentialPush.ForestMatching
