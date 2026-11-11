import research.sN.exponential_push_20261102.forest_matching.Konig
import research.sN.exponential_push_20261102.forest_matching.Cycle

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.ForestMatching.Check
open BigOperators MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
attribute [local instance] Classical.propDecidable

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    ∃ C : Finset (Fin n), ∃ M : Finset (Sym2 (Fin n)),
      (∀ a b, G.Adj a b → a∈C ∨ b∈C) ∧
      M ∈ matchings G M.card ∧ C.card≤M.card :=
  exists_cover_matching G hG

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (r : ℕ) (hno : ¬∃ B : Finset (Sym2 (Fin n)), B ∈ matchings G (r+1)) :
    ∃ C : Finset (Fin n), (∀ a b, G.Adj a b → a∈C ∨ b∈C) ∧ C.card≤r :=
  cover_card_le_of_no_matching G hG r hno

example {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H≤G)
    (M : Finset (Sym2 (Fin n))) (q : ℕ) (hM : M∈matchings H q) :
    M∈matchings G q := matching_mono hHG hM

example {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (A : Finset ι) (a b : ι→V) (hcycle : ¬(indexedGraph A a b).IsAcyclic) :
    ∃ S : Finset ι, S⊆A ∧ S.Nonempty ∧ ∃ reverse : ι→Bool,
      ∀ x : V→ℝ,
        ∑ i in S,(if reverse i then -(x (a i)-x (b i)) else x (a i)-x (b i))=0 :=
  indexedGraph_oriented_cycle A a b hcycle

/-- An explicit acyclic nonempty graph, independent of the leaf construction. -/
def singleEdge : SimpleGraph (Fin 3) where
  Adj u v := (u=0 ∧ v=1) ∨ (u=1 ∧ v=0)
  symm := by intro u v h; tauto
  loopless := by intro u h; rcases h with ⟨rfl,h⟩|⟨rfl,h⟩ <;> norm_num at h

lemma singleEdge_acyclic : singleEdge.IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro v w hvw
  rw [SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges]
  refine ⟨hvw,?_⟩
  intro p
  cases p with
  | nil => exact False.elim (singleEdge.loopless _ hvw)
  | cons h q =>
    have hsame : ∀ u, singleEdge.Adj v u → u=w := by
      intro u hu
      rcases hvw with hvw|hvw <;> rcases hu with hu|hu <;> rcases hvw with ⟨rfl,rfl⟩ <;> simp_all
    have h := hsame _ h
    subst h
    simp

example : ∃ v w : Fin 3, singleEdge.Adj v w ∧ ∀ u, singleEdge.Adj v u → u=w :=
  Forest.exists_leaf singleEdge_acyclic ⟨0,1,Or.inl ⟨rfl,rfl⟩⟩

#check @exists_cover_matching
#check @cover_card_le_of_no_matching
#check @matching_of_no_small_cover
#check @indexedGraph_oriented_cycle
#print axioms Forest.exists_leaf
#print axioms exists_cover_matching
#print axioms cover_card_le_of_no_matching
#print axioms matching_of_no_small_cover
#print axioms indexedGraph_oriented_cycle
#print axioms singleEdge_acyclic
end MaxCaterpillar.ExponentialPush.ForestMatching.Check
