import research.sN.exponential_push_20261102.forest_matching.Cover
import research.sN.exponential_push_20261102.forest_matching.Leaf

/-! A forest has a vertex cover no larger than one of its literal matchings.
This is the finite forest case of König's theorem, proved by leaf deletion. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.ForestMatching
open MaxCaterpillar.Frontier.RandomRestriction GrowingMatching
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Simultaneously construct a cover and a matching, using original vertices
and ordinary unordered edges. The matching cardinality dominates the cover. -/
theorem exists_cover_matching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    ∃ C : Finset (Fin n), ∃ M : Finset (Sym2 (Fin n)),
      IsVertexCover G C ∧ M ∈ matchings G M.card ∧ C.card ≤ M.card := by
  classical
  suffices h : ∀ m : ℕ, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.edgeFinset.card = m → H.IsAcyclic →
      ∃ C : Finset (Fin n), ∃ M : Finset (Sym2 (Fin n)),
        IsVertexCover H C ∧ M ∈ matchings H M.card ∧ C.card ≤ M.card from
    h G.edgeFinset.card G rfl hG
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro H instH hcard hH
    by_cases hedge : ∃ a b, H.Adj a b
    · obtain ⟨v,w,hvw,hleaf⟩ := Forest.exists_leaf hH hedge
      have hlt : (eraseEndpoints H v w).edgeFinset.card < m := by
        rw [← hcard]
        exact eraseEndpoints_card_lt H v w hvw
      obtain ⟨C,M,hC,hM,hCM⟩ := ih _ hlt (eraseEndpoints H v w) rfl
        (eraseEndpoints_acyclic H hH v w)
      have hnew := insert_leaf_edge_matching H v w hvw M hM
      have hsize := ((mem_matchings H _).mp hnew).2.1
      refine ⟨insert w C,insert (⟦(v,w)⟧ : Sym2 (Fin n)) M,
        insert_neighbor_covers H v w hleaf C hC,?_,?_⟩
      · simpa only [hsize] using hnew
      · rw [hsize]
        exact (Finset.card_insert_le w C).trans (Nat.add_le_add_right hCM 1)
    · refine ⟨∅,∅,?_,?_,by simp⟩
      · intro a b hab
        exact False.elim (hedge ⟨a,b,hab⟩)
      · apply (mem_matchings H ∅).mpr
        simp

/-- A matching can be restricted to any smaller requested cardinality. -/
lemma matching_exists_of_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : Finset (Sym2 (Fin n)))
    (hM : M ∈ matchings G M.card) (q : ℕ) (hq : q ≤ M.card) :
    ∃ B, B ∈ matchings G q := by
  classical
  obtain ⟨hsub,_,hdisj⟩ := (mem_matchings G M).mp hM
  obtain ⟨B,hBM,hcard⟩ := Finset.exists_smaller_set M q hq
  refine ⟨B,(mem_matchings G B).mpr ⟨hBM.trans hsub,hcard,?_⟩⟩
  intro e he f hf hef
  exact hdisj e (hBM he) f (hBM hf) hef

/-- Forests with no matching of r+1 edges have an actual cover of at most r vertices. -/
theorem cover_card_le_of_no_matching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (r : ℕ) (hno : ¬∃ B, B ∈ matchings G (r+1)) :
    ∃ C : Finset (Fin n), IsVertexCover G C ∧ C.card ≤ r := by
  obtain ⟨C,M,hC,hM,hCM⟩ := exists_cover_matching G hG
  refine ⟨C,hC,hCM.trans ?_⟩
  apply Nat.le_of_lt_succ
  by_contra hbad
  exact hno (matching_exists_of_le G M hM (r+1) (Nat.le_of_not_lt hbad))

/-- Equivalent contrapositive form: every cover requiring at least q vertices
forces a literal q-edge matching in a forest. -/
theorem matching_of_no_small_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (q : ℕ) (hcover : ∀ C : Finset (Fin n), IsVertexCover G C → q ≤ C.card) :
    ∃ B, B ∈ matchings G q := by
  obtain ⟨C,M,hC,hM,hCM⟩ := exists_cover_matching G hG
  exact matching_exists_of_le G M hM q ((hcover C hC).trans hCM)

#print axioms exists_cover_matching
#print axioms cover_card_le_of_no_matching
#print axioms matching_of_no_small_cover
end MaxCaterpillar.ExponentialPush.ForestMatching
