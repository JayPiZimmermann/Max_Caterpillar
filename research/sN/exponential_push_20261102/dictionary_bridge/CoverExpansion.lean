import research.sN.exponential_push_20261102.dictionary_bridge.Expansion
import research.sN.exponential_push_20261102.forest_matching.Konig

/-! A matching bound on the original graph gives a small cover for every
actual forest state in the constructed expansion. No width bound is used.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DictionaryBridge
open ForestMatching Frontier.RandomRestriction GrowingMatching
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matching_mem_of_graph_le (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G≤H)
    (B : Finset (Sym2 (Fin n))) (q : ℕ) (hB : B∈matchings G q) : B∈matchings H q := by
  obtain ⟨hsub,hcard,hdisj⟩ := (mem_matchings G B).mp hB
  exact (mem_matchings H B).mpr
    ⟨hsub.trans (edgeFinset_subset_of_le hGH),hcard,hdisj⟩

/-- The cover bound concerns each resulting forest on the original input
vertices; all matchings use the same actual unordered-edge convention. -/
theorem forestState_small_cover (A : Finset ι) (a b : ι→Fin n) (r : ℕ)
    (hno : ¬∃ B,B∈matchings (indexedGraph A a b) (r+1))
    (t : ForestState A a b) :
    ∃ C : Finset (Fin n),IsVertexCover (indexedGraph (active t.val) a b) C ∧ C.card≤r := by
  apply cover_card_le_of_no_matching _ t.property.2 r
  rintro ⟨B,hB⟩
  apply hno
  exact ⟨B,matching_mem_of_graph_le _ _ (indexedGraph_mono t.property.1 a b) B (r+1) hB⟩

#check @forestState_small_cover
#print axioms matching_mem_of_graph_le
#print axioms forestState_small_cover
end MaxCaterpillar.ExponentialPush.DictionaryBridge
