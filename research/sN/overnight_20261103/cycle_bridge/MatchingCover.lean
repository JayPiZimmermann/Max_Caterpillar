import research.sN.exponential_push_20261102.forest_matching.Cover

/-! Every ordinary matching is no larger than an endpoint vertex cover.
This uses literal disjoint unordered graph edges, without a forest assumption. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge
open Frontier.RandomRestriction GrowingMatching ForestMatching
attribute [local instance] Classical.propDecidable
variable {n q r : ℕ}

/-- Each edge of a covered graph has an endpoint in the cover. -/
theorem edge_has_cover_endpoint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n)) (hC : IsVertexCover G C)
    (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
    ∃ v : Fin n, v ∈ C ∧ v ∈ GraphRestriction.edgeVertices e := by
  induction e using Sym2.ind with
  | h a b =>
    have hab := (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp he)
    rcases hC a b hab with ha | hb
    · exact ⟨a,ha,by rw [GraphRestriction.edgeVertices_mk]; simp⟩
    · exact ⟨b,hb,by rw [GraphRestriction.edgeVertices_mk]; simp⟩

/-- Choose one covered endpoint from every matching edge. Disjointness makes
this choice injective, so the matching cardinality is bounded by the cover. -/
theorem matching_card_le_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n)) (hC : IsVertexCover G C)
    (B : Finset (Sym2 (Fin n))) (hB : B ∈ matchings G q) :
    q ≤ C.card := by
  classical
  obtain ⟨hsub,hcard,hdisj⟩ := (mem_matchings G B).mp hB
  have hex : ∀ e : B, ∃ v : C, v.val ∈ GraphRestriction.edgeVertices e.val := by
    intro e
    obtain ⟨v,hvC,hve⟩ := edge_has_cover_endpoint G C hC e.val (hsub e.property)
    exact ⟨⟨v,hvC⟩,hve⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro e e' heq
    apply Subtype.ext
    by_contra hne
    have hd := hdisj e.val e.property e'.val e'.property hne
    have hv := hf e
    have hv' := hf e'
    have hval : (f e).val=(f e').val := congrArg Subtype.val heq
    rw [←hval] at hv'
    exact (Finset.disjoint_left.mp hd) hv hv'
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe,hcard] using hc

/-- A cover with at most r vertices excludes a matching of r+1 edges. -/
theorem no_matching_of_small_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n)) (hC : IsVertexCover G C) (hsize : C.card ≤ r) :
    ¬ ∃ B, B ∈ matchings G (r+1) := by
  rintro ⟨B,hB⟩
  have hh := (matching_card_le_cover G C hC B hB).trans hsize
  exact Nat.not_succ_le_self r hh

#check @matching_card_le_cover
#check @no_matching_of_small_cover
#print axioms edge_has_cover_endpoint
#print axioms matching_card_le_cover
#print axioms no_matching_of_small_cover
end MaxCaterpillar.ExponentialPush.CycleBridge
