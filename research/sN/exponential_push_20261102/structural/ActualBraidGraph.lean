import research.sN.exponential_push_20261102.structural.ActualBraid
import research.sN.exponential_push_20261102.forest_matching.Cycle
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph

set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.ActualBraid
open Frontier Frontier.RandomRestriction
variable {N h₁ h₂ : ℕ}

/-- The graph used by finite forest expansion is exactly the original signed
interaction graph, including every cancellation among parallel rows. -/
theorem active_indexedGraph_eq (net : NormalizedNetwork N h₁ h₂)
    (hnorm : net.TranslationNormalized) (k : Fin h₂) :
    ForestMatching.indexedGraph (activeEdges net.A (net.W k)) left right=
      braidInteractionGraph net hnorm k := by
  classical
  apply SimpleGraph.ext
  funext a b
  apply propext
  constructor
  · rintro ⟨hab,p,hp,hpab⟩
    have hc := (activeEdges_original net.A (net.W k) p).mp hp
    refine ⟨hab,?_⟩
    rcases hpab with ⟨ha,hb⟩|⟨hb,ha⟩
    · simpa only [ha,hb] using hc
    · rw [braidEdgeWeight_symm net.A (net.W k) hnorm.1 a b]
      simpa only [ha,hb] using hc
  · rintro ⟨hab,hw⟩
    refine ⟨hab,?_⟩
    rcases lt_or_gt_of_ne hab with hlt|hlt
    · let p : Pair N := ⟨(a,b),hlt⟩
      refine ⟨p,(activeEdges_original net.A (net.W k) p).mpr hw,Or.inl ?_⟩
      exact ⟨rfl,rfl⟩
    · let p : Pair N := ⟨(b,a),hlt⟩
      have hw' : braidEdgeWeight net.A (net.W k) (left p) (right p)≠0 := by
        change braidEdgeWeight net.A (net.W k) b a≠0
        rw [braidEdgeWeight_symm net.A (net.W k) hnorm.1 b a]
        exact hw
      exact ⟨p,(activeEdges_original net.A (net.W k) p).mpr hw',Or.inr ⟨rfl,rfl⟩⟩

#print axioms active_indexedGraph_eq
end MaxCaterpillar.ExponentialPush.ActualBraid
