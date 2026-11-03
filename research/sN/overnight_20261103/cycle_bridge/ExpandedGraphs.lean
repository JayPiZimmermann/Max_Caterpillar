import research.sN.overnight_20261103.cycle_bridge.NetworkExpansion
import research.sN.overnight_20261103.cycle_bridge.StateGraph

/-! Actual interaction graphs of the constructed finite network are forests
contained in the original signed graph of their parent second-hidden neuron. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ActualBraid DictionaryBridge FiniteIndex ForestMatching GrowingMatching
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

theorem expanded_graph_le_state (net : NormalizedNetwork N h₁ h₂)
    (d : (k : Fin h₂) → UnitState net k → ℝ)
    (hn : (expandedNetwork net d).TranslationNormalized)
    (t : ExpandedIndex net) :
    braidInteractionGraph (expandedNetwork net d) hn
      (Fintype.equivFin (ExpandedIndex net) t) ≤
      indexedGraph (active t.2.val) left right := by
  exact indexed_graph_le_state net Sigma.fst (fun t => t.2.val)
    (head net.L net.A net.B) (coefficient net.A net.B)
    (fun t => net.d t.1 * d t.1 t.2) hn t

/-- Every new actual interaction graph is a forest, even if coefficient
cancellation removes further edges from the forest-state graph. -/
theorem expanded_graph_acyclic (net : NormalizedNetwork N h₁ h₂)
    (d : (k : Fin h₂) → UnitState net k → ℝ)
    (hn : (expandedNetwork net d).TranslationNormalized)
    (k : Fin (Fintype.card (ExpandedIndex net))) :
    (braidInteractionGraph (expandedNetwork net d) hn k).IsAcyclic := by
  let t : ExpandedIndex net := (Fintype.equivFin (ExpandedIndex net)).symm k
  have hg := expanded_graph_le_state net d hn t
  rw [Equiv.apply_symm_apply] at hg
  exact acyclic_of_le hg t.2.property.2

/-- Each new neuron inherits a graph-subset relationship to one original
second-hidden index, not a union of unrelated original graphs. -/
theorem expanded_graph_le_original (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (d : (k : Fin h₂) → UnitState net k → ℝ)
    (hnew : (expandedNetwork net d).TranslationNormalized)
    (t : ExpandedIndex net) :
    braidInteractionGraph (expandedNetwork net d) hnew
      (Fintype.equivFin (ExpandedIndex net) t) ≤ braidInteractionGraph net hn t.1 := by
  have hg := (expanded_graph_le_state net d hnew t).trans
    (indexedGraph_mono t.2.property.1 left right)
  rwa [active_indexedGraph_eq net hn t.1] at hg

/-- An upper bound on the matching number of every original interaction
graph gives an actual cover of that size for every expanded neuron. -/
theorem expanded_small_covers (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (r : ℕ)
    (hno : ∀ k : Fin h₂, ¬ ∃ B, B ∈ matchings (braidInteractionGraph net hn k) (r+1))
    (d : (k : Fin h₂) → UnitState net k → ℝ)
    (hnew : (expandedNetwork net d).TranslationNormalized)
    (k : Fin (Fintype.card (ExpandedIndex net))) :
    ∃ C : Finset (Fin N), IsVertexCover
      (braidInteractionGraph (expandedNetwork net d) hnew k) C ∧ C.card ≤ r := by
  let t : ExpandedIndex net := (Fintype.equivFin (ExpandedIndex net)).symm k
  have hno' : ¬ ∃ B, B ∈ matchings
      (indexedGraph (activeEdges net.A (net.W t.1)) left right) (r+1) := by
    rw [active_indexedGraph_eq net hn t.1]
    exact hno t.1
  obtain ⟨C,hC,hsize⟩ := forestState_small_cover
    (activeEdges net.A (net.W t.1)) left right r hno' t.2
  refine ⟨C, ?_, hsize⟩
  have hg := expanded_graph_le_state net d hnew t
  rw [Equiv.apply_symm_apply] at hg
  intro a b hab
  exact hC a b (hg hab)

#check @expanded_small_covers
#print axioms expanded_graph_acyclic
#print axioms expanded_graph_le_original
#print axioms expanded_small_covers
end MaxCaterpillar.ExponentialPush.CycleBridge
