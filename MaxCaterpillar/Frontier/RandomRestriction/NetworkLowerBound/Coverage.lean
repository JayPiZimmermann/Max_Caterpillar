import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.SupportMoment
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronModel
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Configurations

/-! # Actual five-set witnesses cover every nonexceptional configuration -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
open Configurations DominantGap
variable {m h₁ h₂ : ℕ}

theorem actual_neuron_event_cover
    (hcoeff : StructuralWitness.ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x) (K : ℕ) (T : ℝ)
    (hT : PerNeuron.UniformGapScale net T) :
    (Finset.univ : Finset (Configuration m)) ⊆
      badFirstConfigurations (supports net) ∪ badIsolatedConfigurations m K ∪
      feedingBadConfigurationsThree (supports net) K ∪
      Finset.univ.biUnion (PerNeuron.neuronEvent net hn K T) := by
  classical
  intro ω _
  by_cases h₁ : ω∈badFirstConfigurations (supports net)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω∈badIsolatedConfigurations m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω∈feedingBadConfigurationsThree (supports net) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  have hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆selectedSet ω.1 := by
    intro j hj hs
    exact h₁ ((mem_badFirstConfigurations _ _).mpr ⟨j,hj,hs⟩)
  obtain ⟨k,hzero,hmatch⟩ := StructuralWitness.structural_witness_on_five_set_of_generic
    hcoeff net hn hnet (selectedSet ω.1) (selectedSet_card ω.1)
    (baseTail ω.1) ω.2 T (baseTail_image_complement_selectedSet ω.1)
    (hT ω.1 ω.2.1 ω.2.2) hno
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨k,Finset.mem_univ _,(PerNeuron.mem_neuronEvent net hn K T k ω).mpr ?_⟩
  refine ⟨h₃,?_,hzero,?_⟩
  · exact fun hh => h₂ ((mem_rankCoordinateEvent _ _).mpr hh)
  · apply hasTwoDisjointSelectedEdges_of_hasTwoDisjointEdgesOn
    convert hmatch using 1

#print axioms actual_neuron_event_cover
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
