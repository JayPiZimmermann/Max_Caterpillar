import MaxCaterpillar.Frontier.RandomRestriction.FeedingWitness
import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Counting
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Configurations

/-! Count only original feeding rows, while retaining arbitrary output skips.
The remaining half-model moment and normalization transfer is separate. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
open BigOperators NormalizedNetwork Configurations NetworkLowerBound
variable {m h₁ h₂ : ℕ}

lemma core_graph_eq (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (k : Fin h₂) :
    braidInteractionGraph (core net) (core_normalized net hn) k=braidInteractionGraph net hn k := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (a≠b ∧ braidEdgeWeight (core net).A ((core net).W k) a b≠0) ↔ _
  rw [core_edgeWeight]
  rfl

theorem feeding_neuron_event_cover
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x) (K : ℕ) (T : ℝ)
    (hT : PerNeuron.UniformGapScale net T) :
    (Finset.univ : Finset (Configuration m)) ⊆
      badFirstConfigurations (supports (core net)) ∪ badIsolatedConfigurations m K ∪
      feedingBadConfigurationsThree (supports (core net)) K ∪
      Finset.univ.biUnion (PerNeuron.neuronEvent (core net) (core_normalized net hn) K T) := by
  classical
  intro ω _
  by_cases h₁ : ω∈badFirstConfigurations (supports (core net))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω∈badIsolatedConfigurations m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω∈feedingBadConfigurationsThree (supports (core net)) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  let f := StructuralWitness.fiveEmbedding (selectedSet ω.1) (selectedSet_card ω.1)
  have hf : Finset.univ.image f=selectedSet ω.1 := StructuralWitness.fiveEmbedding_image _ _
  have hno : ∀ j,net.Feeding j → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image f := by
    intro j hj hlarge hs
    have hrow : supports (core net) j=rowSupport (net.A j) := by
      simp only [supports,core,if_pos hj]
    apply h₁
    apply (mem_badFirstConfigurations _ _).mpr
    rw [hf] at hs
    exact ⟨j,hrow.symm ▸ hlarge,hrow.symm ▸ hs⟩
  have hcomp : Finset.univ.image (baseTail ω.1)=
      (Finset.univ : Finset (Fin (m+5))) \ Finset.univ.image f := by
    rw [hf]
    exact baseTail_image_complement_selectedSet ω.1
  obtain ⟨k,hzero,hmatch⟩ := structural_witness_of_generic_embedding_feeding
    net hn hnet f (baseTail ω.1) ω.2 T hcomp (hT ω.1 ω.2.1 ω.2.2) hno
  rw [hf] at hmatch
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨k,Finset.mem_univ _,(PerNeuron.mem_neuronEvent _ _ K T k ω).mpr ?_⟩
  refine ⟨h₃,?_,?_,?_⟩
  · exact fun hh => h₂ ((mem_rankCoordinateEvent _ _).mpr hh)
  · exact (core_inner net k _).trans hzero
  · apply hasTwoDisjointSelectedEdges_of_hasTwoDisjointEdgesOn
    rw [core_graph_eq net hn k]
    exact hmatch

/-- The full coefficient-counting prerequisite for an actual normalized MAX
model charges only the feeding support statistics of `core net`. Nonfeeding
output-only rows remain completely unrestricted. The explicit count budget
belongs to the subsequent half-restriction transfer. -/
theorem model_counting_feeding_on_tail
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x) (hm : 400≤m)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount (core net)≤(m+5).descFactorial 3) :
    NewCountingTradeoff.CountingPrerequisite 400 (m : ℝ)
      (regularizedMoment (core net) : ℝ) (h₂ : ℝ) := by
  classical
  intro K hK hsmall hmoment
  obtain ⟨B,_hB,hscale⟩ := PerNeuron.exists_uniform_gap_scale_threshold net
  obtain ⟨C,_hC,hcoreScale⟩ := PerNeuron.exists_uniform_gap_scale_threshold (core net)
  let T := max B C
  have hs := hscale T (le_max_left B C)
  have hc := hcoreScale T (le_max_right B C)
  have hE : ∀ k,(K : ℝ)^2*((PerNeuron.neuronEvent (core net) (core_normalized net hn) K T k).card : ℝ)≤
      400*(Fintype.card (Configuration m) : ℝ) := by
    intro k
    exact_mod_cast PerNeuron.neuron_event_card_le_four_hundred (core net) (core_normalized net hn)
      K T k hm hK hsmall hc
  have hpos : 0<m := lt_of_lt_of_le (by decide : 0<400) hm
  simpa only [Fintype.card_fin] using CountingUnion.counting_union_lower_bound
    (badFirstConfigurations (supports (core net))) (badIsolatedConfigurations m K)
    (feedingBadConfigurationsThree (supports (core net)) K)
    (PerNeuron.neuronEvent (core net) (core_normalized net hn) K T) (K : ℝ) 400
    (feeding_neuron_event_cover net hn hnet K T hs)
    (model_badFirst_quarter (core net) hbudget)
    (badIsolatedConfigurations_card_le K hpos hK hsmall)
    (model_feedingBad_quarter (core net) K hm hK hsmall hmoment) hE

#print axioms feeding_neuron_event_cover
#print axioms model_counting_feeding_on_tail
end MaxCaterpillar.Frontier.RandomRestriction.FeedingCore
