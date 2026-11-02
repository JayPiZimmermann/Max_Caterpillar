import MaxCaterpillar.Frontier.RandomRestriction.PerNeuron

set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron.Check
open BigOperators Configurations GoodEvent DominantGap
attribute [local instance] braidGraphDecidable

/-- Unfold the actual event down to the independently defined full/rank good
event and the original network preactivation, retaining all three samples. -/
example {m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (k : Fin h₂)
    (σ : FullPerm m) (τ : TailPerm m) (ρ : RankPerm m) :
    (σ,τ,ρ)∈neuronEvent net hn K T k ↔
      (effectivePermutation σ τ,ρ)∉GoodEvent.feedingBadConfigurations
        (fun j => NormalizedNetwork.rowSupport (net.A j)) K ∧
      ρ∉badIsolatedEvent m K ∧
      net.inner k (actualGapPoint (baseTail σ) (τ,ρ) T)=0 ∧
      GraphRestriction.hasTwoDisjointSelectedEdges (braidInteractionGraph net hn k) σ := by
  classical
  rw [mem_neuronEvent]
  simp only [feedingBadConfigurationsThree,mem_pullbackEvent,firstSupports,
    actualPoint,effectiveConfiguration]
  rfl

/-- Independent expected type for the actual finite event count. -/
example {m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (k : Fin h₂)
    (hm : 400≤m) (hKlow : 4≤K) (hKhigh : (K:ℝ)≤(m:ℝ)/100)
    (hscale : ∀ σ : Equiv.Perm (Fin (m+5)), ∀ τ ρ : Equiv.Perm (Fin m),
      GenericNetworkPoint net (baseTail σ) (τ,ρ) T) :
    K^2*(neuronEvent net hn K T k).card ≤
      400*Fintype.card (Equiv.Perm (Fin (m+5)) × Equiv.Perm (Fin m) × Equiv.Perm (Fin m)) :=
  neuron_event_card_le_four_hundred net hn K T k hm hKlow hKhigh hscale

/-- No genericity, rank, probability, event count, MAX, or coefficient
certificate premise is imposed on this actual-network threshold theorem. -/
example {m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) :
    ∃ B : ℝ, 2≤B ∧ ∀ T : ℝ, B≤T → ∀ K : ℕ, ∀ k : Fin h₂,
      400≤m → 4≤K → (K:ℝ)≤(m:ℝ)/100 →
      K^2*(neuronEvent net hn K T k).card ≤
        400*Fintype.card (Configuration m) :=
  exists_neuron_event_counting_threshold net hn

noncomputable def sampleNetwork : NormalizedNetwork 405 0 1 where
  A := 0
  U := 0
  W := 0
  L := unitVec 0
  B := 0
  d := 0

theorem sample_translation : sampleNetwork.TranslationNormalized := by
  simp [NormalizedNetwork.TranslationNormalized,sampleNetwork,unitVec]

/-- Boundary parameters and an actual normalized network with one second
neuron witness that the headline hypotheses are jointly satisfiable. -/
example : ∃ B : ℝ, 2≤B ∧ ∀ T : ℝ, B≤T →
    4^2*(neuronEvent sampleNetwork sample_translation 4 T 0).card ≤
      400*Fintype.card (Configuration 400) := by
  obtain ⟨B,hB,h⟩ := exists_neuron_event_counting_threshold sampleNetwork sample_translation
  exact ⟨B,hB,fun T hT => h T hT 4 0 (by norm_num) (by norm_num) (by norm_num)⟩

#check @firstSupports
#check @actualPoint
#check @neuronEvent
#check @UniformGapScale
#check @neuron_event_card_le_four_hundred
#check @exists_neuron_event_counting_threshold
#print axioms outer_density_fiber_count_le
#print axioms outer_density_event_card_le
#print axioms mem_tailFiber
#print axioms card_eq_sum_tailFiber
#print axioms sum_by_recording
#print axioms clean_survival_card_le_sum
#print axioms nativeMatchingCount_recorded_eq
#print axioms enumerated_matchingCount_eq
#print axioms enumeratedSlot_false
#print axioms enumeratedSlot_true
#print axioms native_matching_counting_le_four_hundred
#print axioms uniform_gap_scale_pos
#print axioms exists_uniform_gap_scale_threshold
#print axioms mem_neuronEvent
#print axioms good_implies_actualClean
#print axioms native_braid_matchingCount_eq
#print axioms baseTail_eq_tailLabelEmbedding
#print axioms tail_braidGraph_edge_lower_bound
#print axioms neuron_tail_card_le_of_clean_fiber_bound
#print axioms neuron_event_card_le_of_clean_fiber_bounds
#print axioms activeMatchingEdges_card_eq_native
#print axioms neuron_event_card_le_four_hundred
#print axioms exists_neuron_event_counting_threshold

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron.Check
