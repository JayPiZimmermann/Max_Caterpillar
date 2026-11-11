import research.sN.overnight_20261103.constants.SharpTwo
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.FeedingCounting

/-! Sharp two-edge counting charges only original feeding rows. Output-only
first neurons are unrestricted, and no auxiliary output neuron is counted.
The masked core need not compute MAX: exactness is used only on the original
network when extracting the structural witness. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Feeding
open BigOperators Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Configurations DominantGap NormalizedNetwork
attribute [local instance] Classical.propDecidable
variable {m h₁ h₂ : ℕ}

local instance feedingTotalNeZero : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

/-- Convert the actual original two-edge witness without discarding its
selected endpoint set. -/
lemma matchingOn_two_of_embedded_twoDisjoint {N : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (f : Fin 5 ↪ Fin N)
    (h : HasTwoDisjointEdgesOn G (Finset.univ.image f)) :
    HasMatchingOn G 2 (Finset.univ.image f) := by
  have ht : HasTwoDisjointEdgesOn (G.comap f) Finset.univ :=
    (hasTwoDisjointEdgesOn_comap_iff G f Finset.univ).mpr h
  obtain ⟨B,hB,_⟩ := hasMatchingOn_two_of_twoDisjoint (G.comap f) ht
  have hi : (fun a b => Classical.propDecidable ((G.comap f).Adj a b)) =
      (fun a b => SimpleGraph.instDecidableComapAdj f G a b) := Subsingleton.elim _ _
  rw [hi] at hB
  exact transport_matching G f B hB

/-- The cover retains original second-hidden indices while excluding only
non-braid first rows that feed some original second-hidden neuron. -/
theorem actual_event_cover
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum (m+5) x)
    (K : ℕ) (T : ℝ) (hscale : CommonGapScale net T) :
    (Finset.univ : Finset (Configuration 5 m)) ⊆
      BadFirst.configurationBadFirstEvent 5 m (firstSupports (FeedingCore.core net)) ∪
      shortRankEvent 5 m K ∪
      feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K ∪
      Finset.univ.biUnion
        (actualNeuronEvent (FeedingCore.core net) (FeedingCore.core_normalized net hn) 2 K T) := by
  classical
  intro ω _
  by_cases h₁ : ω ∈ BadFirst.configurationBadFirstEvent 5 m (firstSupports (FeedingCore.core net))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω ∈ shortRankEvent 5 m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω ∈ feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  have hno : ∀ j, net.Feeding j → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j) ⊆ Finset.univ.image (selectedEmbedding ω.1) := by
    intro j hj hlarge hs
    have hrow : firstSupports (FeedingCore.core net) j=rowSupport (net.A j) := by
      simp only [firstSupports,FeedingCore.core,if_pos hj]
    apply h₁
    apply (BadFirst.mem_configurationBadFirstEvent 5 m
      (firstSupports (FeedingCore.core net)) ω).mpr
    rw [GrowingMatching.Configurations.selectedEmbedding_image] at hs
    exact ⟨j,hrow.symm ▸ hlarge,hrow.symm ▸ hs⟩
  have hcomp : Finset.univ.image (baseTail ω.1)=
      (Finset.univ : Finset (Fin (m+5))) \ Finset.univ.image (selectedEmbedding ω.1) := by
    rw [GrowingMatching.Configurations.selectedEmbedding_image]
    exact baseTail_image_complement_selectedLabels ω.1
  obtain ⟨r,hzero,htwo⟩ := FeedingCore.structural_witness_of_generic_embedding_feeding
    net hn hnet (selectedEmbedding ω.1) (baseTail ω.1) ω.2 T hcomp
    (hscale.2 ω.1 ω.2.1 ω.2.2) hno
  have hmatch := matchingOn_two_of_embedded_twoDisjoint
    (braidInteractionGraph net hn r) (selectedEmbedding ω.1) htwo
  rw [GrowingMatching.Configurations.selectedEmbedding_image] at hmatch
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,(mem_actualNeuronEvent _ _ 2 K T r ω).mpr ?_⟩
  refine ⟨fun h => h₂ ((mem_shortRankEvent 5 m K ω).mpr h),
    good_implies_actualClean (FeedingCore.core net) (FeedingCore.core_normalized net hn)
      K r ω.1 ω.2.1 ω.2.2 h₃,?_,?_⟩
  · exact (FeedingCore.core_inner net r _).trans hzero
  · apply (mem_selectedEvent _ ω.1).mpr
    rw [FeedingCore.core_graph_eq net hn r]
    exact hmatch

/-- Internal feeding-only finite transfer. The displayed bad-rank bound is
on the literal permutation event; no cost, support or structural estimate is
assumed for the original coefficient arrays. -/
theorem finite_transfer_of_shortRank_bound
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum (m+5) x)
    (K : ℕ) (hm : 2≤m) (hK : 0<K) (hKm : K<m) (bQ : ℝ)
    (hQ : ((shortRankEvent 5 m K).card:ℝ)/Fintype.card (Configuration 5 m)≤bQ) :
    1-bQ-
      (GrowingMatching.BadFirst.largeSupportCount (firstSupports (FeedingCore.core net)):ℝ)*60/
        ((m+5).descFactorial 3:ℝ)-
      (∑ j, ((firstSupports (FeedingCore.core net) j).card.descFactorial 4:ℝ))/
        ((m+5).descFactorial 4:ℝ)*
        ((K:ℝ)^2*(1+5/(m:ℝ))/(1-(K:ℝ)/(m:ℝ))+10*(K:ℝ)) ≤
      (h₂:ℝ)*(2/7:ℝ)*(120/((m+5).descFactorial 4:ℝ))*
        ((tailRate m K)^2)⁻¹*Real.exp (tailRate m K*(5*((m:ℝ)+4))) := by
  classical
  obtain ⟨B,_hB,hscale⟩ := exists_common_gap_threshold net
  obtain ⟨C,_hC,hcoreScale⟩ := exists_common_gap_threshold (FeedingCore.core net)
  let T : ℝ := max B C
  have hs := hscale T (le_max_left B C)
  have hc := hcoreScale T (le_max_right B C)
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hKpos : (0:ℝ)<K := by exact_mod_cast hK
  have htotal : 4≤m+5 := (by decide : 4≤5).trans (Nat.le_add_left 5 m)
  have hh := finite_union_fraction_bound
    (BadFirst.configurationBadFirstEvent 5 m (firstSupports (FeedingCore.core net)))
    (shortRankEvent 5 m K)
    (feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K)
    (actualNeuronEvent (FeedingCore.core net) (FeedingCore.core_normalized net hn) 2 K T)
    _ _ _ _ (actual_event_cover net hn hnet K T hs)
    (BadFirst.configurationBadFirstEvent_fraction_le 5 m ((by decide : 3≤4).trans htotal)
      (firstSupports (FeedingCore.core net))) hQ
    ((le_of_eq (feedingBadConfigurationsThree_fraction 5
      (firstSupports (FeedingCore.core net)) K)).trans
      (GoodEvent.feedingBadFraction_le 5 (firstSupports (FeedingCore.core net))
        K hmpos hKm htotal))
    (fun r => actualNeuron_fraction_le_two (FeedingCore.core net)
      (FeedingCore.core_normalized net hn) K T r hc hm hKpos)
  simp only [Fintype.card_fin,show (5:ℕ).descFactorial 3=60 by decide,
    show (5:ℕ).descFactorial 2=20 by decide,show (5:ℕ).descFactorial 4=120 by decide,
    Nat.cast_ofNat] at hh
  convert hh using 1 <;> ring

#check @actual_event_cover
#check @finite_transfer_of_shortRank_bound
#print axioms matchingOn_two_of_embedded_twoDisjoint
#print axioms actual_event_cover
#print axioms finite_transfer_of_shortRank_bound
end MaxCaterpillar.Overnight.Constants.Feeding
