import research.sN.overnight_20261103.constants.ThetaTwoActual

/-! Finite actual-network transfer with the stronger isolated-gap threshold.
The structural obstruction and the literal bad-rank estimate are explicit
internal inputs. Every other event and model bridge is proved here/imported. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Theta
open BigOperators Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Configurations DominantGap
open MaxCaterpillar.OvernightConstants.CherryConcentration
attribute [local instance] Classical.propDecidable
variable {k m h₁ h₂ : ℕ}

local instance transferTotalNeZero [NeZero k] : NeZero (m+k) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.le_add_left k m))⟩

noncomputable def highShortRankEvent (k m K : ℕ) : Finset (Configuration k m) :=
  pullbackEvent ((Finset.univ : Finset (FullPerm k m)) ×ˢ highBadIsolatedEvent m K)

@[simp] lemma mem_highShortRankEvent (k m K : ℕ) (ω : Configuration k m) :
    ω∈highShortRankEvent k m K ↔ ω.2.2∈highBadIsolatedEvent m K := by
  classical
  simp only [highShortRankEvent,mem_pullbackEvent,Finset.mem_product,Finset.mem_univ,
    true_and,effectiveConfiguration]

theorem highShortRankEvent_fraction (k m K : ℕ) :
    ((highShortRankEvent k m K).card:ℝ)/Fintype.card (Configuration k m)=
      ((highBadIsolatedEvent m K).card:ℝ)/Fintype.card (RankPerm m) := by
  rw [highShortRankEvent,pullbackEvent_fraction,Finset.card_product,Finset.card_univ,
    Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  apply mul_div_mul_left
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (FullPerm k m)≠0)

theorem high_actual_event_cover [NeZero k]
    (H : LocalMatchingObstruction k 2)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+k) x)
    (K : ℕ) (T : ℝ) (hscale : CommonGapScale net T) :
    (Finset.univ : Finset (Configuration k m)) ⊆
      GrowingMatching.BadFirst.configurationBadFirstEvent k m (firstSupports net) ∪
      highShortRankEvent k m K ∪
      feedingBadConfigurationsThree k (firstSupports net) K ∪
      Finset.univ.biUnion (highActualNeuronEvent net hn K T) := by
  classical
  intro ω _
  by_cases h₁ : ω∈GrowingMatching.BadFirst.configurationBadFirstEvent k m (firstSupports net)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω∈highShortRankEvent k m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω∈feedingBadConfigurationsThree k (firstSupports net) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  have hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image (selectedEmbedding ω.1) := by
    intro j hj hs
    rw [Configurations.selectedEmbedding_image] at hs
    exact h₁ ((GrowingMatching.BadFirst.mem_configurationBadFirstEvent
      k m (firstSupports net) ω).mpr ⟨j,hj,hs⟩)
  have hcomp : Finset.univ.image (baseTail ω.1)=
      (Finset.univ : Finset (Fin (m+k))) \ Finset.univ.image (selectedEmbedding ω.1) := by
    rw [Configurations.selectedEmbedding_image]
    exact baseTail_image_complement_selectedLabels ω.1
  obtain ⟨r,hzero,hselected⟩ := selected_event_witness_of_generic_embedding
    H (by decide : 0<2) net hn hnet
    (selectedEmbedding ω.1) (baseTail ω.1) ω.2 T hcomp
    (hscale.2 ω.1 ω.2.1 ω.2.2) ω.1 (Configurations.selectedEmbedding_image ω.1) hno
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,(mem_highActualNeuronEvent net hn K T r ω).mpr ?_⟩
  exact ⟨fun h => h₂ ((mem_highShortRankEvent k m K ω).mpr h),
    good_implies_actualClean net hn K r ω.1 ω.2.1 ω.2.2 h₃,hzero,
    (mem_selectedEvent (braidInteractionGraph net hn r) ω.1).mpr hselected⟩

/-- This internal assembly accepts only a bound on the actual rank event.
In the closed numerical corollary that bound comes from a proved variance
estimate on the same finite permutation space. -/
theorem conditional_finite_transfer_two_of_highShortRank_bound [NeZero k]
    (H : LocalMatchingObstruction k 2)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+k) x)
    (K : ℕ) (hm : 2≤m) (htotal : 4≤m+k) (hK : 0<K) (hKm : K<m)
    (bQ : ℝ)
    (hQ : ((highShortRankEvent k m K).card:ℝ)/Fintype.card (Configuration k m)≤bQ) :
    1-bQ-
      (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ)*
        (k.descFactorial 3:ℝ)/((m+k).descFactorial 3:ℝ)-
      (∑ j,((firstSupports net j).card.descFactorial 4:ℝ))/((m+k).descFactorial 4:ℝ)*
        ((K:ℝ)^2*(1+(k:ℝ)/(m:ℝ))/(1-(K:ℝ)/(m:ℝ))+
          (k.descFactorial 2:ℝ)*(K:ℝ)/2) ≤
      (h₂:ℝ)*(2/7:ℝ)*((k.descFactorial 4:ℝ)/((m+k).descFactorial 4:ℝ))*
        ((highTailRate m K)^2)⁻¹*
          Real.exp (highTailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  classical
  obtain ⟨T,_hT,hscale⟩ := exists_common_gap_threshold net
  have hs := hscale T le_rfl
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<2) hm
  have hKpos : (0:ℝ)<K := by exact_mod_cast hK
  have hh := finite_union_fraction_bound
    (GrowingMatching.BadFirst.configurationBadFirstEvent k m (firstSupports net))
    (highShortRankEvent k m K)
    (feedingBadConfigurationsThree k (firstSupports net) K) (highActualNeuronEvent net hn K T)
    _ _ _ _ (high_actual_event_cover H net hn hnet K T hs)
    (GrowingMatching.BadFirst.configurationBadFirstEvent_fraction_le
      k m ((by decide : 3≤4).trans htotal) (firstSupports net)) hQ
    ((le_of_eq (feedingBadConfigurationsThree_fraction k (firstSupports net) K)).trans
      (GoodEvent.feedingBadFraction_le k (firstSupports net) K hmpos hKm htotal))
    (fun r => highActualNeuron_fraction_le_two net hn K T r hs hm hKpos)
  simp only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

#check @conditional_finite_transfer_two_of_highShortRank_bound
#print axioms highShortRankEvent_fraction
#print axioms high_actual_event_cover
#print axioms conditional_finite_transfer_two_of_highShortRank_bound
end MaxCaterpillar.Overnight.Constants.Theta
