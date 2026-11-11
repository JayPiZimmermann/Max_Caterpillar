import research.sN.overnight_20261103.constants.ThetaTwoTransfer
import research.sN.overnight_20261103.constants.FeedingSharpTwo

/-! The stronger isolated-gap rate for original feeding rows only.
The original network supplies exactness; the masked core supplies only
the unchanged original inner functions and interaction graphs. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Theta.Feeding
open BigOperators Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Configurations DominantGap
open MaxCaterpillar.OvernightConstants.CherryConcentration
attribute [local instance] Classical.propDecidable
variable {m h₁ h₂ : ℕ}

local instance feedingThetaTotalNeZero : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

/-- Upgrade the existing original-slot feeding cover to the stronger rank
event. The support and structural parts are exactly the same proved cover. -/
theorem high_actual_event_cover
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (K : ℕ) (T : ℝ) (hscale : CommonGapScale net T) :
    (Finset.univ : Finset (Configuration 5 m)) ⊆
      GrowingMatching.BadFirst.configurationBadFirstEvent 5 m (firstSupports (FeedingCore.core net)) ∪
      highShortRankEvent 5 m K ∪
      feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K ∪
      Finset.univ.biUnion
        (highActualNeuronEvent (FeedingCore.core net) (FeedingCore.core_normalized net hn) K T) := by
  classical
  intro ω _
  by_cases h₁ : ω∈GrowingMatching.BadFirst.configurationBadFirstEvent 5 m
      (firstSupports (FeedingCore.core net))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h₁))
  by_cases h₂ : ω∈highShortRankEvent 5 m K
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₂))
  by_cases h₃ : ω∈feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h₃)
  have hgood : ω.2.2∉highBadIsolatedEvent m K :=
    fun h => h₂ ((mem_highShortRankEvent 5 m K ω).mpr h)
  have hold := MaxCaterpillar.Overnight.Constants.Feeding.actual_event_cover
    net hn hnet K T hscale (Finset.mem_univ ω)
  simp only [Finset.mem_union,h₁,h₃,false_or,or_false] at hold
  have hevents : ω∈Finset.univ.biUnion
      (actualNeuronEvent (FeedingCore.core net) (FeedingCore.core_normalized net hn) 2 K T) := by
    rcases hold with hbad|hevents
    · exact False.elim ((high_good_implies_old_good ω.2.2 K hgood)
        ((mem_shortRankEvent 5 m K ω).mp hbad))
    · exact hevents
  obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hevents
  have hparts := (mem_actualNeuronEvent (FeedingCore.core net)
    (FeedingCore.core_normalized net hn) 2 K T r ω).mp hr
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,?_⟩
  exact (mem_highActualNeuronEvent (FeedingCore.core net)
    (FeedingCore.core_normalized net hn) K T r ω).mpr ⟨hgood,hparts.2⟩

/-- Actual feeding-only finite transfer at rate49K/(120m(m−1)). The sole
numerical input is a bound on the explicitly displayed finite bad-rank event. -/
theorem finite_transfer_of_highShortRank_bound
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (K : ℕ) (hm : 2≤m) (hK : 0<K) (hKm : K<m) (bQ : ℝ)
    (hQ : ((highShortRankEvent 5 m K).card:ℝ)/Fintype.card (Configuration 5 m)≤bQ) :
    1-bQ-
      (GrowingMatching.BadFirst.largeSupportCount (firstSupports (FeedingCore.core net)):ℝ)*60/
        ((m+5).descFactorial 3:ℝ)-
      (∑ j,((firstSupports (FeedingCore.core net) j).card.descFactorial 4:ℝ))/
        ((m+5).descFactorial 4:ℝ)*
        ((K:ℝ)^2*(1+5/(m:ℝ))/(1-(K:ℝ)/(m:ℝ))+10*(K:ℝ)) ≤
      (h₂:ℝ)*(2/7:ℝ)*(120/((m+5).descFactorial 4:ℝ))*
        ((highTailRate m K)^2)⁻¹*Real.exp (highTailRate m K*(5*((m:ℝ)+4))) := by
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
    (GrowingMatching.BadFirst.configurationBadFirstEvent 5 m (firstSupports (FeedingCore.core net)))
    (highShortRankEvent 5 m K)
    (feedingBadConfigurationsThree 5 (firstSupports (FeedingCore.core net)) K)
    (highActualNeuronEvent (FeedingCore.core net) (FeedingCore.core_normalized net hn) K T)
    _ _ _ _ (high_actual_event_cover net hn hnet K T hs)
    (GrowingMatching.BadFirst.configurationBadFirstEvent_fraction_le 5 m
      ((by decide : 3≤4).trans htotal) (firstSupports (FeedingCore.core net))) hQ
    ((le_of_eq (feedingBadConfigurationsThree_fraction 5
      (firstSupports (FeedingCore.core net)) K)).trans
      (GoodEvent.feedingBadFraction_le 5 (firstSupports (FeedingCore.core net))
        K hmpos hKm htotal))
    (fun r => highActualNeuron_fraction_le_two (FeedingCore.core net)
      (FeedingCore.core_normalized net hn) K T r hc hm hKpos)
  simp only [Fintype.card_fin,show (5:ℕ).descFactorial 3=60 by decide,
    show (5:ℕ).descFactorial 2=20 by decide,show (5:ℕ).descFactorial 4=120 by decide,
    Nat.cast_ofNat] at hh
  convert hh using 1 <;> ring

#check @finite_transfer_of_highShortRank_bound
#print axioms high_actual_event_cover
#print axioms finite_transfer_of_highShortRank_bound
end MaxCaterpillar.Overnight.Constants.Theta.Feeding
