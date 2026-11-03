import research.sN.overnight_20261103.constants.SharpTwo

/-! The improved two-edge transfer with a separately supplied bound on the
literal bad-rank event. This is an internal assembly lemma, not a closed
network-width theorem. The original-row, survival and matching bridges remain
those of SharpTwo. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.Constants
open BigOperators Frontier.RandomRestriction
open GrowingMatching Configurations DominantGap
attribute [local instance] Classical.propDecidable
variable {m k h₁ h₂ : ℕ}

local instance parameterizedTotalNeZero [NeZero k] : NeZero (m+k) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.le_add_left k m))⟩

theorem conditional_finite_transfer_two_of_shortRank_bound [NeZero k]
    (H : LocalMatchingObstruction k 2)
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x = Maximum (m+k) x)
    (K : ℕ) (hm : 2 ≤ m) (htotal : 4 ≤ m+k) (hK : 0 < K) (hKm : K < m)
    (bQ : ℝ)
    (hQ : ((shortRankEvent k m K).card:ℝ)/Fintype.card (Configuration k m) ≤ bQ) :
    1-bQ-
      (BadFirst.largeSupportCount (firstSupports net):ℝ)*(k.descFactorial 3:ℝ)/((m+k).descFactorial 3:ℝ)-
      (∑ j, ((firstSupports net j).card.descFactorial 4:ℝ))/((m+k).descFactorial 4:ℝ)*
        ((K:ℝ)^2*(1+(k:ℝ)/(m:ℝ))/(1-(K:ℝ)/(m:ℝ))+
          (k.descFactorial 2:ℝ)*(K:ℝ)/2) ≤
      (h₂:ℝ)*(2/7:ℝ)*((k.descFactorial 4:ℝ)/((m+k).descFactorial 4:ℝ))*
        ((tailRate m K)^2)⁻¹*Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  classical
  obtain ⟨T,_hT,hscale⟩ := exists_common_gap_threshold net
  have hs := hscale T le_rfl
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hh := finite_union_fraction_bound
    (BadFirst.configurationBadFirstEvent k m (firstSupports net)) (shortRankEvent k m K)
    (feedingBadConfigurationsThree k (firstSupports net) K) (actualNeuronEvent net hn 2 K T)
    _ _ _ _ (actual_event_cover H (by decide : 0 < 2) net hn hnet K T hs)
    (BadFirst.configurationBadFirstEvent_fraction_le k m ((by decide : 3 ≤ 4).trans htotal) (firstSupports net))
    hQ
    ((le_of_eq (feedingBadConfigurationsThree_fraction k (firstSupports net) K)).trans
      (GoodEvent.feedingBadFraction_le k (firstSupports net) K hmpos hKm htotal))
    (fun r => actualNeuron_fraction_le_two net hn K T r hs hm hKpos)
  simp only [Fintype.card_fin] at hh
  convert hh using 1 <;> ring

#check @conditional_finite_transfer_two_of_shortRank_bound
#print axioms conditional_finite_transfer_two_of_shortRank_bound
end MaxCaterpillar.Overnight.Constants
