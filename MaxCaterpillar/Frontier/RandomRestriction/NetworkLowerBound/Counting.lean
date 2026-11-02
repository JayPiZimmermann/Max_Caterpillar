import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Coverage
import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.Scalar
import MaxCaterpillar.Frontier.RandomRestriction.CountingUnion
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuron

/-! # The counting prerequisite derived from actual network events -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
open Configurations
variable {m n h₁ h₂ : ℕ}

theorem model_counting_on_tail_of_coefficients
    (hcoeff : StructuralWitness.ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x) (hm : 400≤m)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount net≤(m+5).descFactorial 3) :
    NewCountingTradeoff.CountingPrerequisite 400 (m : ℝ)
      (regularizedMoment net : ℝ) (h₂ : ℝ) := by
  classical
  intro K hK hsmall hmoment
  obtain ⟨T,_hT,hscale⟩ := PerNeuron.exists_uniform_gap_scale_threshold net
  have hs := hscale T le_rfl
  have hE : ∀ k,(K : ℝ)^2*((PerNeuron.neuronEvent net hn K T k).card : ℝ)≤
      400*(Fintype.card (Configuration m) : ℝ) := by
    intro k
    exact_mod_cast PerNeuron.neuron_event_card_le_four_hundred net hn K T k hm hK hsmall hs
  have hpos : 0<m := lt_of_lt_of_le (by decide : 0<400) hm
  simpa only [Fintype.card_fin] using CountingUnion.counting_union_lower_bound
    (badFirstConfigurations (supports net)) (badIsolatedConfigurations m K)
    (feedingBadConfigurationsThree (supports net) K)
    (PerNeuron.neuronEvent net hn K T) (K : ℝ) 400
    (actual_neuron_event_cover hcoeff net hn hnet K T hs)
    (model_badFirst_quarter net hbudget)
    (badIsolatedConfigurations_card_le K hpos hK hsmall)
    (model_feedingBad_quarter net K hm hK hsmall hmoment) hE

theorem model_counting_of_coefficients [NeZero n]
    (hcoeff : StructuralWitness.ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x) (hsize : 520≤n)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount net≤n.descFactorial 3) :
    NewCountingTradeoff.CountingPrerequisite 400 ((n : ℝ)-5)
      (regularizedMoment net : ℝ) (h₂ : ℝ) := by
  obtain ⟨m,rfl⟩ : ∃ m,n=m+5 :=
    ⟨n-5,(Nat.sub_add_cancel ((by decide : 5≤520).trans hsize)).symm⟩
  have hm : 400≤m := by linarith only [hsize]
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_sub_cancel] using
    model_counting_on_tail_of_coefficients hcoeff net hn hnet hm hbudget

#print axioms model_counting_on_tail_of_coefficients
#print axioms model_counting_of_coefficients
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
