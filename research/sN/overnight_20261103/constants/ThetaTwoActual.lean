import research.sN.overnight_20261103.constants.ThetaTwo

/-! Actual neuron events at the stronger7/10 isolated-gap threshold.
The finite sample spaces and original neuron indices are retained exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Overnight.Constants.Theta
open BigOperators Frontier.RandomRestriction
open GrowingMatching GrowingMatching.Configurations DominantGap
open MaxCaterpillar.OvernightConstants.CherryConcentration
attribute [local instance] Classical.propDecidable
variable {k m h₁ h₂ : ℕ}

noncomputable def highActualNeuronEvent (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (r : Fin h₂) :
    Finset (Configuration k m) := by
  classical
  exact Finset.univ.filter fun ω =>
    ω.2.2 ∉ highBadIsolatedEvent m K ∧
    ActualClean net (baseTail ω.1) r ω.2.2 K ω.2.1 ∧
    net.inner r (actualPoint ω T)=0 ∧
    ω.1 ∈ selectedEvent (braidInteractionGraph net hn r) k 2

@[simp] theorem mem_highActualNeuronEvent (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (r : Fin h₂)
    (ω : Configuration k m) :
    ω ∈ highActualNeuronEvent net hn K T r ↔
      ω.2.2 ∉ highBadIsolatedEvent m K ∧
      ActualClean net (baseTail ω.1) r ω.2.2 K ω.2.1 ∧
      net.inner r (actualPoint ω T)=0 ∧
      ω.1 ∈ selectedEvent (braidInteractionGraph net hn r) k 2 := by
  classical
  simp only [highActualNeuronEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The actual recording-fiber rank estimate applies at every rank order.
The stronger rank event is retained while averaging; no independence premise
is introduced. -/
theorem highActualNeuron_fraction_le_selectedTailMean
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : CommonGapScale net T) :
    ((highActualNeuronEvent net hn K T r).card:ℝ)/Fintype.card (Configuration k m) ≤
      highSelectedTailMean (braidInteractionGraph net hn r)
        (fun σ => (braidInteractionGraph net hn r).comap (baseTail σ)) k K := by
  classical
  let E := highActualNeuronEvent net hn K T r
  have he : meanOver (fun ω : Configuration k m => if ω∈E then (1:ℝ) else 0)=
      meanOver (fun σ : FullPerm k m => meanOver (fun ρ : RankPerm m =>
        meanOver (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0))) := by
    rw [meanOver_prod]
    simp_rw [meanOver_prod]
    apply congrArg meanOver
    funext σ
    exact meanOver_comm (fun τ ρ => if (σ,τ,ρ)∈E then (1:ℝ) else 0)
  rw [←meanOver_indicator E,he]
  change meanOver (fun σ : FullPerm k m => meanOver (fun ρ : RankPerm m =>
      meanOver (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0))) ≤
    meanOver (fun σ : FullPerm k m => if σ∈selectedEvent (braidInteractionGraph net hn r) k 2 then
      meanOver (fun ρ : RankPerm m => if ρ∉highBadIsolatedEvent m K then
        lowRankMatchingMean ((braidInteractionGraph net hn r).comap (baseTail σ)) ρ K else 0)
      else 0)
  apply meanOver_mono
  intro σ
  by_cases hs : σ∈selectedEvent (braidInteractionGraph net hn r) k 2
  · rw [if_pos hs]
    apply meanOver_mono
    intro ρ
    by_cases hQ : ρ∉highBadIsolatedEvent m K
    · rw [if_pos hQ]
      have hh : (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0)=
          (fun τ : TailPerm m => if ActualClean net (baseTail σ) r ρ K τ ∧
            net.inner r (actualGapPoint (baseTail σ) (τ,ρ) T)=0 then (1:ℝ) else 0) := by
        funext τ
        simp only [E,mem_highActualNeuronEvent,hQ,hs,actualPoint,
          true_and,and_true,not_false_eq_true]
      rw [hh]
      exact actual_clean_mean_le_matching_mean net hn (baseTail σ) r ρ K T
        hscale.1 (fun τ => hscale.2 σ τ ρ)
    · rw [if_neg hQ]
      have hh : (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0)=fun _ => 0 := by
        funext τ
        apply if_neg
        intro hmem
        exact hQ ((mem_highActualNeuronEvent net hn K T r (σ,τ,ρ)).mp hmem).1
      rw [hh,meanOver_const]
  · rw [if_neg hs]
    have hh : (fun ρ : RankPerm m => meanOver
        (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0))=fun _ => 0 := by
      funext ρ
      have hh : (fun τ : TailPerm m => if (σ,τ,ρ)∈E then (1:ℝ) else 0)=fun _ => 0 := by
        funext τ
        simp only [E,mem_highActualNeuronEvent,hs,and_false,if_false]
      rw [hh,meanOver_const]
    rw [hh,meanOver_const]

/-- Closed upper bound for one original actual neuron event. -/
theorem highActualNeuron_fraction_le_two
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : CommonGapScale net T)
    (hm : 2≤m) (hK : 0<(K:ℝ)) :
    ((highActualNeuronEvent net hn K T r).card:ℝ)/Fintype.card (Configuration k m) ≤
      (2/7:ℝ)*((k.descFactorial 4:ℝ)/((m+k).descFactorial 4:ℝ))*
        ((highTailRate m K)^2)⁻¹*
          Real.exp (highTailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  apply (highActualNeuron_fraction_le_selectedTailMean net hn K T r hscale).trans
  apply highSelectedTailMean_le_two _ _ k K ((k:ℝ)*((m:ℝ)+(k:ℝ)-1))
    (Nat.le_add_left k m) hm hK
  intro σ
  apply Configurations.baseTail_edge_card_lower_bound
  exact le_trans (by decide : 1≤2) (hm.trans (Nat.le_add_right m k))

#check @highActualNeuron_fraction_le_two
#print axioms highActualNeuron_fraction_le_selectedTailMean
#print axioms highActualNeuron_fraction_le_two
end MaxCaterpillar.Overnight.Constants.Theta
