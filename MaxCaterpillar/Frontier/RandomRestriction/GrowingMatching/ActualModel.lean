import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Configurations
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiniteMeans
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ActualRank

/-! # Actual growing-arity clean neuron cost

All sample spaces are actual uniform permutation spaces. Cleanliness is the
literal original-row dominant-gap condition. No survival, rank or probability
bound is imposed on the actual coefficient arrays.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators Configurations DominantGap
attribute [local instance] Classical.propDecidable
variable {k m h₁ h₂ : ℕ}

noncomputable def actualPoint (ω : Configuration k m) (T : ℝ) : Point (m+k) :=
  actualGapPoint (baseTail ω.1) (ω.2.1,ω.2.2) T

/-- One positive actual scale works simultaneously across every full, tail,
and rank permutation. It is derived from the original arrays below. -/
def CommonGapScale (net : NormalizedNetwork (m+k) h₁ h₂) (T : ℝ) : Prop :=
  0<T ∧ ∀σ : FullPerm k m,∀τ : TailPerm m,∀ρ : RankPerm m,
    GenericNetworkPoint net (baseTail σ) (τ,ρ) T

theorem exists_common_gap_threshold (net : NormalizedNetwork (m+k) h₁ h₂) :
    ∃ B : ℝ,2≤B ∧ ∀T : ℝ,B≤T → CommonGapScale net T := by
  classical
  choose bound hbound hstable using fun σ : FullPerm k m =>
    exists_network_gap_threshold net (baseTail σ)
  let B : ℝ :=2+∑σ : FullPerm k m,bound σ
  have hn : ∀σ : FullPerm k m,0≤bound σ :=
    fun σ=>le_trans (by norm_num) (hbound σ)
  have hsum : 0≤∑σ : FullPerm k m,bound σ := Finset.sum_nonneg fun σ _=>hn σ
  have hB : 2≤B := by dsimp only [B];linarith only [hsum]
  refine ⟨B,hB,?_⟩
  intro T hT
  refine ⟨lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hB.trans hT),?_⟩
  intro σ τ ρ
  apply hstable σ T _ (τ,ρ)
  have hσ : bound σ≤∑σ : FullPerm k m,bound σ :=
    Finset.single_le_sum (fun υ _=>hn υ) (Finset.mem_univ σ)
  dsimp only [B] at hT
  linarith only [hσ,hT]

/-- Literal actual clean survival with a selected q-edge matching. -/
noncomputable def actualNeuronEvent (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂) :
    Finset (Configuration k m) := by
  classical
  exact Finset.univ.filter fun ω=>
    ω.2.2∉GoodEvent.badIsolatedEvent m K ∧
    ActualClean net (baseTail ω.1) r ω.2.2 K ω.2.1 ∧
    net.inner r (actualPoint ω T)=0 ∧
    ω.1∈selectedEvent (braidInteractionGraph net hn r) k q

@[simp] theorem mem_actualNeuronEvent (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (ω : Configuration k m) :
    ω∈actualNeuronEvent net hn q K T r ↔
      ω.2.2∉GoodEvent.badIsolatedEvent m K ∧
      ActualClean net (baseTail ω.1) r ω.2.2 K ω.2.1 ∧
      net.inner r (actualPoint ω T)=0 ∧
      ω.1∈selectedEvent (braidInteractionGraph net hn r) k q := by
  classical
  simp only [actualNeuronEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The actual network event is bounded by the genuine selected-tail moment;
cleanliness is discarded only after the actual recording-fiber rank bound. -/
theorem actualNeuron_fraction_le_selectedTailMean
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (q K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : CommonGapScale net T) :
    ((actualNeuronEvent net hn q K T r).card:ℝ)/Fintype.card (Configuration k m) ≤
      selectedTailMean (braidInteractionGraph net hn r)
        (fun σ=>((braidInteractionGraph net hn r).comap (baseTail σ))) k q K := by
  classical
  let E := actualNeuronEvent net hn q K T r
  have he : meanOver (fun ω : Configuration k m=>if ω∈E then (1:ℝ) else 0)=
      meanOver (fun σ : FullPerm k m=>meanOver (fun ρ : RankPerm m=>
        meanOver (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0))) := by
    rw [meanOver_prod]
    simp_rw [meanOver_prod]
    apply congrArg meanOver
    funext σ
    exact meanOver_comm (fun τ ρ=>if (σ,τ,ρ)∈E then (1:ℝ) else 0)
  rw [←meanOver_indicator E,he]
  change meanOver (fun σ : FullPerm k m=>meanOver (fun ρ : RankPerm m=>
      meanOver (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0))) ≤
    meanOver (fun σ : FullPerm k m=>if σ∈selectedEvent (braidInteractionGraph net hn r) k q then
      meanOver (fun ρ : RankPerm m=>if ρ∉GoodEvent.badIsolatedEvent m K then
        lowRankMatchingMean ((braidInteractionGraph net hn r).comap (baseTail σ)) ρ K else 0)
      else 0)
  apply meanOver_mono
  intro σ
  by_cases hs : σ∈selectedEvent (braidInteractionGraph net hn r) k q
  · rw [if_pos hs]
    apply meanOver_mono
    intro ρ
    by_cases hQ : ρ∉GoodEvent.badIsolatedEvent m K
    · rw [if_pos hQ]
      have hh : (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0)=
          (fun τ : TailPerm m=>if ActualClean net (baseTail σ) r ρ K τ ∧
            net.inner r (actualGapPoint (baseTail σ) (τ,ρ) T)=0 then (1:ℝ) else 0) := by
        funext τ
        simp only [E,mem_actualNeuronEvent,hQ,hs,actualPoint,true_and,and_true,not_false_eq_true]
      rw [hh]
      exact actual_clean_mean_le_matching_mean net hn (baseTail σ) r ρ K T
        hscale.1 (fun τ=>hscale.2 σ τ ρ)
    · rw [if_neg hQ]
      have hh : (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0)=fun _=>0 := by
        funext τ
        apply if_neg
        intro hmem
        exact hQ ((mem_actualNeuronEvent net hn q K T r (σ,τ,ρ)).mp hmem).1
      rw [hh,meanOver_const]
  · rw [if_neg hs]
    have hh : (fun ρ : RankPerm m=>meanOver
        (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0))=fun _=>0 := by
      funext ρ
      have hh : (fun τ : TailPerm m=>if (σ,τ,ρ)∈E then (1:ℝ) else 0)=fun _=>0 := by
        funext τ
        simp only [E,mem_actualNeuronEvent,hs,and_false,if_false]
      rw [hh,meanOver_const]
    rw [hh,meanOver_const]

/-- The actual growing-arity per-neuron cost, with its exact k and q dependence.
All graph counting and tail bounds are derived; no structural H is needed for
this quantitative upper bound on a fixed actual event. -/
theorem actualNeuron_fraction_le
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (q K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : CommonGapScale net T)
    (hm : 2≤m) (hK : 0<(K:ℝ)) :
    ((actualNeuronEvent net hn q K T r).card:ℝ)/Fintype.card (Configuration k m) ≤
      ((k.descFactorial (2*q):ℝ)/((m+k).descFactorial (2*q):ℝ))*
        ((tailRate m K)^q)⁻¹*Real.exp (tailRate m K*((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) := by
  apply (actualNeuron_fraction_le_selectedTailMean net hn q K T r hscale).trans
  apply selectedTailMean_le _ _ k q K ((k:ℝ)*((m:ℝ)+(k:ℝ)-1))
    (Nat.le_add_left k m) hm hK
  intro σ
  apply Configurations.baseTail_edge_card_lower_bound
  exact le_trans (by decide : 1≤2) (hm.trans (Nat.le_add_right m k))

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
