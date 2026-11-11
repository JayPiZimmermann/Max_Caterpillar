import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.TailEnvelope
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronFibers
import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingRank

/-! # Actual real-network clean survival averaged over true permutation fibers

The original preactivation is evaluated at the original gap point. No rank,
activation, probability, or counting conclusion is a premise of this bridge.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators GoodEvent DominantGap
attribute [local instance] Classical.propDecidable
variable {N m h₁ h₂ : ℕ}

theorem native_braid_count_eq_active
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m↪Fin N) (r : Fin h₂) (ρ τ : Equiv.Perm (Fin m)) (K : ℕ) :
    PerNeuron.nativeMatchingCount ((braidInteractionGraph net hn r).comap e)
      (rankIsolatedSlots ρ K) τ=(activeMatchingEdges net e r ρ K τ).card := by
  classical
  unfold PerNeuron.nativeMatchingCount activeMatchingEdges tailBraidWeight
  congr 1
  ext i
  have hne : e (τ (rankIsolatedSlots ρ K (i,false)))≠
      e (τ (rankIsolatedSlots ρ K (i,true))) :=
    e.injective.ne (τ.injective.ne (Matching.slot_pair_ne (rankIsolatedSlots ρ K) i))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    SimpleGraph.comap_adj,braidInteractionGraph_adj]
  exact and_iff_right hne

/-- Literal clean actual survival, averaged over uniform tail permutations,
is bounded by the genuine matching moment in the actual induced graph. -/
theorem actual_clean_mean_le_matching_mean
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m↪Fin N) (r : Fin h₂) (ρ : Equiv.Perm (Fin m)) (K : ℕ)
    (T : ℝ) (hT : 0<T)
    (hgen : ∀τ,GenericNetworkPoint net e (τ,ρ) T) :
    meanOver (fun τ : Equiv.Perm (Fin m) =>
      if ActualClean net e r ρ K τ ∧ net.inner r (actualGapPoint e (τ,ρ) T)=0
        then (1:ℝ) else 0) ≤
      lowRankMatchingMean ((braidInteractionGraph net hn r).comap e) ρ K := by
  classical
  let slot := rankIsolatedSlots ρ K
  let H := (braidInteractionGraph net hn r).comap e
  let clean := ActualClean net e r ρ K
  let survive := fun τ : Equiv.Perm (Fin m) => net.inner r (actualGapPoint e (τ,ρ) T)=0
  let weight := fun τ : Equiv.Perm (Fin m) =>
    (1/2:ℝ)^PerNeuron.nativeMatchingCount H slot τ
  have hc : ((PerNeuron.cleanSurvivalSet clean survive).card:ℝ)≤∑τ,weight τ := by
    apply PerNeuron.clean_survival_card_le_sum (Matching.recorded slot) clean survive weight
    · intro τ
      exact pow_nonneg (by norm_num) _
    · intro τ υ hdata
      dsimp only [weight]
      rw [PerNeuron.nativeMatchingCount_recorded_eq H slot τ υ hdata]
    · intro u base hbase
      have hh := actualClean_fiber_survival_fraction_le net hn e r ρ K u base
        hbase T hT hgen
      rw [←native_braid_count_eq_active net hn e r ρ base.val K] at hh
      exact hh
  have he : (∑τ : Equiv.Perm (Fin m),if clean τ ∧ survive τ then (1:ℝ) else 0)=
      ((PerNeuron.cleanSurvivalSet clean survive).card:ℝ) := by
    rw [Finset.sum_boole]
    rfl
  change (Fintype.card (Equiv.Perm (Fin m)):ℝ)⁻¹ *
      (∑τ,if clean τ ∧ survive τ then (1:ℝ) else 0) ≤
    (Fintype.card (Equiv.Perm (Fin m)):ℝ)⁻¹ *∑τ,weight τ
  rw [he]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
