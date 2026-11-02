import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronGraph
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronFibers
import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronAveraging

/-! # Aggregating actual local rank bounds over the tail permutation

This intermediate lemma makes its local rank input explicit. The actual
network rank theorem supplies that input in the final per-neuron assembly.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations GoodEvent DominantGap
variable {m h₁ h₂ : ℕ}
attribute [local instance] braidGraphDecidable

theorem neuron_tail_card_le_of_clean_fiber_bound
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (k : Fin h₂) (σ : FullPerm m) (ρ : RankPerm m)
    (hrank : ∀ u : Matching.Data (↥(rankIsolatedGaps ρ K)) m,
      ∀ base : Matching.Fiber (rankIsolatedSlots ρ K) u,
      ActualClean net (baseTail σ) k ρ K base.val →
      ((Finset.univ.filter fun p : Matching.Fiber (rankIsolatedSlots ρ K) u =>
        net.inner k (actualGapPoint (baseTail σ) (p.val,ρ) T)=0).card : ℝ) /
          Fintype.card (Matching.Fiber (rankIsolatedSlots ρ K) u) ≤
        (1/2:ℝ)^nativeMatchingCount
          ((braidInteractionGraph net hn k).comap (baseTail σ))
          (rankIsolatedSlots ρ K) base.val) :
    ((tailFiber (neuronEvent net hn K T k) σ ρ).card : ℝ) ≤
      ∑ τ : TailPerm m, (1/2:ℝ)^nativeMatchingCount
        ((braidInteractionGraph net hn k).comap (baseTail σ))
        (rankIsolatedSlots ρ K) τ := by
  classical
  let slot := rankIsolatedSlots ρ K
  let H := (braidInteractionGraph net hn k).comap (baseTail σ)
  let clean := ActualClean net (baseTail σ) k ρ K
  let survive := fun τ : TailPerm m =>
    net.inner k (actualGapPoint (baseTail σ) (τ,ρ) T)=0
  let weight := fun τ : TailPerm m => (1/2:ℝ)^nativeMatchingCount H slot τ
  have hsubset : tailFiber (neuronEvent net hn K T k) σ ρ ⊆
      cleanSurvivalSet clean survive := by
    intro τ hτ
    have hh := (mem_neuronEvent net hn K T k (σ,τ,ρ)).mp
      ((mem_tailFiber _ σ ρ τ).mp hτ)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,good_implies_actualClean net hn K k σ τ ρ hh.1,hh.2.2.1⟩
  have hc : ((cleanSurvivalSet clean survive).card : ℝ) ≤ ∑ τ, weight τ := by
    apply clean_survival_card_le_sum (Matching.recorded slot) clean survive weight
    · intro τ
      exact pow_nonneg (by norm_num) _
    · intro τ υ hdata
      dsimp only [weight]
      rw [nativeMatchingCount_recorded_eq H slot τ υ hdata]
    · intro u base hbase
      exact hrank u base hbase
  exact (show ((tailFiber (neuronEvent net hn K T k) σ ρ).card : ℝ) ≤
    ((cleanSurvivalSet clean survive).card : ℝ) by
      exact_mod_cast Finset.card_le_of_subset hsubset).trans hc

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
