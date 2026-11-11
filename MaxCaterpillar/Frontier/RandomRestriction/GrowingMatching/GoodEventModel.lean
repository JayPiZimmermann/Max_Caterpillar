import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventProbability
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventDominance
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ActualModel

/-! # The actual growing-arity role good event implies actual cleanliness -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators Configurations DominantGap
variable {k m h₁ h₂ : ℕ}

noncomputable def firstSupports (net : NormalizedNetwork (m+k) h₁ h₂) :
    Fin h₁→Finset (Fin (m+k)) := fun j=>NormalizedNetwork.rowSupport (net.A j)

noncomputable def feedingBadConfigurationsThree
    {κ : Type*} [Fintype κ] (k : ℕ) (T : κ→Finset (Fin (m+k))) (K : ℕ) :
    Finset (Configuration k m) :=
  pullbackEvent (GoodEvent.feedingBadConfigurations k T K)

@[simp] theorem mem_feedingBadConfigurationsThree
    {κ : Type*} [Fintype κ] (k : ℕ) (T : κ→Finset (Fin (m+k))) (K : ℕ)
    (ω : Configuration k m) :
    ω∈feedingBadConfigurationsThree k T K ↔
      effectiveConfiguration ω∈GoodEvent.feedingBadConfigurations k T K :=
  mem_pullbackEvent _ _

/-- The actual counted good event excludes every feeding nonbraid dominant
original row at every isolated low-rank gap in the actual tail order. -/
theorem good_implies_actualClean
    (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (r : Fin h₂) (σ : FullPerm k m) (τ : TailPerm m) (ρ : RankPerm m)
    (hgood : (σ,τ,ρ)∉feedingBadConfigurationsThree k (firstSupports net) K) :
    ActualClean net (baseTail σ) r ρ K τ := by
  classical
  intro j hW hs g hg
  have hgoodj : (effectivePermutation σ τ,ρ)∉
      GoodEvent.supportBadConfigurations k (NormalizedNetwork.rowSupport (net.A j)) K := by
    intro hj
    apply hgood
    apply (mem_feedingBadConfigurationsThree k (firstSupports net) K _).mpr
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_univ _,hj⟩
  apply GoodEventDominance.good_event_excludes_nonbraid_dominant_of_tail_order
    k (net.A j) (hn.1 j) hs (effectivePermutation σ τ) (τ,ρ)
    (DominantGap.collapsedRow (baseTail σ) (net.A j)) ?_ K hgoodj g hg
  intro a
  change net.A j (baseTail σ (τ a))=
    net.A j ((effectivePermutation σ τ).symm (tailPosition k m a))
  rw [effectivePermutation_tail]
  rfl

theorem feedingBadConfigurationsThree_fraction
    {κ : Type*} [Fintype κ] (k : ℕ) (T : κ→Finset (Fin (m+k))) (K : ℕ) :
    ((feedingBadConfigurationsThree k T K).card:ℝ)/Fintype.card (Configuration k m)=
      GoodEvent.feedingBadFraction k T K :=
  pullbackEvent_fraction _

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
