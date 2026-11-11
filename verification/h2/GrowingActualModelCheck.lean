import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventModel

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Check
open BigOperators Configurations DominantGap
attribute [local instance] Classical.propDecidable

/-- Exact original-coordinate per-neuron statement, expanded rate and actual
uniform triple sample space. No rank/probability/count premise. -/
example {k m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (hscale : 0<T ∧ ∀σ : Equiv.Perm (Fin (m+k)),∀τ ρ : Equiv.Perm (Fin m),
      GenericNetworkPoint net (baseTail σ) (τ,ρ) T)
    (hm : 2≤m) (hK : 0<(K:ℝ)) :
    ((actualNeuronEvent net hn q K T r).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin (m+k))×Equiv.Perm (Fin m)×Equiv.Perm (Fin m)) ≤
      ((k.descFactorial (2*q):ℝ)/((m+k).descFactorial (2*q):ℝ))*
        ((7*(K:ℝ)/(24*(m:ℝ)*((m:ℝ)-1)))^q)⁻¹*
          Real.exp ((7*(K:ℝ)/(24*(m:ℝ)*((m:ℝ)-1)))*
            ((k:ℝ)*((m:ℝ)+(k:ℝ)-1))) :=
  actualNeuron_fraction_le net hn q K T r hscale hm hK

/-- Actual original coefficients derive their common scale, even without an
all-input MAX identity or translation normalization. -/
example {k m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+k) h₁ h₂) :
    ∃B : ℝ,2≤B ∧ ∀T : ℝ,B≤T →
      0<T ∧ ∀σ : FullPerm k m,∀τ : TailPerm m,∀ρ : RankPerm m,
        GenericNetworkPoint net (baseTail σ) (τ,ρ) T :=
  exists_common_gap_threshold net

/-- The counted good event implies actual cleanliness at the original point,
with no abstract clean-event premise. -/
example {k m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+k) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (r : Fin h₂)
    (σ : FullPerm k m) (τ : TailPerm m) (ρ : RankPerm m)
    (hgood : (effectivePermutation σ τ,ρ)∉
      GoodEvent.feedingBadConfigurations k (fun j=>NormalizedNetwork.rowSupport (net.A j)) K) :
    ActualClean net (baseTail σ) r ρ K τ := by
  apply good_implies_actualClean net hn K r σ τ ρ
  intro hbad
  have hb := (mem_feedingBadConfigurationsThree k (firstSupports net) K (σ,τ,ρ)).mp hbad
  change (effectivePermutation σ τ,ρ)∈GoodEvent.feedingBadConfigurations k (firstSupports net) K at hb
  rw [show firstSupports net=(fun j=>NormalizedNetwork.rowSupport (net.A j)) from rfl] at hb
  exact hgood hb

/-- Zero selected arity with a positive requested matching gives an empty
actual event, including real networks with arbitrary numbers of indexed rows. -/
example {m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+0) h₁ h₂)
    (hn : net.TranslationNormalized) (K : ℕ) (T : ℝ) (r : Fin h₂) :
    actualNeuronEvent net hn 1 K T r=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro ω hω
  have hs := ((mem_actualNeuronEvent net hn 1 K T r ω).mp hω).2.2.2
  have he := selectedEvent_empty_of_prefix_lt (braidInteractionGraph net hn r)
    (k:=0) (q:=1) (Nat.zero_le _) (by norm_num)
  rw [he] at hs
  exact Finset.not_mem_empty _ hs

#check @selectedTailMean
#check @actualNeuronEvent
#check @CommonGapScale
#check @actualNeuron_fraction_le
#print axioms meanOver_mono
#print axioms meanOver_const
#print axioms lowRankMatchingMean_le_shifted
#print axioms selectedTailMean_le
#print axioms meanOver_prod
#print axioms meanOver_comm
#print axioms meanOver_indicator
#print axioms native_braid_count_eq_active
#print axioms actual_clean_mean_le_matching_mean
#print axioms exists_common_gap_threshold
#print axioms mem_actualNeuronEvent
#print axioms actualNeuron_fraction_le_selectedTailMean
#print axioms actualNeuron_fraction_le
#print axioms GoodEvent.mem_roleEvents
#print axioms GoodEvent.mem_supportBadAt
#print axioms GoodEvent.mem_supportBadAt_of_caseA
#print axioms GoodEvent.mem_supportBadAt_of_caseB
#print axioms GoodEvent.mem_supportBadAt_of_caseC
#print axioms GoodEvent.mem_supportBadConfigurations
#print axioms mem_feedingBadConfigurationsThree
#print axioms good_implies_actualClean
#print axioms feedingBadConfigurationsThree_fraction
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Check
