import MaxCaterpillar.Frontier.RandomRestriction.PerNeuronCounting
import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingRank

/-! # Actual per-neuron cost 400

The rank estimate is proved for the original network at its actual gap point.
The configuration and graph averaging in `PerNeuronCounting` then supply the
uniform finite event count. No conditional probability or counting estimate is
an assumption of the result.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations GoodEvent DominantGap
variable {m h₁ h₂ : ℕ}
attribute [local instance] braidGraphDecidable

theorem activeMatchingEdges_card_eq_native
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (k : Fin h₂) (e : Fin m ↪ Fin (m+5)) (ρ τ : TailPerm m) (K : ℕ) :
    (activeMatchingEdges net e k ρ K τ).card =
      nativeMatchingCount ((braidInteractionGraph net hn k).comap e)
        (rankIsolatedSlots ρ K) τ := by
  rw [native_braid_matchingCount_eq]
  rfl

/-- The actual per-neuron event has cost at most 400/K², for every normalized
real network and the same common actual generic scale used by the witness. -/
theorem neuron_event_card_le_four_hundred
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (K : ℕ) (T : ℝ) (k : Fin h₂)
    (hm : 400≤m) (hKlow : 4≤K) (hKhigh : (K:ℝ)≤(m:ℝ)/100)
    (hscale : UniformGapScale net T) :
    K^2*(neuronEvent net hn K T k).card ≤ 400*Fintype.card (Configuration m) := by
  apply neuron_event_card_le_of_clean_fiber_bounds net hn K T k hm hKlow hKhigh
  intro σ ρ u base hclean
  have hT := uniform_gap_scale_pos net T (le_trans (by norm_num) hm) hscale
  have hh := actualClean_fiber_survival_fraction_le net hn (baseTail σ) k ρ K u base
    hclean T hT (fun τ => hscale σ τ ρ)
  rw [activeMatchingEdges_card_eq_native net hn] at hh
  exact hh

/-- A common admissible scale exists for arbitrary actual coefficient arrays;
the event bound is consequently available without any genericity premise. -/
theorem exists_neuron_event_counting_threshold
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized) :
    ∃ B : ℝ, 2≤B ∧ ∀ T : ℝ, B≤T → ∀ K : ℕ, ∀ k : Fin h₂,
      400≤m → 4≤K → (K:ℝ)≤(m:ℝ)/100 →
      K^2*(neuronEvent net hn K T k).card ≤ 400*Fintype.card (Configuration m) := by
  obtain ⟨B,hB,hscale⟩ := exists_uniform_gap_scale_threshold net
  exact ⟨B,hB,fun T hT K k hm hKlow hKhigh =>
    neuron_event_card_le_four_hundred net hn K T k hm hKlow hKhigh (hscale T hT)⟩

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
