import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingGeometry

/-! # Actual variable-tail samples and a single common dominant-gap scale

Every finite selected set has its literal complement tail dimension. One
threshold works for every selected set, both tail permutations, every original
neuron, and every possible first-layer activation pattern. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
variable {n h₁ h₂ : ℕ}

abbrev RawConfig (S : Finset (Fin n)) := Cartesian.RawConfig (tailCount S)
abbrev Sample (n : ℕ) := Σ S : Finset (Fin n),RawConfig S

noncomputable def actualPoint (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ) : Point n :=
  DominantGap.actualGapPoint (tail S) p T
noncomputable def actualSamplePoint (ω : Sample n) (T : ℝ) : Point n :=
  actualPoint ω.1 ω.2 T

lemma actualPoint_eq_setGapPoint (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ) :
    actualPoint S p T=DominantGap.setGapPoint S p T := rfl

lemma actualPoint_selected_zero (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ)
    (v : Fin n) (hv : v∈S) : actualPoint S p T v=0 := by
  apply DominantGap.actualGapPoint_outside
  rw [tail_image]
  exact fun h => (Finset.mem_sdiff.mp h).2 hv

lemma actualPoint_tail (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ)
    (j : Fin (tailCount S)) :
    actualPoint S p T (tail S j)=Cartesian.gapPoint p T (some j) :=
  DominantGap.actualGapPoint_selected (tail S) p T j

lemma actualPoint_tail_negative (S : Finset (Fin n)) (p : RawConfig S) (T : ℝ)
    (hT : 0<T) (j : Fin (tailCount S)) : actualPoint S p T (tail S j)<0 :=
  DominantGap.actualGapPoint_selected_neg (tail S) p T hT j

/-- Actual genericity on every selected set and its literal variable-size tail.
The scalar is positive and independent of every sampled coordinate. -/
def CommonGapScale (net : NormalizedNetwork n h₁ h₂) (T : ℝ) : Prop :=
  0<T ∧ ∀ S : Finset (Fin n),∀ p : RawConfig S,
    DominantGap.GenericNetworkPoint net (tail S) p T

lemma CommonGapScale.set_generic (net : NormalizedNetwork n h₁ h₂) (T : ℝ)
    (h : CommonGapScale net T) (S : Finset (Fin n)) (p : RawConfig S) :
    DominantGap.GenericSetNetworkPoint net S p T :=
  DominantGap.genericSetNetworkPoint_of_generic net S p T (h.2 S p)

/-- This follows from the already proved actual-set realization theorem; no
common-scale or survival conclusion is assumed of the network. -/
theorem exists_common_gap_threshold (net : NormalizedNetwork n h₁ h₂) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B ≤ T → CommonGapScale net T := by
  obtain ⟨B,hB,h⟩ := DominantGap.exists_uniform_set_network_gap_threshold net
  refine ⟨B,hB,?_⟩
  intro T hT
  refine ⟨lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hB.trans hT),?_⟩
  intro S p
  exact (h S T hT p).underlying_generic

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Sampling
