import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.TailEnvelope
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.SamplingPoint
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ActualRank
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiniteMeans

/-! # Actual Bernoulli-selected network events and their conditional cost

The selected-set law is Bernoulli, with genuine uniform raw tail/rank samples
at its actual variable dimension. Survival always concerns the original
second preactivation at the same original-coordinate structured point.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators DominantGap
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (badIsolatedEvent)
attribute [local instance] Classical.propDecidable
variable {n h₁ h₂ : ℕ}

noncomputable def firstSupports (net : NormalizedNetwork n h₁ h₂) :
    Fin h₁→Finset (Fin n) :=fun j=>NormalizedNetwork.rowSupport (net.A j)

noncomputable def actualNeuronEvent (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (S : Finset (Fin n)) : Finset (Sampling.RawConfig S) :=
  Finset.univ.filter fun a=>
    a.2∉badIsolatedEvent (Sampling.tailCount S) K ∧
    ActualClean net (Sampling.tail S) r a.2 K a.1 ∧
    net.inner r (Sampling.actualPoint S a T)=0 ∧
    S∈matchingSets (braidInteractionGraph net hn r) q

@[simp] theorem mem_actualNeuronEvent (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (S : Finset (Fin n)) (a : Sampling.RawConfig S) :
    a∈actualNeuronEvent net hn q K T r S ↔
      a.2∉badIsolatedEvent (Sampling.tailCount S) K ∧
      ActualClean net (Sampling.tail S) r a.2 K a.1 ∧
      net.inner r (Sampling.actualPoint S a T)=0 ∧
      S∈matchingSets (braidInteractionGraph net hn r) q := by
  simp only [actualNeuronEvent,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def actualNeuronFraction (net : NormalizedNetwork n h₁ h₂)
    (hn : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (S : Finset (Fin n)) : ℝ :=
  ((actualNeuronEvent net hn q K T r S).card:ℝ)/Fintype.card (Sampling.RawConfig S)

noncomputable def actualNeuronMean (p : ℝ) (D : Finset (Finset (Fin n)))
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (q K : ℕ) (T : ℝ) (r : Fin h₂) : ℝ :=
  condMean p D (actualNeuronFraction net hn q K T r)

/-- Joint clean survival is averaged over true recorded permutation fibers,
then cleanliness is discarded. This is not survival conditioned on Good. -/
theorem actualNeuronFraction_le_tailMean
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (q K : ℕ) (T : ℝ) (r : Fin h₂) (hscale : Sampling.CommonGapScale net T)
    (S : Finset (Fin n)) :
    actualNeuronFraction net hn q K T r S ≤
      if S∈matchingSets (braidInteractionGraph net hn r) q then
        meanOver (fun ρ : Equiv.Perm (Fin (Sampling.tailCount S))=>
          if ρ∉badIsolatedEvent (Sampling.tailCount S) K then
            lowRankMatchingMean ((braidInteractionGraph net hn r).comap (Sampling.tail S)) ρ K
          else 0)
      else 0 := by
  classical
  let E:=actualNeuronEvent net hn q K T r S
  change (E.card:ℝ)/Fintype.card (Sampling.RawConfig S)≤_
  rw [←meanOver_indicator E,meanOver_prod]
  rw [meanOver_comm (fun τ ρ=>if (τ,ρ)∈E then (1:ℝ) else 0)]
  by_cases hs : S∈matchingSets (braidInteractionGraph net hn r) q
  · rw [if_pos hs]
    apply meanOver_mono
    intro ρ
    by_cases hQ : ρ∉badIsolatedEvent (Sampling.tailCount S) K
    · rw [if_pos hQ]
      have he : (fun τ : Equiv.Perm (Fin (Sampling.tailCount S))=>
          if (τ,ρ)∈E then (1:ℝ) else 0)=
        (fun τ=>if ActualClean net (Sampling.tail S) r ρ K τ ∧
          net.inner r (actualGapPoint (Sampling.tail S) (τ,ρ) T)=0 then (1:ℝ) else 0) := by
        funext τ
        simp only [E,mem_actualNeuronEvent,hQ,hs,Sampling.actualPoint,
          true_and,and_true,not_false_eq_true]
      rw [he]
      exact actual_clean_mean_le_matching_mean net hn (Sampling.tail S) r ρ K T
        hscale.1 (fun τ=>hscale.2 S (τ,ρ))
    · rw [if_neg hQ]
      have he : (fun τ : Equiv.Perm (Fin (Sampling.tailCount S))=>
          if (τ,ρ)∈E then (1:ℝ) else 0)=fun _=>0 := by
        funext τ
        apply if_neg
        intro hmem
        exact hQ ((mem_actualNeuronEvent net hn q K T r S (τ,ρ)).mp hmem).1
      rw [he,meanOver_const]
  · rw [if_neg hs]
    have he : (fun ρ : Equiv.Perm (Fin (Sampling.tailCount S))=>meanOver
        (fun τ : Equiv.Perm (Fin (Sampling.tailCount S))=>
          if (τ,ρ)∈E then (1:ℝ) else 0))=fun _=>0 := by
      funext ρ
      have he : (fun τ : Equiv.Perm (Fin (Sampling.tailCount S))=>
          if (τ,ρ)∈E then (1:ℝ) else 0)=fun _=>0 := by
        funext τ
        simp only [E,mem_actualNeuronEvent,hs,and_false,if_false]
      rw [he,meanOver_const]
    rw [he,meanOver_const]

/-- Actual conditional network event cost at variable selected arity. Every
rank/moment/graph estimate is derived from the original arrays. -/
theorem actualNeuronMean_le (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (net : NormalizedNetwork n h₁ h₂)
    (hnorm : net.TranslationNormalized) (q K : ℕ) (T : ℝ) (r : Fin h₂)
    (hscale : Sampling.CommonGapScale net T) (b : ℕ) (hn : 0<n) (hK : 0<(K:ℝ))
    (hm : ∀S∈D,2≤Sampling.tailCount S) (hcap : ∀S∈D,S.card≤b) :
    actualNeuronMean p D net hnorm q K T r ≤
      (p^2/ambientRate n K)^q*Real.exp (ambientRate n K*((b:ℝ)*((n:ℝ)-1))) := by
  have hstep : actualNeuronMean p D net hnorm q K T r ≤
      selectedTailMean p D (braidInteractionGraph net hnorm r) q K := by
    apply condMean_mono_on hp0 hp1 D hpos
    intro S _
    exact actualNeuronFraction_le_tailMean net hnorm q K T r hscale S
  exact hstep.trans (selectedTailMean_le p hp0 hp1 D hD hpos
    (braidInteractionGraph net hnorm r) q K b hn hK hm hcap)

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
