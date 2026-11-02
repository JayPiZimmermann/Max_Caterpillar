import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Realization
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.LiftedPoint
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.Linearization
import Mathlib.Data.Fintype.Sum

/-! # Actual generic-scale first and second neuron survival

One scale works for every raw permutation and every possible first-activation
pattern. The actual pattern is selected only after the scale is chosen, so no
fixed-pattern or survival equivalence is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open BigOperators Cartesian

abbrev NetworkRowIndex (h₁ h₂ : ℕ) := Fin h₁ ⊕ EffectiveRowIndex h₁ h₂

noncomputable def networkRows {N h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂) :
    NetworkRowIndex h₁ h₂→Point N
  | Sum.inl j => net.A j
  | Sum.inr s => effectiveRowFamily net s

lemma networkRows_zero_sum {N h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (s : NetworkRowIndex h₁ h₂) :
    (∑ i,networkRows net s i)=0 := by
  cases s with
  | inl j => exact hn.1 j
  | inr s => exact effectiveRowFamily_zero_sum net hn s

/-- The proved scalar genericity result in actual original coordinates. -/
theorem stableGap_actual_zero_iff {N m : ℕ} (e : Fin m ↪ Fin N)
    (p : RawConfig m) (w : Point N) (T : ℝ)
    (h : StableGap p (collapsedRow e w) T) :
    lin w (actualGapPoint e p T)=0 ↔ NormalizedNetwork.restrict e w=0 := by
  rw [lin_actualGapPoint_eq_weighted]
  exact h.1.trans (collapsedRow_tail_zero_iff_restrict e w)

/-- Explicit evidence on the actual gap point, not a definition of a surviving
network or an assumed replacement of the original coefficients. -/
structure GenericNetworkPoint {N h₁ h₂ m : ℕ} (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ) : Prop where
  tied_block : ∀ i∉Finset.univ.image e,actualGapPoint e p T i=0
  negative_tail : ∀ a,actualGapPoint e p T (e a)<0
  first_zero_iff : ∀ j,lin (net.A j) (actualGapPoint e p T)=0 ↔
    NormalizedNetwork.restrict e (net.A j)=0
  second_zero_iff : ∀ k,net.inner k (actualGapPoint e p T)=0 ↔
    NormalizedNetwork.restrict e
      (actualEffectiveRow net k (actualGapPoint e p T))=0
  all_rows_stable : ∀ s,StableGap p (collapsedRow e (networkRows net s)) T

/-- For any real-weight normalized skip network, one sufficiently large scale
works simultaneously for every actual tau/rho and all original neurons. This
zero/restriction equivalence is proved even without translation normalization. -/
theorem exists_network_gap_threshold {N h₁ h₂ m : ℕ}
    (net : NormalizedNetwork N h₁ h₂) (e : Fin m ↪ Fin N) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,GenericNetworkPoint net e p T := by
  classical
  obtain ⟨B,hB,hstable⟩ := finite_gap_family_shared_threshold
    (fun s : NetworkRowIndex h₁ h₂ => collapsedRow e (networkRows net s))
  refine ⟨B,hB,?_⟩
  intro T hT p
  have hpos : 0<T := lt_of_lt_of_le (by linarith only [hB]) hT
  have hcrit : ∀ s : NetworkRowIndex h₁ h₂,
      lin (networkRows net s) (actualGapPoint e p T)=0 ↔
        NormalizedNetwork.restrict e (networkRows net s)=0 := by
    intro s
    exact stableGap_actual_zero_iff e p (networkRows net s) T (hstable T hT p s)
  refine ⟨actualGapPoint_outside e p T,actualGapPoint_selected_neg e p T hpos,?_,?_,hstable T hT p⟩
  · intro j
    exact hcrit (Sum.inl j)
  · intro k
    exact inner_eq_zero_iff_of_family_criterion_at net
      (fun t : ℝ => actualGapPoint e p t)
      (fun _ w => NormalizedNetwork.restrict e w) T k (fun s => hcrit (Sum.inr s))

/-- Actual activation sign is the source highest-rank prefix sign on every row
in the complete finite family, including every possible effective second row. -/
theorem genericNetworkPoint_prefix_sign {N h₁ h₂ m : ℕ}
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (h : GenericNetworkPoint net e p T) (s : NetworkRowIndex h₁ h₂) (g : Fin m)
    (hg : GapDominant p (collapsedRow e (networkRows net s)) g) :
    (0<lin (networkRows net s) (actualGapPoint e p T) ↔
      0<collapsedRow e (networkRows net s) none+
        ∑ k in Finset.univ.filter (fun k : Fin m => k.val<g.val),
          collapsedRow e (networkRows net s) (some (p.1 k))) ∧
    (lin (networkRows net s) (actualGapPoint e p T)<0 ↔
      collapsedRow e (networkRows net s) none+
        ∑ k in Finset.univ.filter (fun k : Fin m => k.val<g.val),
          collapsedRow e (networkRows net s) (some (p.1 k))<0) := by
  have hs := stableGap_prefix_sign_iff
    (collapsedRow_zero_sum e (networkRows net s) (networkRows_zero_sum net hn s))
    (h.all_rows_stable s) hg
  simpa only [gapValue,lin_actualGapPoint_eq_weighted] using hs
end MaxCaterpillar.Frontier.RandomRestriction.DominantGap
