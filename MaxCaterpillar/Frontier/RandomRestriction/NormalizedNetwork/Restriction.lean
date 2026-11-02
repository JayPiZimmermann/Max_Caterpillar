import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Ordinary
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! # Actual ordinary networks restrict faithfully to every nonempty tied set

The final representation keeps the original first and second index types.
Its retained first coefficients are exact original coefficients, rather than
proportional representatives. The support budget follows for any natural
cost, with no monotonicity assumption.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m]

/-- All-input actual-network reduction, including exact coefficients, the
translation-normalization invariant, and an arbitrary indexed support cost. -/
theorem exists_ordinary_restriction (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (e : Fin m ↪ Fin N) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x, model.eval x = Maximum m x) ∧ model.TranslationNormalized ∧
      (∀ j, model.A j = if (∑ i, net.W₁ j i) = 0 ∧
          rowSupport (net.W₁ j) ⊆ Finset.univ.image e
        then restrict e (net.W₁ j) else 0) ∧
      (∀ j, model.Feeding j → ∃ k, net.W₂ k j ≠ 0) ∧
      (∀ cost : ℕ → ℕ,
        (∑ j, if 3 ≤ (rowSupport (model.A j)).card
          then cost (rowSupport (model.A j)).card else 0) ≤
        ∑ j, if 3 ≤ (rowSupport (net.W₁ j)).card ∧
            rowSupport (net.W₁ j) ⊆ Finset.univ.image e
          then cost (rowSupport (net.W₁ j)).card else 0) := by
  classical
  obtain ⟨model,hmax,hnorm,hrows,hfeed⟩ :=
    exists_localized_normalized (ofOrdinary net) (ofOrdinary_computes_max net hnet)
      (ofOrdinary_translation_normalized net hnet).1 e
  have hactual : ∀ j, model.A j = if (∑ i, net.W₁ j i) = 0 ∧
      rowSupport (net.W₁ j) ⊆ Finset.univ.image e then restrict e (net.W₁ j) else 0 := by
    intro j
    have hj := hrows j
    rw [ofOrdinary_first_row] at hj
    by_cases hz : (∑ i, net.W₁ j i) = 0
    · simpa [hz] using hj
    · simpa [hz,restrict] using hj
  refine ⟨model,hmax,hnorm,hactual,?_,?_⟩
  · intro j hj
    exact ofOrdinary_feeding_original net j (hfeed j hj)
  · intro cost
    exact indexed_support_cost_le_of_masked_restriction e net.W₁ model.A
      (fun j => (∑ i, net.W₁ j i) = 0 ∧ rowSupport (net.W₁ j) ⊆ Finset.univ.image e)
      cost (fun _ hj => hj.2) hactual

#check @exists_ordinary_restriction
#print axioms exists_ordinary_restriction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
