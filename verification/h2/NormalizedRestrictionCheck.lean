import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
import MaxCaterpillar.Fiber.Star65.Construction

set_option autoImplicit false
namespace NormalizedRestrictionCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction NormalizedNetwork

-- The normalization invariant is expanded in this independent expected type.
example {N m h₁ h₂ : ℕ} [NeZero N] [NeZero m] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (e : Fin m ↪ Fin N) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x, model.eval x = Maximum m x) ∧
      (∀ j, ∑ i, model.A j i = 0) ∧
      (∀ k, ∑ i, model.U k i = 0) ∧
      (∑ i, model.L i = 1) ∧
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
  obtain ⟨model,hmax,hnorm,hrows,hfeed,hcost⟩ := exists_ordinary_restriction net hnet e
  exact ⟨model,hmax,hnorm.1,hnorm.2.1,hnorm.2.2,hrows,hfeed,hcost⟩

-- The germ rule is generic and assumes neither MAX nor normalization.
example {N m h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N) (x : Point m) :
    ∃ ε : ℝ, 0 < ε ∧ net.eval (q + ε • lift e x) =
      net.eval q + ε*net.directionalEval q e x :=
  exists_eval_direction net q e x

-- A genuine four-input ordinary network restricts to a proper two-input set.
private def selected02 : Fin 2 ↪ Fin 4 := ⟨![0,2],by decide⟩
example : ∃ model : NormalizedNetwork 2 6 5,
    (∀ x, model.eval x = Maximum 2 x) ∧ model.TranslationNormalized := by
  obtain ⟨model,hmax,hnorm,_hrows,_hfeed,_hcost⟩ :=
    exists_ordinary_restriction (Fiber.Star65.branchINet 1 0)
      (fun x => Fiber.Star65.branchINet_eval (by norm_num) (by norm_num) (by norm_num) x)
      selected02
  exact ⟨model,hmax,hnorm⟩

#check @exists_ordinary_set_restriction
#print axioms ofOrdinary_computes_max
#print axioms ofOrdinary_translation_normalized
#print axioms ofOrdinary_exact_direction
#print axioms eventually_eval_direction
#print axioms exists_eval_direction
#print axioms directional_computes_max_of_tied
#print axioms exists_generic_tied_point
#print axioms exists_localized_normalized
#print axioms exists_ordinary_restriction
#print axioms exists_ordinary_set_restriction
#print axioms normalizeOuter_computes_max
#print axioms normalizeOuter_translation_normalized
end NormalizedRestrictionCheck
