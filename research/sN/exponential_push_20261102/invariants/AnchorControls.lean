import MaxCaterpillar.Frontier.Basic

/-! Semantic anchor controls for the research crease-cube invariant.
These general set-function lemmas do not prove the analytic span theorem. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.ExponentialPush
open Finset

/-- If the last coordinate is not an anchor coordinate, the final chain
increment of an anchored set function is zero. -/
theorem anchored_last_increment_zero {α : Type} [Fintype α] [DecidableEq α]
    (G : Finset α → ℝ) (A : Finset α) (z : α)
    (hA : ∀ B, A ⊆ B → G B = 0) (hz : z ∉ A) :
    G univ - G (univ.erase z) = 0 := by
  have hsub : A ⊆ univ.erase z := by
    intro a ha
    apply mem_erase.mpr
    exact ⟨fun he => hz (he ▸ ha), mem_univ a⟩
  rw [hA _ (subset_univ A), hA _ hsub]
  ring

/-- An anchored set function has zero mixed increment at its anchor.
For a quadratic function, this increment is the interaction coefficient. -/
theorem anchored_mixed_increment_zero {α : Type} [DecidableEq α]
    (G : Finset α → ℝ) (A : Finset α) (a b : α)
    (hA : ∀ B, A ⊆ B → G B = 0) :
    G (insert a (insert b A)) - G (insert a A) - G (insert b A) + G A = 0 := by
  rw [hA _ (Subset.trans (subset_insert b A) (subset_insert a (insert b A))),
    hA _ (subset_insert a A), hA _ (subset_insert b A), hA _ (Subset.refl A)]
  ring

#check @anchored_last_increment_zero
#check @anchored_mixed_increment_zero
#print axioms anchored_last_increment_zero
#print axioms anchored_mixed_increment_zero
end MaxCaterpillar.Frontier.ExponentialPush
