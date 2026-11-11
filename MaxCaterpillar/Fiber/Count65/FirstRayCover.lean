import MaxCaterpillar.Fiber.First65.Irredundancy

/-! # Completing a first-matrix normal form from a positive-ray cover

First-width minimality makes any assignment of actual first rows to six
prescribed positive rays injective. The resulting finite bijection supplies
all hidden-row bookkeeping at once.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open MaxCaterpillar.Frontier

/-- Covering the actual first rows by six prescribed positive rays already
provides positive scales and a hidden-row permutation. -/
theorem first_matrix_of_positive_ray_cover {h₂ : ℕ} (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (A : Fin 6 → Point 4)
    (hcover : ∀ j, ∃ k, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • A k) :
    ∃ s : Fin 6 → ℝ, (∀ j, 0 < s j) ∧ ∃ p : Equiv.Perm (Fin 6),
      ∀ j, net.W₁ j = s j • A (p j) := by
  classical
  choose k s hs hrows using hcover
  have hinj : Function.Injective k := by
    intro j l hjl
    by_contra hne
    apply net.first_rows_not_pos_proportional_of_max4_six hnet hne (div_pos (hs j) (hs l))
    rw [hrows j,hrows l,hjl,smul_smul,div_mul_cancel _ (hs l).ne']
  let p : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective k ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨s,hs,p,hrows⟩

#print axioms first_matrix_of_positive_ray_cover
end MaxCaterpillar.Fiber.Count65
