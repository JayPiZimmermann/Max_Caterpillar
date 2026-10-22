import MaxNN.CPWL.Pieces.Polyhedra
import Mathlib.Analysis.Convex.Basic

/-!
# Convexity of polyhedra

`Polyhedron.convex_carrier`: an H-presented polyhedron is a convex set — each halfspace
constraint is preserved under convex combinations.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

namespace Polyhedron

/-- An H-presented polyhedron is convex. -/
theorem convex_carrier {d : ℕ} (P : Polyhedron d) : Convex ℝ P.carrier := by
  intro x hx y hy a b ha hb hab
  intro l
  have hsum : (∑ j, P.C l j * (a • x + b • y) j)
      = a * (∑ j, P.C l j * x j) + b * (∑ j, P.C l j * y j) := by
    rw [Finset.sum_congr rfl fun j _ => show P.C l j * (a • x + b • y) j
          = a * (P.C l j * x j) + b * (P.C l j * y j) from by
        show P.C l j * (a * x j + b * y j) = a * (P.C l j * x j) + b * (P.C l j * y j)
        ring,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum]
  have h1 : a * (∑ j, P.C l j * x j) ≤ a * P.r l :=
    mul_le_mul_of_nonneg_left (hx l) ha
  have h2 : b * (∑ j, P.C l j * y j) ≤ b * P.r l :=
    mul_le_mul_of_nonneg_left (hy l) hb
  have hr : a * P.r l + b * P.r l = P.r l := by
    rw [← add_mul, hab, one_mul]
  linarith

end Polyhedron

end MaxNN
