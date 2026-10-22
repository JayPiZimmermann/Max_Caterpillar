import MaxNN.CPWL.Pieces.Polyhedra
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.Monoid

/-!
# Topological facts about the CPWL vocabulary

* `AffineFn.continuous_eval` — a scalar affine function is continuous;
* `Polyhedron.isClosed_carrier` — an H-presented polyhedron is a closed set.

`ℝ^d` carries the product topology of `Fin d → ℝ` throughout.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- The linear form `x ↦ ∑ j, a j * x j` is continuous on `ℝ^d`. -/
theorem continuous_linear_form {d : ℕ} (a : Fin d → ℝ) :
    Continuous fun x : Fin d → ℝ => ∑ j, a j * x j :=
  continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)

namespace AffineFn

/-- A scalar affine function is continuous. -/
theorem continuous_eval {d : ℕ} (g : AffineFn d) : Continuous g.eval := by
  show Continuous fun x : Fin d → ℝ => (∑ j, g.a j * x j) + g.c
  exact (continuous_linear_form g.a).add continuous_const

end AffineFn

namespace Polyhedron

/-- An H-presented polyhedron is a closed subset of `ℝ^d`. -/
theorem isClosed_carrier {d : ℕ} (P : Polyhedron d) : IsClosed P.carrier := by
  have e : P.carrier = ⋂ l, { x : Fin d → ℝ | (∑ j, P.C l j * x j) ≤ P.r l } := by
    ext x
    rw [Set.mem_iInter]
    exact Iff.rfl
  rw [e]
  exact isClosed_iInter fun l =>
    isClosed_le (continuous_linear_form (P.C l)) continuous_const

end Polyhedron

end MaxNN
