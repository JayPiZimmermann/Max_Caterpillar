import MaxNN.Core.Affine
import MaxNN.CPWL.Pieces.Polyhedra

/-!
# Bundling a family of scalar affine functions into one affine layer

`Affine.ofRows g` is the affine map `ℝ^d → ℝ^m` whose `i`-th component is the scalar
affine function `g i : AffineFn d`.  This is the (free) network layer that turns a
pointwise maximum of `m` affine functions into `MAX m` precomposed with an affine map —
the key step of the finitary conditional-collapse theorem
(`MaxNN/CPWL/Conditional/Finitary.lean`), since affine precomposition costs no hidden
layers (`comp_affine_mem_reluClass`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Affine

/-- The affine map `ℝ^d → ℝ^m` whose `i`-th component (row) is the scalar affine
function `g i`. -/
noncomputable def ofRows {d m : ℕ} (g : Fin m → AffineFn d) : Affine d m where
  A := fun i j => (g i).a j
  b := fun i => (g i).c

theorem ofRows_eval {d m : ℕ} (g : Fin m → AffineFn d) (x : Fin d → ℝ) :
    (ofRows g).eval x = fun i => (g i).eval x := rfl

end Affine

end MaxNN
