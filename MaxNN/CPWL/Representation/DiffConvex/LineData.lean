import MaxNN.CPWL.Pieces.Convexity
import MaxNN.CPWL.Pieces.Topology

/-!
# Restricting a polyhedral witness to a line

Bricks for the difference-of-convex theorem (`MaxNN/CPWL/Representation/DiffConvex.lean`).
Along the parametrized line `t ↦ x + t • v`:

* `AffineFn.eval_line` — an affine function restricts to a one-variable affine function;
* `line_combo`, `line_at_zero`, `line_convex_combo` — the parametrization is affine;
* `Polyhedron.isClosed_line_preimage`, `Polyhedron.convex_line_preimage` — a polyhedral
  piece restricts to a closed convex subset of `ℝ` (an interval).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- An affine function restricted to the line `t ↦ x + t • v` is affine in `t`, with
slope `∑ j, a j * v j` and value `g.eval x` at `t = 0`. -/
theorem AffineFn.eval_line {d : ℕ} (g : AffineFn d) (x v : Fin d → ℝ) (t : ℝ) :
    g.eval (x + t • v) = (∑ j, g.a j * v j) * t + g.eval x := by
  show (∑ j, g.a j * (x + t • v) j) + g.c
      = (∑ j, g.a j * v j) * t + ((∑ j, g.a j * x j) + g.c)
  have hterm : ∀ j : Fin d, g.a j * (x + t • v) j = g.a j * v j * t + g.a j * x j := by
    intro j
    show g.a j * (x j + t * v j) = g.a j * v j * t + g.a j * x j
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- Convex combinations of points on a line stay on the line, with combined parameter. -/
theorem line_combo {d : ℕ} (x v : Fin d → ℝ) {α β : ℝ} (hab : α + β = 1) (t₁ t₂ : ℝ) :
    α • (x + t₁ • v) + β • (x + t₂ • v) = x + (α * t₁ + β * t₂) • v := by
  funext j
  show α * (x j + t₁ * v j) + β * (x j + t₂ * v j) = x j + (α * t₁ + β * t₂) * v j
  have h1 : α * x j + β * x j = x j := by rw [← add_mul, hab, one_mul]
  nlinarith [h1]

theorem line_at_zero {d : ℕ} (x v : Fin d → ℝ) : x + (0 : ℝ) • v = x := by
  funext j
  show x j + 0 * v j = x j
  rw [zero_mul, add_zero]

theorem line_at_one {d : ℕ} (x y : Fin d → ℝ) : x + (1 : ℝ) • (y - x) = y := by
  funext j
  show x j + 1 * (y j - x j) = y j
  ring

/-- `a • x + b • y` is the point at parameter `b` on the line from `x` towards `y`. -/
theorem line_convex_combo {d : ℕ} (x y : Fin d → ℝ) {a b : ℝ} (hab : a + b = 1) :
    a • x + b • y = x + b • (y - x) := by
  funext j
  show a * x j + b * y j = x j + b * (y j - x j)
  have h1 : a * x j + b * x j = x j := by rw [← add_mul, hab, one_mul]
  nlinarith [h1]

namespace Polyhedron

/-- The parameter set of a line inside a polyhedron is closed. -/
theorem isClosed_line_preimage {d : ℕ} (P : Polyhedron d) (x v : Fin d → ℝ) :
    IsClosed {t : ℝ | (x + t • v) ∈ P.carrier} := by
  have hcont : Continuous fun t : ℝ => x + t • v := by
    refine continuous_pi fun j => ?_
    show Continuous fun t : ℝ => x j + t * v j
    exact continuous_const.add (continuous_id.mul continuous_const)
  exact P.isClosed_carrier.preimage hcont

/-- The parameter set of a line inside a polyhedron is convex (an interval). -/
theorem convex_line_preimage {d : ℕ} (P : Polyhedron d) (x v : Fin d → ℝ) :
    Convex ℝ {t : ℝ | (x + t • v) ∈ P.carrier} := by
  intro t₁ h₁ t₂ h₂ α β hα hβ hab
  show (x + (α * t₁ + β * t₂) • v) ∈ P.carrier
  rw [← line_combo x v hab t₁ t₂]
  exact P.convex_carrier h₁ h₂ hα hβ hab

end Polyhedron

end MaxNN
