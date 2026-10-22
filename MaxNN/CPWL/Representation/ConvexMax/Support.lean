import MaxNN.CPWL.Pieces.Polyhedra
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real

/-!
# The support brick: affine pieces of a convex function are global minorants

`AffineFn.le_of_convexOn_of_eqOn_open`: if a convex function `f` agrees with an affine
function `g` on a nonempty **open** set, then `g ≤ f` everywhere.  This is the convexity
half of the "convex CPWL = max of its full-dimensional pieces" theorem
(`MaxNN/CPWL/Representation/ConvexMax.lean`).

The proof needs no support-hyperplane machinery: walk from a point `z` of the open
agreement set a short parameter distance `t` towards an arbitrary `y`; convexity at the
intermediate point plus affinity of `g` gives `t * g y ≤ t * f y`, and `t > 0` cancels.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

namespace AffineFn

/-- An affine function evaluates affinely on convex combinations. -/
theorem eval_convexComb {d : ℕ} (g : AffineFn d) {a b : ℝ} (hab : a + b = 1)
    (x y : Fin d → ℝ) : g.eval (a • x + b • y) = a * g.eval x + b * g.eval y := by
  show (∑ j, g.a j * (a • x + b • y) j) + g.c
      = a * ((∑ j, g.a j * x j) + g.c) + b * ((∑ j, g.a j * y j) + g.c)
  have hcomp : ∀ j : Fin d, g.a j * (a • x + b • y) j
      = a * (g.a j * x j) + b * (g.a j * y j) := by
    intro j
    show g.a j * (a * x j + b * y j) = a * (g.a j * x j) + b * (g.a j * y j)
    ring
  rw [Finset.sum_congr rfl fun j _ => hcomp j, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hc : g.c = a * g.c + b * g.c := by
    rw [← add_mul, hab, one_mul]
  linarith [hc]

/-- **Support brick.**  If a convex function agrees with the affine function `g` on an
open set containing `z`, then `g` is a global minorant of `f`. -/
theorem le_of_convexOn_of_eqOn_open {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) {g : AffineFn d} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {z : Fin d → ℝ} (hz : z ∈ U)
    (hagree : ∀ w ∈ U, f w = g.eval w) (y : Fin d → ℝ) : g.eval y ≤ f y := by
  -- the straight path from `z` towards `y`, and the parameters that stay inside `U`
  have hcont : Continuous fun t : ℝ => (1 - t) • z + t • y := by
    refine continuous_pi fun j => ?_
    show Continuous fun t : ℝ => (1 - t) * z j + t * y j
    exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  have h0mem : (0 : ℝ) ∈ (fun t : ℝ => (1 - t) • z + t • y) ⁻¹' U := by
    show ((1 - (0 : ℝ)) • z + (0 : ℝ) • y) ∈ U
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) 0 h0mem
  set t := min (ε / 2) (1 / 2)
  have ht0 : 0 < t := lt_min (by linarith) one_half_pos
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htlt : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact htlt
  have hz' : ((1 - t) • z + t • y) ∈ U := hball htball
  -- convexity at the intermediate point
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hcx := hconv.2 (Set.mem_univ z) (Set.mem_univ y) h1t (le_of_lt ht0)
    (by rw [sub_add_cancel])
  rw [smul_eq_mul, smul_eq_mul] at hcx
  have h2 : f ((1 - t) • z + t • y) = g.eval ((1 - t) • z + t • y) :=
    hagree _ hz'
  have h3 : g.eval ((1 - t) • z + t • y) = (1 - t) * g.eval z + t * g.eval y :=
    g.eval_convexComb (by rw [sub_add_cancel]) z y
  have h4 : f z = g.eval z := hagree z hz
  have h5 : t * f z = t * g.eval z := by rw [h4]
  have key : t * g.eval y ≤ t * f y := by linarith
  exact le_of_mul_le_mul_left key ht0

end AffineFn

end MaxNN
