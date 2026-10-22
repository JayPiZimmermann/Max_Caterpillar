import MaxNN.Core.Relu
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith

/-!
# One-variable convexity bricks

Small `ConvexOn` facts on `ℝ` used by the one-dimensional core of the
difference-of-convex theorem (`MaxNN/CPWL/Representation/DiffConvex/OneDim/Core.lean`):
affine functions, `relu ∘ affine`, `max` of two affine functions, finite sums, and the
lattice identity `min a b + relu (a-b) + relu (b-a) = max a b` that absorbs a concave
kink into the pair sum.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- One-variable affine functions are convex on any convex set. -/
theorem convexOn_affine1 {D : Set ℝ} (hD : Convex ℝ D) (c e : ℝ) :
    ConvexOn ℝ D (fun t => c * t + e) := by
  refine ⟨hD, fun x _ y _ a b _ _ hab => ?_⟩
  show c * (a * x + b * y) + e ≤ a * (c * x + e) + b * (c * y + e)
  have h1 : a * e + b * e = e := by rw [← add_mul, hab, one_mul]
  linarith

/-- `relu` of a one-variable affine function is convex on any convex set. -/
theorem convexOn_relu_affine1 {D : Set ℝ} (hD : Convex ℝ D) (c e : ℝ) :
    ConvexOn ℝ D (fun t => relu (c * t + e)) :=
  ConvexOn.sup (convexOn_const 0 hD) (convexOn_affine1 hD c e)

/-- `relu` of a difference of two one-variable affine functions is convex on any
convex set. -/
theorem convexOn_relu_affine_sub {D : Set ℝ} (hD : Convex ℝ D) (c₁ e₁ c₂ e₂ : ℝ) :
    ConvexOn ℝ D (fun t => relu ((c₁ * t + e₁) - (c₂ * t + e₂))) := by
  have e : (fun t => relu ((c₁ * t + e₁) - (c₂ * t + e₂)))
      = fun t => relu ((c₁ - c₂) * t + (e₁ - e₂)) := by
    funext t
    rw [show (c₁ * t + e₁) - (c₂ * t + e₂) = (c₁ - c₂) * t + (e₁ - e₂) from by ring]
  rw [e]
  exact convexOn_relu_affine1 hD _ _

/-- The maximum of two one-variable affine functions is convex on any convex set. -/
theorem convexOn_max_affine1 {D : Set ℝ} (hD : Convex ℝ D) (c₁ e₁ c₂ e₂ : ℝ) :
    ConvexOn ℝ D (fun t => max (c₁ * t + e₁) (c₂ * t + e₂)) :=
  ConvexOn.sup (convexOn_affine1 hD c₁ e₁) (convexOn_affine1 hD c₂ e₂)

/-- A finite sum of convex functions is convex. -/
theorem convexOn_finset_sum {ι : Type _} [DecidableEq ι] {E : Type _} [AddCommMonoid E]
    [SMul ℝ E] {D : Set E} (hD : Convex ℝ D)
    (s : Finset ι) (F : ι → E → ℝ) (hF : ∀ i ∈ s, ConvexOn ℝ D (F i)) :
    ConvexOn ℝ D (fun t => ∑ i in s, F i t) := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun t : E => ∑ i in (∅ : Finset ι), F i t) = fun _ => (0 : ℝ) := by
      funext t
      exact Finset.sum_empty
    rw [e]
    exact convexOn_const 0 hD
  · intro a s ha ih hF
    have e : (fun t : E => ∑ i in insert a s, F i t)
        = fun t => F a t + ∑ i in s, F i t := by
      funext t
      exact Finset.sum_insert ha
    rw [e]
    exact ConvexOn.add (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- The lattice identity that absorbs a concave kink into the pair sum:
`min a b + relu (a - b) + relu (b - a) = max a b`. -/
theorem min_add_relu_add_relu (a b : ℝ) :
    min a b + relu (a - b) + relu (b - a) = max a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, relu_of_nonpos (sub_nonpos.mpr h),
      relu_of_nonneg (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left h, relu_of_nonneg (sub_nonneg.mpr h),
      relu_of_nonpos (sub_nonpos.mpr h)]
    ring

end MaxNN
