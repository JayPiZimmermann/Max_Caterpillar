import Mathlib.Data.Real.Basic

/-!
# `relu` and the one-hidden-layer base case

`relu x = max 0 x`, and the identity `max x y = relu (y - x) + x`, which is the base case
of every depth upper bound in this project.

House style (see `.claude/skills/formalization-conventions`): no `simp`, no `sorry`.
-/

namespace MaxNN

/-- The rectified linear unit. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_left 0 x

theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_right hx

theorem relu_of_nonpos {x : ℝ} (hx : x ≤ 0) : relu x = 0 := max_eq_left hx

/-- The maximum of two reals is computable with one hidden layer. -/
theorem max_eq_relu_add (x y : ℝ) : max x y = relu (y - x) + x := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, relu_of_nonneg (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left h, relu_of_nonpos (sub_nonpos.mpr h)]
    ring

/-- The identity passes through one `relu` layer: `x = relu x - relu (-x)`.
This is how network surgery carries a value unchanged past a hidden layer. -/
theorem relu_sub_relu_neg (x : ℝ) : relu x - relu (-x) = x := by
  rcases le_total 0 x with h | h
  · rw [relu_of_nonneg h, relu_of_nonpos (neg_nonpos.mpr h), sub_zero]
  · rw [relu_of_nonpos h, relu_of_nonneg (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- Positive homogeneity of `relu` along a nonnegative ray. -/
theorem relu_mul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    relu (a * t) = t * relu a := by
  rcases le_total 0 a with ha | ha
  · rw [relu_of_nonneg (mul_nonneg ha ht), relu_of_nonneg ha, mul_comm]
  · rw [relu_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha ht), relu_of_nonpos ha,
      mul_zero]

/-- A sum of two binary maxima is a maximum of the four pairwise sums.  This is how a
one-hidden-layer building block `max + max` flattens into a list of affine terms. -/
theorem max_add_max (a b c d : ℝ) :
    max a b + max c d = max (max (a + c) (a + d)) (max (b + c) (b + d)) := by
  have hmono : ∀ {p q : ℝ}, p ≤ q → ∀ r s : ℝ,
      max (p + r) (p + s) ≤ max (q + r) (q + s) := by
    intro p q hpq r s
    exact max_le (le_trans (add_le_add_right hpq r) (le_max_left _ _))
      (le_trans (add_le_add_right hpq s) (le_max_right _ _))
  rcases le_total a b with hab | hab
  · rcases le_total c d with hcd | hcd
    · rw [max_eq_right hab, max_eq_right hcd, max_eq_right (hmono hab c d),
        max_eq_right (add_le_add_left hcd b)]
    · rw [max_eq_right hab, max_eq_left hcd, max_eq_right (hmono hab c d),
        max_eq_left (add_le_add_left hcd b)]
  · rcases le_total c d with hcd | hcd
    · rw [max_eq_left hab, max_eq_right hcd, max_eq_left (hmono hab c d),
        max_eq_right (add_le_add_left hcd a)]
    · rw [max_eq_left hab, max_eq_left hcd, max_eq_left (hmono hab c d),
        max_eq_left (add_le_add_left hcd a)]

end MaxNN
