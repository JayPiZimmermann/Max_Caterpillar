import MaxCaterpillar.Frontier.Basic

/-! Independent research control: exact local sorting rectangles.
No growing-arity obstruction is asserted here. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.ExponentialPush

/-- Rectangular variations of the two opposite comparison directions give
an exact zero-output identity, with an arbitrary common preactivation g. -/
theorem relu_rectangle (g a a' b b' t : ℝ) :
    relu (g + a * relu t + b * relu (-t)) -
      relu (g + a' * relu t + b * relu (-t)) -
      relu (g + a * relu t + b' * relu (-t)) +
      relu (g + a' * relu t + b' * relu (-t)) = 0 := by
  by_cases ht : 0 ≤ t
  · rw [relu_of_nonpos (neg_nonpos.mpr ht)]
    simp only [mul_zero, add_zero]
    ring
  · rw [relu_of_nonpos (le_of_not_ge ht)]
    simp only [mul_zero, add_zero]
    ring

/-- The same identity holds pointwise for any shared nonlinear
preactivation and any real comparison function. -/
theorem relu_rectangle_function {X : Type} (g t : X → ℝ)
    (a a' b b' : ℝ) (x : X) :
    relu (g x + a * relu (t x) + b * relu (-t x)) -
      relu (g x + a' * relu (t x) + b * relu (-t x)) -
      relu (g x + a * relu (t x) + b' * relu (-t x)) +
      relu (g x + a' * relu (t x) + b' * relu (-t x)) = 0 :=
  relu_rectangle (g x) a a' b b' (t x)

example (g a a' b b' t : ℝ) :
    relu (g + a * relu t + b * relu (-t)) +
      relu (g + a' * relu t + b' * relu (-t)) =
    relu (g + a' * relu t + b * relu (-t)) +
      relu (g + a * relu t + b' * relu (-t)) := by
  linarith only [relu_rectangle g a a' b b' t]

#check @relu_rectangle
#check @relu_rectangle_function
#print axioms relu_rectangle
#print axioms relu_rectangle_function
end MaxCaterpillar.Frontier.ExponentialPush
