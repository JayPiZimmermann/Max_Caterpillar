import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Ring

/-! # Scalar exponential-series bounds for a conditional growing-arity argument

These are analytic scalar inequalities only. They do not supply any local
structural matching hypothesis or an unconditional network lower bound.
The reciprocal `(c ^ q)⁻¹` is explicit because q is a natural number.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching

/-- A single nonnegative term of the real exponential series bounds every
polynomial-times-exponential factor, including q=0 and eta=0. -/
theorem pow_mul_exp_neg_div_factorial_le_inv_pow
    (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η) (q : ℕ) :
    η ^ q * Real.exp (-(c * η)) / (q.factorial : ℝ) ≤ (c ^ q)⁻¹ := by
  have hseries := Real.pow_div_factorial_le_exp (c * η) (mul_nonneg hc.le hη) q
  apply (mul_le_mul_right (pow_pos hc q)).mp
  calc
    (η ^ q * Real.exp (-(c * η)) / (q.factorial : ℝ)) * c ^ q =
        ((c * η) ^ q / (q.factorial : ℝ)) * Real.exp (-(c * η)) := by
      rw [mul_pow]
      ring
    _ ≤ Real.exp (c * η) * Real.exp (-(c * η)) :=
      mul_le_mul_of_nonneg_right hseries (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp
    _ = (c ^ q)⁻¹ * c ^ q := (inv_mul_cancel (pow_ne_zero q hc.ne')).symm

/-- Multiplication by a nonnegative amplitude and an arbitrary exponential
shift. No sign assumption on P or d is needed for this scalar implication. -/
theorem le_shifted_exp_envelope
    (P A c η d : ℝ) (q : ℕ) (hc : 0 < c) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hP : P ≤ A * η ^ q / (q.factorial : ℝ) * Real.exp (-(c * (η - d)))) :
    P ≤ A * (c ^ q)⁻¹ * Real.exp (c * d) := by
  calc
    P ≤ A * η ^ q / (q.factorial : ℝ) * Real.exp (-(c * (η - d))) := hP
    _ = (A * Real.exp (c * d)) *
        (η ^ q * Real.exp (-(c * η)) / (q.factorial : ℝ)) := by
      rw [show -(c * (η - d)) = -(c * η) + c * d by ring,Real.exp_add]
      ring
    _ ≤ (A * Real.exp (c * d)) * (c ^ q)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_div_factorial_le_inv_pow c η hc hη q)
        (mul_nonneg hA (Real.exp_pos _).le)
    _ = A * (c ^ q)⁻¹ * Real.exp (c * d) := by ring

#print axioms pow_mul_exp_neg_div_factorial_le_inv_pow
#print axioms le_shifted_exp_envelope
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
