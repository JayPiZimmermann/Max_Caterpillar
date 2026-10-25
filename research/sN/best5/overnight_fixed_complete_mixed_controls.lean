import Mathlib

/- Exact elementary controls for the mixed-chamber propagation argument.
   The complete geometric/network theorem remains a written proof. -/
namespace OvernightCompleteMixed

/-- A Boolean quadratic on a three-cube is determined by its other seven corners. -/
theorem quadratic_cube_missing_corner (a b c d e f g : ℝ)
    (h1 : a+b=0) (h2 : a+c=0) (h3 : a+d=0)
    (h12 : a+b+c+e=0) (h13 : a+b+d+f=0) (h23 : a+c+d+g=0)
    (h123 : a+b+c+d+e+f+g=0) : a=0 := by
  linarith

/-- Opposite nonzero coefficients yield a zero with both gap coordinates positive. -/
theorem positive_gap_zero (a b : ℝ) (ha : 0<a) (hb : b<0) :
    ∃ s t : ℝ, 0<s ∧ 0<t ∧ a*s+b*t=0 := by
  refine ⟨-b,a,neg_pos.mpr hb,ha,?_⟩
  ring

#print axioms quadratic_cube_missing_corner
#print axioms positive_gap_zero
end OvernightCompleteMixed
