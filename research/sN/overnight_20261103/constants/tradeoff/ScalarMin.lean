import Mathlib

/-! Convert a family of scaled-width inequalities to its literal minimum tradeoff. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.Tradeoff

/-- The uniform linear lower bound controls the entire small-arity branch,
including the boundary N=3 and arbitrary real scale C≥1. -/
theorem scaled_linear_absorption (n C y : ℝ) (hn : 3≤n) (hC : 1≤C)
    (hy : 0≤y) (hsmall : n≤250000*C) (hlinear : n≤2*y+2) :
    n^2/(650000*C)≤y := by
  have hC0 : 0<C := by linarith only [hC]
  have hp : 0≤(n-3)*(250000*C-n) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hsmall])
  have hl := mul_le_mul_of_nonneg_left hlinear hC0.le
  have hCy : y≤C*y := by
    have hh := mul_le_mul_of_nonneg_right hC hy
    simpa only [one_mul] using hh
  apply (div_le_iff (mul_pos (by norm_num : (0:ℝ)<650000) hC0)).mpr
  linarith only [hp,hl,hlinear,hCy,hC,hy]

theorem min_tradeoff_of_scaled (x M y D : ℝ) (hx : 0<x) (hD : 0<D)
    (hscaled : ∀ C : ℝ, 1≤C → M≤C*x → x/(D*C)≤y) :
    min x (x^2/M)/D≤y := by
  by_cases hMx : M≤x
  · have hh := hscaled 1 le_rfl (by simpa only [one_mul] using hMx)
    rw [mul_one] at hh
    exact (div_le_div_of_le hD.le (min_le_left _ _)).trans hh
  · have hM : 0<M := hx.trans (lt_of_not_ge hMx)
    have hC : 1≤M/x := (le_div_iff hx).mpr (by linarith only [lt_of_not_ge hMx])
    have hw : M≤(M/x)*x := by rw [div_mul_cancel M hx.ne']
    have hh := hscaled (M/x) hC hw
    have heq : x/(D*(M/x))=(x^2/M)/D := by
      field_simp [hx.ne',hM.ne',hD.ne']
      <;> ring
    rw [heq] at hh
    exact (div_le_div_of_le hD.le (min_le_right _ _)).trans hh

/-- Both zero and subquadratic denominators are handled by the theorem,
without importing a convention that division by zero is infinite. -/
example : min (9:ℝ) (9^2/0)/(650000:ℝ)≤1 := by norm_num

#check @min_tradeoff_of_scaled
#print axioms min_tradeoff_of_scaled
#print axioms scaled_linear_absorption
end MaxCaterpillar.OvernightConstants.Tradeoff
