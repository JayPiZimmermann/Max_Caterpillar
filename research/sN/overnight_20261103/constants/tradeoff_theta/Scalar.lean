import research.sN.overnight_20261103.constants.tradeoff.ScalarMin

/-! Small-arity absorption for the improved theta-cutoff width tradeoff. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta

theorem scaled_linear_absorption (n C y : ℝ) (hn : 3≤n) (hC : 1≤C)
    (hy : 0≤y) (hsmall : n≤50000*C) (hlinear : n≤2*y+2) :
    n^2/(175000*C)≤y := by
  have hC0 : 0<C := by linarith only [hC]
  have hp : 0≤(n-3)*(50000*C-n) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hsmall])
  have hl := mul_le_mul_of_nonneg_left hlinear hC0.le
  have hCy : y≤C*y := by
    have hh := mul_le_mul_of_nonneg_right hC hy
    simpa only [one_mul] using hh
  apply (div_le_iff (mul_pos (by norm_num : (0:ℝ)<175000) hC0)).mpr
  linarith only [hp,hl,hlinear,hCy,hC,hy]

#print axioms scaled_linear_absorption
end MaxCaterpillar.OvernightConstants.TradeoffTheta
