import MaxCaterpillar.Frontier.Basic

/-! # Turning a normalized crease ratio into a physical coefficient bound -/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

/-- A unit target jump and a large normalized incoming ratio force a large
original output-times-input coefficient. The sign of the preactivation is free. -/
theorem effective_bound_of_ratio (t o v w : ℝ) (ht : 0 < t) (ho : 0 < o)
    (hw : w ≠ 0) (hr : 1 ≤ t * (v / w)) (ha : 1 ≤ o * |w|) :
    1 ≤ t * |o * v| := by
  have hk : 0 ≤ v / w := by
    by_contra hn
    have hh := mul_neg_of_pos_of_neg ht (lt_of_not_ge hn)
    linarith only [hh, hr]
  have hv : v = (v / w) * w := (div_mul_cancel v hw).symm
  have habs : |v| = (v / w) * |w| := by
    calc
      |v| = |(v / w) * w| := congrArg abs hv
      _ = |v / w| * |w| := abs_mul _ _
      _ = (v / w) * |w| := by rw [abs_of_nonneg hk]
  rw [abs_mul, abs_of_pos ho, habs]
  have hmul := mul_le_mul_of_nonneg_left ha (mul_nonneg ht.le hk)
  nlinarith only [hmul, hr]

end MaxCaterpillar.Fiber.Mixed65
