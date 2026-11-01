import MaxCaterpillar.Fiber.Mixed65.PhysicalCoefficientBound
import MaxCaterpillar.Fiber.Mixed65.Blowup

/-! # The physical coefficient divergence bound

An arbitrary exact physical completion supplies three original residual gates.
The all-input three-gate divergence theorem applies to their unchanged
coefficients, and their coefficient size is a subsum of the physical size.
Thus no choice of residual normalization or of a bounded parameter chart is
assumed. Biases are allowed in the physical inequality through recession.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators

/-- The extracted residual size is bounded by the original physical size. -/
theorem physicalResidualSystem_coefficientSize_le {m : ℕ} (net : Network 4 6 m)
    (S : Finset (Fin m)) (l : Fin m → ℝ) :
    (physicalResidualSystem net S l).coefficientSize ≤ coefficientSize net := by
  exact physicalResidualSystem_effective_sum_le net S l

/-- The divergence inequality holds for every actual exact mixed completion,
including arbitrary biases. No output signs or nonzero coefficients are assumed. -/
theorem physical_coefficient_bound (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    1 ≤ t * coefficientSize net := by
  classical
  obtain ⟨S, hS, l, hrep⟩ := physical_three_gate_extraction net t ht hW hmax
  have hd := physicalResidualSystem_represents net t S l hrep
  have hcard : Fintype.card S = 3 := by simpa only [Fintype.card_coe] using hS
  have hb := (physicalResidualSystem net S l).three_gate_coefficient_bound t ht hd hcard
  exact hb.trans (mul_le_mul_of_nonneg_left
    (physicalResidualSystem_coefficientSize_le net S l) ht.le)

/-- The previously isolated physical bound is discharged for the full exact
fiber, rather than for a chosen residual chart. -/
theorem normalizedCoefficientBound : NormalizedCoefficientBound := by
  intro t ht net _ hW
  exact physical_coefficient_bound net.val t ht hW net.property

end MaxCaterpillar.Fiber.Mixed65
