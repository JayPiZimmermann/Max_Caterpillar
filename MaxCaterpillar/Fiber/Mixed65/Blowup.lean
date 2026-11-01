import MaxCaterpillar.Fiber.Mixed65.ThreeGateWalls
import MaxCaterpillar.Fiber.Mixed65.SpuriousBounds
import MaxCaterpillar.Fiber.Mixed65.CarrierAmplitude
import MaxCaterpillar.Fiber.Mixed65.ThreeGateOrdering
import MaxCaterpillar.Fiber.Mixed65.RatioBound

/-! # Coefficient blowup for every three-gate mixed residual

The output and incoming weights in this theorem are the original weights.
No orientation or positive scaling is hidden in the coefficient norm.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators

noncomputable def ResidualSystem.coefficientSize {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) : ℝ :=
  ∑ i, (|d.out i * d.U i| + |d.out i * d.V i| +
    |d.out i * d.W i| + |d.out i * d.T i|)

theorem ResidualSystem.abs_effective_V_le {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (j : ι) : |d.out j * d.V j| ≤ d.coefficientSize := by
  classical
  have hs := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      add_nonneg (add_nonneg (add_nonneg (abs_nonneg (d.out i * d.U i))
        (abs_nonneg (d.out i * d.V i))) (abs_nonneg (d.out i * d.W i)))
        (abs_nonneg (d.out i * d.T i))) (Finset.mem_univ j)
  change |d.out j * d.U j| + |d.out j * d.V j| + |d.out j * d.W j| +
    |d.out j * d.T j| ≤ d.coefficientSize at hs
  linarith only [hs, abs_nonneg (d.out j * d.U j), abs_nonneg (d.out j * d.W j),
    abs_nonneg (d.out j * d.T j)]

theorem ResidualSystem.abs_effective_T_le {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (j : ι) : |d.out j * d.T j| ≤ d.coefficientSize := by
  classical
  have hs := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      add_nonneg (add_nonneg (add_nonneg (abs_nonneg (d.out i * d.U i))
        (abs_nonneg (d.out i * d.V i))) (abs_nonneg (d.out i * d.W i)))
        (abs_nonneg (d.out i * d.T i))) (Finset.mem_univ j)
  change |d.out j * d.U j| + |d.out j * d.V j| + |d.out j * d.W j| +
    |d.out j * d.T j| ≤ d.coefficientSize at hs
  linarith only [hs, abs_nonneg (d.out j * d.U j), abs_nonneg (d.out j * d.V j),
    abs_nonneg (d.out j * d.W j)]

theorem ResidualSystem.ordered_coefficient_bound
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1) (h2 : d.out 2 < 0)
    (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0)
    (hU0 : d.U 0 = -(1 + t) * d.W 0) (hT0 : d.T 0 = d.W 0)
    (hU1 : d.U 1 = -d.W 1) (hV1 : d.V 1 = -d.W 1) :
    1 ≤ t * d.coefficientSize := by
  obtain ⟨ha0, ha1⟩ := d.carrier_amplitudes_ge_one t ht h h2.le hW0 hU0 hT0 hW1 hU1 hV1
  rcases d.middle_facet_dichotomy t ht h h2 hU0 hT0 hU1 hV1 with hV0 | hT1
  · obtain ⟨hV2, hU2, hW2⟩ := d.negative_form_left_branch t ht h h0 h1 hW0 hU0 hV0
    have hr := d.right_coefficient_bound t ht h h0 h1 hW1 hU1 hV2 hU2 hW2
    have hb := effective_bound_of_ratio t (d.out 1) (d.T 1) (d.W 1) ht h1 hW1 hr ha1
    exact hb.trans (mul_le_mul_of_nonneg_left (d.abs_effective_T_le 1) ht.le)
  · obtain ⟨hT2, hU2, hW2⟩ := d.negative_form_right_branch t ht h h0 h1 hW1 hU1 hT1
    have hr := d.left_coefficient_bound t ht h h0 h1 hW0 hU0 hT2 hU2 hW2
    have hb := effective_bound_of_ratio t (d.out 0) (d.V 0) (d.W 0) ht h0 hW0
      (by linarith only [hr, ht]) ha0
    exact hb.trans (mul_le_mul_of_nonneg_left (d.abs_effective_V_le 0) ht.le)

/-- Every exact residual using exactly three arbitrary real gates has an
effective coefficient sum at least `1/t`. No chart classification is assumed. -/
theorem ResidualSystem.three_gate_coefficient_bound {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) :
    1 ≤ t * d.coefficientSize := by
  obtain ⟨e, he, h0, h1, h2, hW0, hW1, hU0, hT0, hU1, hV1⟩ :=
    d.exists_ordered_three_gate t ht h hcard
  have hb := (d.reindex e).ordered_coefficient_bound t ht he
    h0 h1 h2 hW0 hW1 hU0 hT0 hU1 hV1
  have hs : (d.reindex e).coefficientSize = d.coefficientSize := d.reindex_effective_sum e
  rwa [hs] at hb

end MaxCaterpillar.Fiber.Mixed65
