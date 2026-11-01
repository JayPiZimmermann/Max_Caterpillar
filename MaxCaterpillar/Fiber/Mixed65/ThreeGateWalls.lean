import MaxCaterpillar.Fiber.Mixed65.CarrierForcing

/-! # Wall equations for arbitrary three-gate mixed residuals

Gate zero is the left carrier, gate one the right carrier, and gate two
the negative gate. These labels do not impose a residual normal form.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

theorem ResidualSystem.negative_gate_at_spurious_zero {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (h : d.Represents t)
    (q b c : ℝ) (hc : 0 < c) (hneq : c ≠ max (q + b) b)
    (i : ι) (hi : 0 < d.out i) (hz : d.gate t i q b c = 0) (hW : d.W i ≠ 0) :
    ∃ j, d.out j < 0 ∧ d.gate t j q b c = 0 ∧ d.W j ≠ 0 := by
  obtain ⟨δ, u, v, hδ, hloc⟩ := target_affine_near q b c hc hneq
  have hidentity : ∀ s : ℝ, |s| < δ →
      (∑ j, d.out j * relu (d.W j * s + d.gate t j q b c)) =
        (u - d.lW) * s + (v - d.base t q b c) := by
    intro s hs
    obtain ⟨hcs, htarget⟩ := hloc s hs
    have hh := h q b (c + s)
    rw [htarget] at hh
    have hbase := form_shift_last t d.lU d.lV d.lW d.lT q b c s hc.le hcs
    change d.base t q b (c + s) = d.lW * s + d.base t q b c at hbase
    have hgate : ∀ j, d.gate t j q b (c + s) = d.W j * s + d.gate t j q b c :=
      fun j => form_shift_last t (d.U j) (d.V j) (d.W j) (d.T j) q b c s hc.le hcs
    simp_rw [hbase, hgate] at hh
    nlinarith only [hh]
  exact exists_negative_active_zero_gate d.W (fun j => d.gate t j q b c) d.out
    (u - d.lW) (v - d.base t q b c) δ hδ hidentity i hi hz hW

theorem ResidualSystem.third_gate_zero_at_spurious
    (d : ResidualSystem (Fin 3)) (t : ℝ) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (q b c : ℝ) (hc : 0 < c) (hneq : c ≠ max (q + b) b)
    (i : Fin 3) (hi : 0 < d.out i) (hz : d.gate t i q b c = 0) (hW : d.W i ≠ 0) :
    d.gate t 2 q b c = 0 ∧ d.W 2 ≠ 0 := by
  obtain ⟨j, hj, hjz, hjW⟩ := d.negative_gate_at_spurious_zero t h q b c hc hneq i hi hz hW
  fin_cases j
  · change d.out 0 < 0 at hj
    exact (by linarith only [hj, h0] : False).elim
  · change d.out 1 < 0 at hj
    exact (by linarith only [hj, h1] : False).elim
  · exact ⟨hjz, hjW⟩

/-- The middle target facet forces one of the two free positive coefficients
to vanish. No sign of either free coefficient was assumed. -/
theorem ResidualSystem.middle_facet_dichotomy
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h2 : d.out 2 < 0)
    (hU0 : d.U 0 = -(1 + t) * d.W 0) (hT0 : d.T 0 = d.W 0)
    (hU1 : d.U 1 = -d.W 1) (hV1 : d.V 1 = -d.W 1) :
    d.V 0 = 0 ∨ d.T 1 = 0 := by
  obtain ⟨j, hj, _, hz⟩ := d.positive_gate_on_facet t h 1 (t / 2)
    (by norm_num) (by linarith)
  have hhalf : 0 ≤ t / 2 := by linarith
  have hlast : 0 ≤ 1 + t / 2 := by linarith
  have hT : 0 ≤ t * 1 - t / 2 := by linarith
  fin_cases j
  · left
    change d.gate t 0 1 (t / 2) (1 + t / 2) = 0 at hz
    simp only [ResidualSystem.gate, form, hU0, hT0,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1), relu_of_nonneg hhalf,
      relu_of_nonneg hlast, relu_of_nonneg hT] at hz
    have hp : t * d.V 0 = 0 := by nlinarith only [hz]
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt ht)
  · right
    change d.gate t 1 1 (t / 2) (1 + t / 2) = 0 at hz
    simp only [ResidualSystem.gate, form, hU1, hV1,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1), relu_of_nonneg hhalf,
      relu_of_nonneg hlast, relu_of_nonneg hT] at hz
    have hp : t * d.T 1 = 0 := by nlinarith only [hz]
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt ht)
  · change 0 < d.out 2 at hj
    exact (by linarith only [hj, h2] : False).elim

/-- In the branch with zero left `V` coefficient, the extra left wall fixes
the negative gate's `U,V,W` coefficients. -/
theorem ResidualSystem.negative_form_left_branch
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW0 : d.W 0 ≠ 0) (hU0 : d.U 0 = -(1 + t) * d.W 0) (hV0 : d.V 0 = 0) :
    d.V 2 = 0 ∧ d.U 2 = -(1 + t) * d.W 2 ∧ d.W 2 ≠ 0 := by
  have hz : ∀ b : ℝ, t < b →
      d.gate t 2 1 b (1 + t) = 0 ∧ d.W 2 ≠ 0 := by
    intro b hb
    apply d.third_gate_zero_at_spurious t h h0 h1 1 b (1 + t) (by linarith)
      (by rw [max_eq_left (by linarith : b ≤ 1 + b)]; linarith) 0 h0 _ hW0
    simp only [ResidualSystem.gate, form, hU0, hV0, zero_mul,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t),
      relu_of_nonpos (by linarith : t * 1 - b ≤ 0)]
    ring
  have hc1 := (hz (t + 1) (by linarith)).1
  have hc2 := (hz (t + 2) (by linarith)).1
  simp only [ResidualSystem.gate, form,
    relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    relu_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t),
    relu_of_nonneg (by linarith : (0:ℝ) ≤ t + 1),
    relu_of_nonneg (by linarith : (0:ℝ) ≤ t + 2),
    relu_of_nonpos (by linarith : t * 1 - (t + 1) ≤ 0),
    relu_of_nonpos (by linarith : t * 1 - (t + 2) ≤ 0)] at hc1 hc2
  have hV : d.V 2 = 0 := by nlinarith only [hc1, hc2]
  refine ⟨hV, ?_, (hz (t + 1) (by linarith)).2⟩
  rw [hV] at hc1
  nlinarith only [hc1]

/-- In the branch with zero right `T` coefficient, the extra right wall fixes
the negative gate's `U,T,W` coefficients. -/
theorem ResidualSystem.negative_form_right_branch
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW1 : d.W 1 ≠ 0) (hU1 : d.U 1 = -d.W 1) (hT1 : d.T 1 = 0) :
    d.T 2 = 0 ∧ d.U 2 = -d.W 2 ∧ d.W 2 ≠ 0 := by
  have hz : ∀ b : ℝ, b < 0 → d.gate t 2 1 b 1 = 0 ∧ d.W 2 ≠ 0 := by
    intro b hb
    apply d.third_gate_zero_at_spurious t h h0 h1 1 b 1 (by norm_num)
      (by rw [max_eq_left (by linarith : b ≤ 1 + b)]; linarith) 1 h1 _ hW1
    simp only [ResidualSystem.gate, form, hU1, hT1, zero_mul,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1), relu_of_nonpos hb.le]
    ring
  have hc1 := (hz (-1) (by norm_num)).1
  have hc2 := (hz (-2) (by norm_num)).1
  simp only [ResidualSystem.gate, form,
    relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    relu_of_nonpos (by norm_num : (-1:ℝ) ≤ 0),
    relu_of_nonpos (by norm_num : (-2:ℝ) ≤ 0),
    relu_of_nonneg (by linarith : 0 ≤ t * 1 - (-1)),
    relu_of_nonneg (by linarith : 0 ≤ t * 1 - (-2))] at hc1 hc2
  have hT : d.T 2 = 0 := by nlinarith only [hc1, hc2]
  refine ⟨hT, ?_, (hz (-1) (by norm_num)).2⟩
  rw [hT] at hc1
  nlinarith only [hc1]

end MaxCaterpillar.Fiber.Mixed65
