import MaxCaterpillar.Fiber.JumpBalance

/-! # Local crease cancellation for actual finite ReLU sums

The hypotheses are identities of functions on an open set. The conclusion
is the signed absolute slope balance along an actual line through that set.
The one-dimensional midpoint calculation is reused from `JumpBalance`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators Filter Topology

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Every line through a point of an open set stays in that set for a
sufficiently small two-sided interval. -/
theorem open_line_interval (U : Set (Point n)) (hU : IsOpen U)
    (q v : Point n) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ → q + s • v ∈ U := by
  have hc : Continuous (fun s : ℝ => q + s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun s : ℝ => q + s • v) (𝓝 0) (𝓝 q) := by
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have he := ht.eventually (hU.mem_nhds hq)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, fun s hs => hb ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs

/-- Restricting an actual open-set identity to a line gives zero total
signed kink amplitude of precisely the forms vanishing at its base point. -/
theorem open_set_line_balance (U : Set (Point n)) (hU : IsOpen U)
    (w : ι → Point n) (c : ι → ℝ) (l : Point n) (β : ℝ)
    (h : ∀ x ∈ U, lin l x + β = ∑ i, c i * relu (lin (w i) x))
    (q v : Point n) (hq : q ∈ U) :
    (∑ i in Finset.univ.filter (fun i => lin (w i) q = 0),
      c i * |lin (w i) v|) = 0 := by
  obtain ⟨δ, hδ, hline⟩ := open_line_interval U hU q v hq
  apply MaxCaterpillar.Fiber.affine_jump_balance
    (fun i => lin (w i) v) (fun i => lin (w i) q) c
    (lin l v) (lin l q + β) δ hδ
  intro s hs
  have hh := h (q + s • v) (hline s hs)
  simp only [lin_add_right, lin_smul_right] at hh
  convert hh using 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring

/-- At a generic point of a target hyperplane, the open-set identity
forces cancellation of the complete parallel class, including zero forms. -/
theorem generic_parallel_crease_balance (U : Set (Point n)) (hU : IsOpen U)
    (w : ι → Point n) (c : ι → ℝ) (l : Point n) (β : ℝ)
    (h : ∀ x ∈ U, lin l x + β = ∑ i, c i * relu (lin (w i) x))
    (w₀ q v : Point n) (J : Finset ι) (scale : ι → ℝ)
    (hqU : q ∈ U) (hq : lin w₀ q = 0) (hv : lin w₀ v = 1)
    (hparallel : ∀ i ∈ J, w i = scale i • w₀)
    (havoid : ∀ i ∉ J, lin (w i) q ≠ 0) :
    (∑ i in J, c i * |scale i|) = 0 := by
  classical
  have hzero : Finset.univ.filter (fun i => lin (w i) q = 0) = J := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hij
      exact havoid i hij hi
    · intro hi
      rw [hparallel i hi, lin_smul_left, hq, mul_zero]
  have hh := open_set_line_balance U hU w c l β h q v hqU
  rw [hzero] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hparallel i hi, lin_smul_left, hv, mul_one]

/-- A nonzero coefficient vector has a direction on which its form is one. -/
theorem exists_unit_direction (w₀ : Point n) (hw : w₀ ≠ 0) :
    ∃ v : Point n, lin w₀ v = 1 := by
  classical
  have he : ∃ a, w₀ a ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hw
    funext a
    exact hn a
  obtain ⟨a, ha⟩ := he
  refine ⟨(w₀ a)⁻¹ • unitVec a, ?_⟩
  rw [lin_smul_right, lin_unitVec, inv_mul_cancel ha]

/-- Vanishing on a nonzero form's kernel is exactly the condition needed
for a coefficient vector to be its scalar multiple. -/
theorem multiple_of_vanishes_on_kernel (w₀ w : Point n) (hw : w₀ ≠ 0)
    (hker : ∀ x : Point n, lin w₀ x = 0 → lin w x = 0) :
    ∃ a : ℝ, w = a • w₀ := by
  obtain ⟨v, hv⟩ := exists_unit_direction w₀ hw
  refine ⟨lin w v, ?_⟩
  funext j
  have hz : lin w₀ (unitVec j - (w₀ j) • v) = 0 := by
    rw [lin_sub_right, lin_unitVec, lin_smul_right, hv, mul_one, sub_self]
  have hh := hker (unitVec j - (w₀ j) • v) hz
  rw [lin_sub_right, lin_unitVec, lin_smul_right] at hh
  change w j = lin w v * w₀ j
  linarith only [hh]

/-- Every nonparallel form has a nonzero restriction to the target kernel. -/
theorem nonparallel_kernel_witness (w₀ w : Point n) (hw : w₀ ≠ 0)
    (hn : ¬ ∃ a : ℝ, w = a • w₀) :
    ∃ v : Point n, lin w₀ v = 0 ∧ lin w v ≠ 0 := by
  classical
  by_contra hh
  push_neg at hh
  exact hn (multiple_of_vanishes_on_kernel w₀ w hw hh)

end MaxCaterpillar.Frontier.StarCertificate
