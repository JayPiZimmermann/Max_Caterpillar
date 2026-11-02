import MaxCaterpillar.Frontier.StarCertificate.CreaseGeneric

/-! # Mixed linear forms cross the positive-gap cone

The chamber application uses strictly positive gap coordinates. Mixedness
is sufficient to construct an actual positive point of the target kernel,
so the final cancellation theorem needs no assumed generic point.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

variable {n : ℕ} {ι : Type*} [Fintype ι]

def positiveGapCone (n : ℕ) : Set (Point n) := {x | ∀ j, 0 < x j}

theorem isOpen_positiveGapCone : IsOpen (positiveGapCone n) := by
  simp only [positiveGapCone, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)

/-- A form with both a negative and a positive coefficient has a zero at
a strictly positive point. The construction adjusts one coordinate of 1. -/
theorem mixed_positive_kernel_point (w₀ : Point n)
    (hneg : ∃ a, w₀ a < 0) (hpos : ∃ a, 0 < w₀ a) :
    ∃ q : Point n, q ∈ positiveGapCone n ∧ lin w₀ q = 0 := by
  classical
  obtain ⟨a, ha⟩ := hneg
  obtain ⟨b, hb⟩ := hpos
  let e : Point n := fun _ => 1
  let r : ℝ := lin w₀ e
  by_cases hr : 0 ≤ r
  · let t : ℝ := -r / w₀ a
    have ht : 0 ≤ t := div_nonneg_of_nonpos (neg_nonpos.mpr hr) ha.le
    refine ⟨e + t • unitVec a, ?_, ?_⟩
    · intro j
      change 0 < 1 + t * unitVec a j
      have hu : 0 ≤ unitVec a j := by
        unfold unitVec
        split_ifs <;> norm_num
      exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hu)
    · rw [lin_add_right, lin_smul_right, lin_unitVec]
      change r + (-r / w₀ a) * w₀ a = 0
      rw [div_mul_cancel _ ha.ne]
      ring
  · let t : ℝ := -r / w₀ b
    have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    have ht : 0 ≤ t := div_nonneg (neg_nonneg.mpr hr') hb.le
    refine ⟨e + t • unitVec b, ?_, ?_⟩
    · intro j
      change 0 < 1 + t * unitVec b j
      have hu : 0 ≤ unitVec b j := by
        unfold unitVec
        split_ifs <;> norm_num
      exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hu)
    · rw [lin_add_right, lin_smul_right, lin_unitVec]
      change r + (-r / w₀ b) * w₀ b = 0
      rw [div_mul_cancel _ hb.ne']
      ring

/-- Actual finite ReLU cancellation on a chamber's positive gap cone.
Mixedness supplies crossing; finite genericity is proved internally. -/
theorem positive_gap_parallel_crease_cancel
    (w : ι → Point n) (c : ι → ℝ) (l : Point n) (β : ℝ)
    (h : ∀ x : Point n, (∀ j, 0 < x j) →
      lin l x + β = ∑ i, c i * relu (lin (w i) x))
    (w₀ : Point n) (hneg : ∃ a, w₀ a < 0) (hpos : ∃ a, 0 < w₀ a)
    (J : Finset ι) (scale : ι → ℝ)
    (hparallel : ∀ i ∈ J, w i = scale i • w₀)
    (hnonparallel : ∀ i ∉ J, ¬ ∃ a : ℝ, w i = a • w₀) :
    (∑ i in J, c i * |scale i|) = 0 := by
  have hw : w₀ ≠ 0 := by
    obtain ⟨a, ha⟩ := hneg
    intro hz
    rw [hz] at ha
    exact (lt_irrefl 0 ha)
  exact open_set_parallel_crease_cancel (positiveGapCone n) isOpen_positiveGapCone
    w c l β h w₀ hw J scale hparallel hnonparallel
    (mixed_positive_kernel_point w₀ hneg hpos)

end MaxCaterpillar.Frontier.StarCertificate
