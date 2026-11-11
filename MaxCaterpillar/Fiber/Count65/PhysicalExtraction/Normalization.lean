import MaxCaterpillar.Fiber.Symmetry

/-! # Positive physical normalization of nonzero second-layer outputs

This is the existing second-neuron scaling symmetry applied to output
magnitudes. The first hidden layer is unchanged, every function is unchanged,
and zero/nonzero carrier incidences are unchanged.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open MaxCaterpillar.Frontier

variable {N h₁ h₂ : ℕ}

noncomputable def normalizeSecond (net : Network N h₁ h₂) : Network N h₁ h₂ :=
  scaleSecond net (fun k => |net.w₃ k|)

theorem normalizeSecond_eval (net : Network N h₁ h₂)
    (h : ∀ k, net.w₃ k ≠ 0) (x : Point N) :
    (normalizeSecond net).eval x = net.eval x :=
  scaleSecond_eval net (fun k => |net.w₃ k|) (fun k => abs_pos.mpr (h k)) x

theorem normalizeSecond_first (net : Network N h₁ h₂) :
    (normalizeSecond net).W₁ = net.W₁ := rfl

theorem normalizeSecond_unit_outputs (net : Network N h₁ h₂)
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin h₂) :
    (normalizeSecond net).w₃ k = 1 ∨ (normalizeSecond net).w₃ k = -1 := by
  change net.w₃ k / |net.w₃ k| = 1 ∨ net.w₃ k / |net.w₃ k| = -1
  rcases lt_or_gt_of_ne (h k) with hk | hk
  · right
    rw [abs_of_neg hk]
    field_simp [hk.ne]
  · left
    rw [abs_of_pos hk, div_self hk.ne']

theorem normalizeSecond_second_zero_iff (net : Network N h₁ h₂)
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin h₂) (j : Fin h₁) :
    (normalizeSecond net).W₂ k j = 0 ↔ net.W₂ k j = 0 := by
  change |net.w₃ k| * net.W₂ k j = 0 ↔ net.W₂ k j = 0
  rw [mul_eq_zero]
  simp only [(abs_pos.mpr (h k)).ne', false_or]

theorem normalizeSecond_positive_output_iff (net : Network N h₁ h₂)
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin h₂) :
    0 < (normalizeSecond net).w₃ k ↔ 0 < net.w₃ k := by
  change 0 < net.w₃ k / |net.w₃ k| ↔ 0 < net.w₃ k
  simp only [div_pos_iff, abs_pos.mpr (h k),
    not_lt_of_ge (abs_nonneg (net.w₃ k)), and_true, and_false, or_false]

theorem normalizeSecond_negative_output_iff (net : Network N h₁ h₂)
    (h : ∀ k, net.w₃ k ≠ 0) (k : Fin h₂) :
    (normalizeSecond net).w₃ k < 0 ↔ net.w₃ k < 0 := by
  change net.w₃ k / |net.w₃ k| < 0 ↔ net.w₃ k < 0
  simp only [div_neg_iff, abs_pos.mpr (h k),
    not_lt_of_ge (abs_nonneg (net.w₃ k)), and_true, and_false, false_or]

#print axioms normalizeSecond_eval
#print axioms normalizeSecond_unit_outputs
#print axioms normalizeSecond_second_zero_iff
end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
