import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact scalar relations between two planar directions

A vanishing determinant makes two nonzero planar vectors proportional.
Coordinatewise nonpositive products force the proportionality factor to
be negative, including when either coordinate vanishes.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

/-- Two nonzero planar vectors of determinant zero differ by a nonzero scalar. -/
theorem exists_nonzero_scalar_of_det_eq_zero
    (a b c d : ℝ) (hx : a ≠ 0 ∨ b ≠ 0) (hy : c ≠ 0 ∨ d ≠ 0)
    (hdet : a * d - b * c = 0) :
    ∃ k : ℝ, k ≠ 0 ∧ c = k * a ∧ d = k * b := by
  have nonzero_of_relations (k : ℝ) (hc : c = k * a) (hd : d = k * b) : k ≠ 0 := by
    intro hk
    have hc0 : c = 0 := by simpa only [hk, zero_mul] using hc
    have hd0 : d = 0 := by simpa only [hk, zero_mul] using hd
    exact hy.elim (fun h => h hc0) (fun h => h hd0)
  rcases hx with ha | hb
  · have hc : c = c / a * a := by field_simp [ha]
    have hd : d = c / a * b := by
      field_simp [ha]
      nlinarith only [hdet]
    exact ⟨c / a, nonzero_of_relations _ hc hd, hc, hd⟩
  · have hc : c = d / b * a := by
      field_simp [hb]
      nlinarith only [hdet]
    have hd : d = d / b * b := by field_simp [hb]
    exact ⟨d / b, nonzero_of_relations _ hc hd, hc, hd⟩

/-- Determinant zero and coordinatewise opposite signs force antiparallel vectors. -/
theorem exists_pos_neg_scalar_of_det_eq_zero
    (a b c d : ℝ) (hx : a ≠ 0 ∨ b ≠ 0) (hy : c ≠ 0 ∨ d ≠ 0)
    (hdet : a * d - b * c = 0) (hac : a * c ≤ 0) (hbd : b * d ≤ 0) :
    ∃ k : ℝ, 0 < k ∧ c = -k * a ∧ d = -k * b := by
  obtain ⟨k, hk, hc, hd⟩ := exists_nonzero_scalar_of_det_eq_zero a b c d hx hy hdet
  have hknonpos : k ≤ 0 := by
    rcases hx with ha | hb
    · have hs : 0 < a * a := mul_self_pos.mpr ha
      have hprod : k * (a * a) ≤ 0 := by
        rw [hc] at hac
        nlinarith only [hac]
      exact (mul_le_mul_right hs).mp (by simpa only [zero_mul] using hprod)
    · have hs : 0 < b * b := mul_self_pos.mpr hb
      have hprod : k * (b * b) ≤ 0 := by
        rw [hd] at hbd
        nlinarith only [hbd]
      exact (mul_le_mul_right hs).mp (by simpa only [zero_mul] using hprod)
  have hkneg : k < 0 := lt_of_le_of_ne hknonpos hk
  refine ⟨-k, neg_pos.mpr hkneg, ?_, ?_⟩
  · simpa only [neg_neg] using hc
  · simpa only [neg_neg] using hd

#print axioms exists_nonzero_scalar_of_det_eq_zero
#print axioms exists_pos_neg_scalar_of_det_eq_zero
end MaxCaterpillar.Fiber.Count65.SectorSeparation
