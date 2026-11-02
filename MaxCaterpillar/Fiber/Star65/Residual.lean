import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Exact residual identities for the positive-path Max4 family

These identities hold for every real input and every parameter in the stated
closed parameter domains. They prove sufficiency of both residual branches,
including their common first-layer endpoint `r = 1`. They do not assert that
these branches exhaust the fiber or count its connected components.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

/-- The feature-linear comparison reconstructed from the fourth first-layer feature. -/
noncomputable def comparison (r q b : ℝ) : ℝ :=
  (max 0 (q + r * b) - (1 - r) * max 0 q) / r

/-- The first residual coefficient branch, with slack parameter `k ≤ 0`. -/
noncomputable def branchI (r k q b c : ℝ) : ℝ :=
  let U := max 0 q
  let V := max 0 b
  let W := max 0 c
  let A := comparison r q b
  W + max 0 (A - W) + max 0 (V - W + k * U) -
    max 0 (A - U - W + k * U)

/-- The second residual coefficient branch, with slack parameter `h ≤ -1`. -/
noncomputable def branchII (r h q b c : ℝ) : ℝ :=
  let U := max 0 q
  let V := max 0 b
  let W := max 0 c
  let A := comparison r q b
  W + max 0 (A - W + h * V) + max 0 (U + V - W) -
    max 0 (U + (1 + h) * V - W)

private lemma add_positive_part_sub (a w : ℝ) :
    w + max 0 (a - w) = max a w := by
  rcases le_total a w with haw | hwa
  · rw [max_eq_left (sub_nonpos.mpr haw), max_eq_right haw]
    ring
  · rw [max_eq_right (sub_nonneg.mpr hwa), max_eq_left hwa]
    ring

private lemma target_of_q_nonpos {q b c : ℝ} (hq : q ≤ 0) :
    max (max 0 (q + b)) (max b c) = max (max 0 b) (max 0 c) := by
  apply le_antisymm
  · apply max_le
    · exact max_le (le_trans (le_max_left 0 b) (le_max_left _ _))
        (le_trans (by linarith : q + b ≤ b)
          (le_trans (le_max_right 0 b) (le_max_left _ _)))
    · exact max_le (le_trans (le_max_right 0 b) (le_max_left _ _))
        (le_trans (le_max_right 0 c) (le_max_right _ _))
  · apply max_le
    · exact max_le (le_trans (le_max_left 0 (q + b)) (le_max_left _ _))
        (le_trans (le_max_left b c) (le_max_right _ _))
    · exact max_le (le_trans (le_max_left 0 (q + b)) (le_max_left _ _))
        (le_trans (le_max_right b c) (le_max_right _ _))

private lemma target_of_nonneg {q b c : ℝ} (hq : 0 ≤ q) (hb : 0 ≤ b) :
    max (max 0 (q + b)) (max b c) = max (q + b) (max 0 c) := by
  rw [max_eq_right (add_nonneg hq hb)]
  apply le_antisymm
  · exact max_le (le_max_left _ _)
      (max_le (le_trans (by linarith : b ≤ q + b) (le_max_left _ _))
        (le_trans (le_max_right 0 c) (le_max_right _ _)))
  · exact max_le (le_max_left _ _)
      (max_le (le_trans (add_nonneg hq hb) (le_max_left _ _))
        (le_trans (le_max_right b c) (le_max_right _ _)))

private lemma target_of_b_nonpos {q b c : ℝ} (hb : b ≤ 0) :
    max (max 0 (q + b)) (max b c) = max (q + b) (max 0 c) := by
  apply le_antisymm
  · exact max_le
      (max_le (le_trans (le_max_left 0 c) (le_max_right _ _)) (le_max_left _ _))
      (max_le (le_trans hb (le_trans (le_max_left 0 c) (le_max_right _ _)))
        (le_trans (le_max_right 0 c) (le_max_right _ _)))
  · exact max_le (le_trans (le_max_right 0 (q + b)) (le_max_left _ _))
      (max_le (le_trans (le_max_left 0 (q + b)) (le_max_left _ _))
        (le_trans (le_max_right b c) (le_max_right _ _)))

lemma comparison_of_nonneg {r q b : ℝ} (hr : 0 < r) (hq : 0 ≤ q) (hb : 0 ≤ b) :
    comparison r q b = q + b := by
  unfold comparison
  rw [max_eq_right hq, max_eq_right (add_nonneg hq (mul_nonneg hr.le hb))]
  apply (div_eq_iff (ne_of_gt hr)).2
  ring

lemma comparison_le_of_q_nonpos {r q b : ℝ} (hr : 0 < r) (hq : q ≤ 0) :
    comparison r q b ≤ max 0 b := by
  unfold comparison
  rw [max_eq_left hq, mul_zero, sub_zero]
  apply (div_le_iff hr).2
  apply max_le
  · exact mul_nonneg (le_max_left 0 b) hr.le
  · have h := mul_le_mul_of_nonneg_left (le_max_right 0 b) hr.le
    nlinarith only [hq, h]

lemma comparison_le_q_of_b_nonpos {r q b : ℝ} (hr : 0 < r) (hq : 0 ≤ q)
    (hb : b ≤ 0) : comparison r q b ≤ q := by
  unfold comparison
  rw [max_eq_right hq]
  apply (div_le_iff hr).2
  have hT : max 0 (q + r * b) ≤ q :=
    max_le hq (by nlinarith only [hr, hb])
  nlinarith only [hT]

lemma max_comparison_of_b_nonpos {r q b c : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq : 0 ≤ q) (hb : b ≤ 0) :
    max (comparison r q b) (max 0 c) = max (q + b) (max 0 c) := by
  by_cases ht : 0 ≤ q + r * b
  · have ha : comparison r q b = q + b := by
      unfold comparison
      rw [max_eq_right hq, max_eq_right ht]
      apply (div_eq_iff (ne_of_gt hr)).2
      ring
    rw [ha]
  · have ht' : q + r * b ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have ha : comparison r q b ≤ 0 := by
      unfold comparison
      rw [max_eq_right hq, max_eq_left ht']
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hr1, hq]) hr.le
    have hab : q + b ≤ 0 := by nlinarith only [hr1, hb, ht']
    rw [max_eq_right (le_trans ha (le_max_left 0 c)),
      max_eq_right (le_trans hab (le_max_left 0 c))]

/-- Branch I computes the invariant Max4 residual for every real input. -/
theorem branchI_eq_max {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : k ≤ 0)
    (q b c : ℝ) : branchI r k q b c = max (max 0 (q + b)) (max b c) := by
  rcases le_total q 0 with hq | hq
  · unfold branchI
    dsimp only
    simp only [max_eq_left hq, mul_zero, add_zero, sub_zero]
    have hc := add_positive_part_sub (max 0 b) (max 0 c)
    rw [target_of_q_nonpos hq]
    linarith only [hc]
  · rcases le_total 0 b with hb | hb
    · unfold branchI
      dsimp only
      rw [max_eq_right hq, max_eq_right hb, comparison_of_nonneg hr hq hb,
        target_of_nonneg hq hb]
      have hsame : q + b - q - max 0 c + k * q = b - max 0 c + k * q := by ring
      rw [hsame]
      have hc := add_positive_part_sub (q + b) (max 0 c)
      linarith only [hc]
    · unfold branchI
      dsimp only
      rw [max_eq_right hq, max_eq_left hb]
      have hku : k * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk hq
      have hw : 0 ≤ max 0 c := le_max_left _ _
      have ha := comparison_le_q_of_b_nonpos hr hq hb
      rw [max_eq_left (by linarith only [hku, hw] : 0 - max 0 c + k * q ≤ 0),
        max_eq_left (by linarith only [ha, hku, hw] :
          comparison r q b - q - max 0 c + k * q ≤ 0)]
      rw [add_zero, sub_zero, add_positive_part_sub,
        max_comparison_of_b_nonpos hr hr1 hq hb, target_of_b_nonpos hb]

/-- Branch II computes the same invariant Max4 residual for every real input. -/
theorem branchII_eq_max {r h : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hh : h ≤ -1)
    (q b c : ℝ) : branchII r h q b c = max (max 0 (q + b)) (max b c) := by
  rcases le_total q 0 with hq | hq
  · unfold branchII
    dsimp only
    rw [max_eq_left hq]
    have ha := comparison_le_of_q_nonpos (b := b) hr hq
    have hv : 0 ≤ max 0 b := le_max_left _ _
    have hw : 0 ≤ max 0 c := le_max_left _ _
    have hhV : (1 + h) * max 0 b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hh]) hv
    rw [max_eq_left (by nlinarith only [ha, hhV, hw] :
        comparison r q b - max 0 c + h * max 0 b ≤ 0),
      max_eq_left (by linarith only [hhV, hw] :
        0 + (1 + h) * max 0 b - max 0 c ≤ 0)]
    simp only [add_zero, zero_add, sub_zero]
    rw [add_positive_part_sub, target_of_q_nonpos hq]
  · rcases le_total 0 b with hb | hb
    · unfold branchII
      dsimp only
      rw [max_eq_right hq, max_eq_right hb, comparison_of_nonneg hr hq hb,
        target_of_nonneg hq hb]
      have hsame : q + b - max 0 c + h * b = q + (1 + h) * b - max 0 c := by ring
      rw [hsame]
      have hc := add_positive_part_sub (q + b) (max 0 c)
      linarith only [hc]
    · unfold branchII
      dsimp only
      rw [max_eq_right hq, max_eq_left hb]
      simp only [mul_zero, add_zero]
      have hc := add_positive_part_sub (comparison r q b) (max 0 c)
      rw [max_comparison_of_b_nonpos hr hr1 hq hb, ← target_of_b_nonpos hb] at hc
      linarith only [hc]

/-- Reversing a residual preactivation is compensated by its linear part. -/
theorem orientation_identity (a : ℝ) : max 0 a = a + max 0 (-a) := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h)]
    ring

end MaxCaterpillar.Fiber.Star65
