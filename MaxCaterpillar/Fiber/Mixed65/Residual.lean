import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic

/-! # Exact residual identities for the mixed Max4 dictionary

These are identities for every real input and every admissible real parameter.
They prove sufficiency of both residual charts. They do not assert that the
charts exhaust arbitrary networks or count their connected components.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

private lemma add_relu_sub (a w : ℝ) : a + relu (w - a) = max a w := by
  rcases le_total a w with h | h
  · rw [relu_of_nonneg (sub_nonneg.mpr h), max_eq_right h]
    ring
  · rw [relu_of_nonpos (sub_nonpos.mpr h), max_eq_left h]
    ring

/-- The first residual chart, with the independent nonnegative `W` feature. -/
theorem residualA (t k q b w : ℝ) (ht : 0 < t) (hk : 1 ≤ t * k) (hw : 0 ≤ w) :
    relu q + relu b + relu (w - (1 + t) * relu q + relu (t * q - b)) +
      relu (w - relu q - relu b + k * relu (t * q - b)) -
      relu (w - (1 + t) * relu q + (k + 1) * relu (t * q - b)) =
      max (max (q + b) b) w := by
  have hk0 : 0 < k := by nlinarith
  rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg hb]
    rcases le_total 0 q with hq | hq
    · rw [relu_of_nonneg hq, max_eq_left (by linarith : b ≤ q + b)]
      rcases le_total 0 (t * q - b) with hT | hT
      · rw [relu_of_nonneg hT]
        have hR : w - (1 + t) * q + (t * q - b) = w - (q + b) := by ring
        have hD : w - (1 + t) * q + (k + 1) * (t * q - b) =
            w - q - b + k * (t * q - b) := by ring
        rw [hR, hD]
        linarith [add_relu_sub (q + b) w]
      · rw [relu_of_nonpos hT]
        simp only [mul_zero, add_zero]
        have hS : w - q - b = w - (q + b) := by ring
        rw [hS]
        linarith [add_relu_sub (q + b) w]
    · have hT : t * q - b ≤ 0 := by nlinarith
      rw [relu_of_nonpos hq, relu_of_nonpos hT,
        max_eq_right (by linarith : q + b ≤ b)]
      simp only [mul_zero, sub_zero, add_zero, zero_add]
      linarith [add_relu_sub b w]
  · rw [relu_of_nonpos hb]
    rcases le_total 0 q with hq | hq
    · have hT : 0 ≤ t * q - b := by nlinarith
      rw [relu_of_nonneg hq, relu_of_nonneg hT,
        max_eq_left (by linarith : b ≤ q + b)]
      have hprod : 0 ≤ (t * k - 1) * q := mul_nonneg (by linarith) hq
      have hkb : k * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le hb
      have hS : 0 ≤ w - q - 0 + k * (t * q - b) := by
        nlinarith only [hw, hprod, hkb]
      have hD : 0 ≤ w - (1 + t) * q + (k + 1) * (t * q - b) := by
        nlinarith only [hS, hb]
      rw [relu_of_nonneg hS, relu_of_nonneg hD]
      have hR : w - (1 + t) * q + (t * q - b) = w - (q + b) := by ring
      rw [hR]
      nlinarith only [add_relu_sub (q + b) w]
    · rw [relu_of_nonpos hq, max_eq_right (by linarith : q + b ≤ b),
        max_eq_right (hb.trans hw)]
      simp only [mul_zero, sub_zero, zero_add]
      have hT := relu_nonneg (t * q - b)
      have hS : 0 ≤ w + k * relu (t * q - b) := by positivity
      have hD : 0 ≤ w + (k + 1) * relu (t * q - b) := by positivity
      rw [relu_of_nonneg (add_nonneg hw hT), relu_of_nonneg hS,
        relu_of_nonneg hD]
      ring

/-- The second residual chart, with the independent nonnegative `W` feature. -/
theorem residualB (t r q b w : ℝ) (ht : 0 < t) (hr : 1 + t ≤ t * r)
    (hw : 0 ≤ w) :
    (1 + t) * relu q - relu (t * q - b) +
      relu (w - (1 + t) * relu q + r * relu b + relu (t * q - b)) +
      relu (w - relu q - relu b) - relu (w - relu q + (r - 1) * relu b) =
      max (max (q + b) b) w := by
  have hr1 : 1 < r := by nlinarith
  rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg hb]
    rcases le_total 0 q with hq | hq
    · rw [relu_of_nonneg hq, max_eq_left (by linarith : b ≤ q + b)]
      rcases le_total 0 (t * q - b) with hT | hT
      · rw [relu_of_nonneg hT]
        have hR : w - (1 + t) * q + r * b + (t * q - b) =
            w - q + (r - 1) * b := by ring
        have hS : w - q - b = w - (q + b) := by ring
        rw [hR, hS]
        nlinarith only [add_relu_sub (q + b) w]
      · rw [relu_of_nonpos hT]
        have hprod : 0 ≤ (t * r - (1 + t)) * q := mul_nonneg (by linarith) hq
        have hprod2 : 0 ≤ (r - 1) * (b - t * q) :=
          mul_nonneg (by linarith) (by linarith)
        have hD : 0 ≤ w - q + (r - 1) * b := by
          nlinarith only [hw, hprod, hprod2]
        have hR : 0 ≤ w - (1 + t) * q + r * b + 0 := by
          nlinarith only [hD, hT]
        rw [relu_of_nonneg hR, relu_of_nonneg hD]
        have hS : w - q - b = w - (q + b) := by ring
        rw [hS]
        nlinarith only [add_relu_sub (q + b) w]
    · have hT : t * q - b ≤ 0 := by nlinarith
      rw [relu_of_nonpos hq, relu_of_nonpos hT,
        max_eq_right (by linarith : q + b ≤ b)]
      simp only [mul_zero, sub_zero, zero_add, add_zero]
      have hR : 0 ≤ w + r * b := by positivity
      have hD : 0 ≤ w + (r - 1) * b :=
        add_nonneg hw (mul_nonneg (by linarith) hb)
      rw [relu_of_nonneg hR, relu_of_nonneg hD]
      nlinarith only [add_relu_sub b w]
  · rw [relu_of_nonpos hb]
    rcases le_total 0 q with hq | hq
    · have hT : 0 ≤ t * q - b := by nlinarith
      rw [relu_of_nonneg hq, relu_of_nonneg hT,
        max_eq_left (by linarith : b ≤ q + b)]
      simp only [mul_zero, sub_zero, add_zero]
      have hR : w - (1 + t) * q + (t * q - b) = w - (q + b) := by ring
      rw [hR]
      nlinarith only [add_relu_sub (q + b) w]
    · rw [relu_of_nonpos hq, max_eq_right (by linarith : q + b ≤ b),
        max_eq_right (hb.trans hw)]
      simp only [mul_zero, sub_zero, zero_sub, zero_add, add_zero]
      rw [relu_of_nonneg (add_nonneg hw (relu_nonneg (t * q - b)))]
      ring

/-- A residual gate can be reversed while absorbing its linear part. -/
theorem orientation_identity (u : ℝ) (reverse : Bool) :
    relu (if reverse then -u else u) + (if reverse then u else 0) = relu u := by
  cases reverse
  · simp
  · change relu (-u) + u = relu u
    linarith [relu_sub_relu_neg u]

/-- All eight orientation choices preserve a three-core residual identity. -/
theorem three_orientations (F R S D : ℝ) (i j k : Bool) :
    (F + (if i then R else 0) + (if j then S else 0) - (if k then D else 0)) +
      relu (if i then -R else R) + relu (if j then -S else S) -
      relu (if k then -D else D) = F + relu R + relu S - relu D := by
  linarith only [orientation_identity R i, orientation_identity S j,
    orientation_identity D k]

end MaxCaterpillar.Fiber.Mixed65
