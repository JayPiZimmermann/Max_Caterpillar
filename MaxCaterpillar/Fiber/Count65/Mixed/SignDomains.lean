import MaxCaterpillar.Fiber.Mixed65.SignSpans

/-! # Both sign domains of a mixed residual core span all four coefficients

A nonzero independent-feature coefficient and an oppositely signed middle ray
suffice. The conclusion quantifies over actual all-real feature functions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Frontier

/-- No nonzero feature readout vanishes on either strict sign domain. -/
def FormBothSignSpans (t a b c d : ℝ) : Prop :=
  ∀ A B C D : ℝ,
    ((∀ q v w : ℝ, 0 < form t a b c d q v w → form t A B C D q v w = 0) →
      A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0) ∧
    ((∀ q v w : ℝ, form t a b c d q v w < 0 → form t A B C D q v w = 0) →
      A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0)

lemma form_both_sign_spans_of_middle_a (t a b c d : ℝ) (ht : 0 < t)
    (hopposite : c * (a+t*b) < 0) : FormBothSignSpans t a b c d := by
  intro A B C D
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have ha : 0 < a+t*b := by
      by_contra hn
      have hm := mul_nonneg_of_nonpos_of_nonpos hc.le (le_of_not_gt hn)
      linarith only [hopposite,hm]
    have hnega : -a+t*(-b) < 0 := by nlinarith only [ha]
    constructor
    · intro h
      apply coefficients_zero_of_vanish_on_negative_a (a := -a) (b := -b)
        (c := -c) (d := -d) ht hnega
      intro q v w hneg
      rw [form_neg] at hneg
      exact h q v w (by linarith only [hneg])
    · intro h
      apply coefficients_zero_of_vanish_on_positive (a := -a) (b := -b)
        (c := -c) (d := -d) ht (neg_pos.mpr hc)
      intro q v w hpos
      rw [form_neg] at hpos
      exact h q v w (by linarith only [hpos])
  · subst c
    norm_num at hopposite
  · have ha : a+t*b < 0 := by
      by_contra hn
      have hm := mul_nonneg hc.le (le_of_not_gt hn)
      linarith only [hopposite,hm]
    exact ⟨fun h => coefficients_zero_of_vanish_on_positive ht hc h,
      fun h => coefficients_zero_of_vanish_on_negative_a ht ha h⟩

lemma form_both_sign_spans_of_middle_b (t a b c d : ℝ) (ht : 0 < t)
    (hopposite : c * (a+t*d) < 0) : FormBothSignSpans t a b c d := by
  intro A B C D
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have ha : 0 < a+t*d := by
      by_contra hn
      have hm := mul_nonneg_of_nonpos_of_nonpos hc.le (le_of_not_gt hn)
      linarith only [hopposite,hm]
    have hnega : -a+t*(-d) < 0 := by nlinarith only [ha]
    constructor
    · intro h
      apply coefficients_zero_of_vanish_on_negative_b (a := -a) (b := -b)
        (c := -c) (d := -d) ht hnega
      intro q v w hneg
      rw [form_neg] at hneg
      exact h q v w (by linarith only [hneg])
    · intro h
      apply coefficients_zero_of_vanish_on_positive (a := -a) (b := -b)
        (c := -c) (d := -d) ht (neg_pos.mpr hc)
      intro q v w hpos
      rw [form_neg] at hpos
      exact h q v w (by linarith only [hpos])
  · subst c
    norm_num at hopposite
  · have ha : a+t*d < 0 := by
      by_contra hn
      have hm := mul_nonneg hc.le (le_of_not_gt hn)
      linarith only [hopposite,hm]
    exact ⟨fun h => coefficients_zero_of_vanish_on_positive ht hc h,
      fun h => coefficients_zero_of_vanish_on_negative_b ht ha h⟩

/-- The first middle-ray test covers every row of branch A, with either orientation. -/
theorem form_both_sign_spans_of_middle_a_multiple (t a b c d : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) (ha : a+t*b = -(1+t)*c) : FormBothSignSpans t a b c d := by
  apply form_both_sign_spans_of_middle_a t a b c d ht
  rw [ha]
  have hc2 : 0 < c*c := mul_self_pos.mpr hc
  have hm := mul_pos (show 0 < 1+t by linarith) hc2
  nlinarith only [hm]

/-- The other middle ray covers the two noncentral branch-B rows. -/
theorem form_both_sign_spans_of_middle_b_multiple (t a b c d : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) (ha : a+t*d = -c) : FormBothSignSpans t a b c d := by
  apply form_both_sign_spans_of_middle_b t a b c d ht
  rw [ha]
  have hc2 : 0 < c*c := mul_self_pos.mpr hc
  nlinarith only [hc2]

end MaxCaterpillar.Fiber.Mixed65
