import MaxCaterpillar.Fiber.Mixed65.Clipping

/-! # Full coefficient span of strict sign domains

The assertions are about actual feature functions. A readout vanishing on the
indicated strict sign domain must have all four coefficients zero. The proofs
use arbitrarily small positive perturbations of actual feature rays and include
all boundary parameter values of the mixed residual charts.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

lemma affine_coefficients_zero_of_vanish_negative {g₀ g₁ f₀ f₁ : ℝ}
    (hg : g₀ < 0)
    (h : ∀ s : ℝ, 0 ≤ s → g₀ + s * g₁ < 0 → f₀ + s * f₁ = 0) :
    f₀ = 0 ∧ f₁ = 0 := by
  have hf₀ : f₀ = 0 := by
    simpa only [zero_mul, add_zero] using h 0 le_rfl (by simpa using hg)
  obtain ⟨s, hs, hsg⟩ := exists_pos_mul_lt (neg_pos.mpr hg) g₁
  have hf := h s hs.le (by nlinarith only [hsg])
  have he : s * f₁ = 0 := by linarith only [hf₀, hf]
  exact ⟨hf₀, (mul_eq_zero.mp he).resolve_left (ne_of_gt hs)⟩

lemma affine_coefficients_zero_of_vanish_positive {g₀ g₁ f₀ f₁ : ℝ}
    (hg : 0 < g₀)
    (h : ∀ s : ℝ, 0 ≤ s → 0 < g₀ + s * g₁ → f₀ + s * f₁ = 0) :
    f₀ = 0 ∧ f₁ = 0 := by
  apply affine_coefficients_zero_of_vanish_negative
    (g₀ := -g₀) (g₁ := -g₁) (neg_neg_of_pos hg)
  intro s hs hneg
  exact h s hs (by nlinarith only [hneg])

lemma form_a_add_v {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (A B C D : ℝ) :
    form t A B C D 1 (t + s) 0 = (A + t * B) + s * B := by
  have he : t * 1 - (t + s) = -s := by ring
  simp only [form, he, relu_of_nonneg (add_nonneg ht hs),
    relu_of_nonpos (neg_nonpos.mpr hs)]
  norm_num [relu]
  ring

lemma form_a_add_b {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (A B C D : ℝ) :
    form t A B C D (1 + s) t 0 = (A + t * B) + s * (A + t * D) := by
  have hq : 0 ≤ 1 + s := by linarith only [hs]
  have he : t * (1 + s) - t = t * s := by ring
  simp only [form, he, relu_of_nonneg hq, relu_of_nonneg ht,
    relu_of_nonneg (mul_nonneg ht hs)]
  norm_num [relu]
  ring

lemma form_b_add_a {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (A B C D : ℝ) :
    form t A B C D (1 + s) (s * t) 0 = (A + t * D) + s * (A + t * B) := by
  have hq : 0 ≤ 1 + s := by linarith only [hs]
  have he : t * (1 + s) - s * t = t := by ring
  simp only [form, he, relu_of_nonneg hq, relu_of_nonneg ht,
    relu_of_nonneg (mul_nonneg hs ht)]
  norm_num [relu]
  ring

lemma form_b_add_u {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (A B C D : ℝ) :
    form t A B C D 1 (-s) 0 = (A + t * D) + s * D := by
  have he : t * 1 - -s = t + s := by ring
  simp only [form, he, relu_of_nonpos (neg_nonpos.mpr hs),
    relu_of_nonneg (add_nonneg ht hs)]
  norm_num [relu]
  ring

lemma form_add_w_nonneg {s : ℝ} (hs : 0 ≤ s) (t A B C D q b : ℝ) :
    form t A B C D q b s = form t A B C D q b 0 + s * C := by
  simp only [form, relu_of_nonneg hs]
  norm_num [relu]
  ring

lemma form_w_add_v {s : ℝ} (hs : 0 ≤ s) (t A B C D : ℝ) :
    form t A B C D 0 s 1 = C + s * B := by
  simp only [form, mul_zero, zero_sub, relu_of_nonneg hs,
    relu_of_nonpos (neg_nonpos.mpr hs)]
  norm_num [relu]
  ring

lemma form_w_add_u {s : ℝ} (hs : 0 ≤ s) (t A B C D : ℝ) :
    form t A B C D 0 (-s) 1 = C + s * D := by
  simp only [form, mul_zero, zero_sub, neg_neg, relu_of_nonneg hs,
    relu_of_nonpos (neg_nonpos.mpr hs)]
  norm_num [relu]
  ring

lemma form_w_add_a {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (A B C D : ℝ) :
    form t A B C D s (t * s) 1 = C + s * (A + t * B) := by
  simp only [form, sub_self, relu_of_nonneg hs, relu_of_nonneg (mul_nonneg ht hs)]
  norm_num [relu]
  ring

/-- Negativity on the first middle ray gives a sign domain with full coefficient span. -/
theorem coefficients_zero_of_vanish_on_negative_a {t A B C D a b c d : ℝ}
    (ht : 0 < t) (hga : a + t * b < 0)
    (h : ∀ q v w : ℝ, form t a b c d q v w < 0 → form t A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hv : A + t * B = 0 ∧ B = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hga
    intro s hs hg
    have hh := h 1 (t + s) 0 (by simpa only [form_a_add_v ht.le hs] using hg)
    simpa only [form_a_add_v ht.le hs] using hh
  have hb : A + t * B = 0 ∧ A + t * D = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hga
    intro s hs hg
    have hh := h (1 + s) t 0 (by simpa only [form_a_add_b ht.le hs] using hg)
    simpa only [form_a_add_b ht.le hs] using hh
  have hw : A + t * B = 0 ∧ C = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hga
    intro s hs hg
    have hh := h 1 t s (by simpa only [form_add_w_nonneg hs, form_a ht.le] using hg)
    simpa only [form_add_w_nonneg hs, form_a ht.le] using hh
  have hA : A = 0 := by simpa only [hv.2, mul_zero, add_zero] using hv.1
  have hD : D = 0 := by
    have he : t * D = 0 := by simpa only [hA, zero_add] using hb.2
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)
  exact ⟨hA, hv.2, hw.2, hD⟩

/-- Negativity on the other middle ray gives the same full-span conclusion. -/
theorem coefficients_zero_of_vanish_on_negative_b {t A B C D a b c d : ℝ}
    (ht : 0 < t) (hgb : a + t * d < 0)
    (h : ∀ q v w : ℝ, form t a b c d q v w < 0 → form t A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hu : A + t * D = 0 ∧ D = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hgb
    intro s hs hg
    have hh := h 1 (-s) 0 (by simpa only [form_b_add_u ht.le hs] using hg)
    simpa only [form_b_add_u ht.le hs] using hh
  have ha : A + t * D = 0 ∧ A + t * B = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hgb
    intro s hs hg
    have hh := h (1 + s) (s * t) 0 (by simpa only [form_b_add_a ht.le hs] using hg)
    simpa only [form_b_add_a ht.le hs] using hh
  have hw : A + t * D = 0 ∧ C = 0 := by
    apply affine_coefficients_zero_of_vanish_negative hgb
    intro s hs hg
    have hh := h 1 0 s (by simpa only [form_add_w_nonneg hs, form_b ht.le] using hg)
    simpa only [form_add_w_nonneg hs, form_b ht.le] using hh
  have hA : A = 0 := by simpa only [hu.2, mul_zero, add_zero] using hu.1
  have hB : B = 0 := by
    have he : t * B = 0 := by simpa only [hA, zero_add] using ha.2
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)
  exact ⟨hA, hB, hw.2, hu.2⟩

/-- A positive coefficient on the independent `W` ray gives full span of
the positive sign domain. -/
theorem coefficients_zero_of_vanish_on_positive {t A B C D a b c d : ℝ}
    (ht : 0 < t) (hgc : 0 < c)
    (h : ∀ q v w : ℝ, 0 < form t a b c d q v w → form t A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hv : C = 0 ∧ B = 0 := by
    apply affine_coefficients_zero_of_vanish_positive hgc
    intro s hs hg
    have hh := h 0 s 1 (by simpa only [form_w_add_v hs] using hg)
    simpa only [form_w_add_v hs] using hh
  have hu : C = 0 ∧ D = 0 := by
    apply affine_coefficients_zero_of_vanish_positive hgc
    intro s hs hg
    have hh := h 0 (-s) 1 (by simpa only [form_w_add_u hs] using hg)
    simpa only [form_w_add_u hs] using hh
  have ha : C = 0 ∧ A + t * B = 0 := by
    apply affine_coefficients_zero_of_vanish_positive hgc
    intro s hs hg
    have hh := h s (t * s) 1 (by simpa only [form_w_add_a ht.le hs] using hg)
    simpa only [form_w_add_a ht.le hs] using hh
  have hA : A = 0 := by simpa only [hv.2, mul_zero, add_zero] using ha.2
  exact ⟨hA, hv.2, hv.1, hu.2⟩

end MaxCaterpillar.Fiber.Mixed65
