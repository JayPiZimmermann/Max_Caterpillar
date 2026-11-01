import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Clipping rigidity of the mixed four-feature dictionary

This module concerns actual functions on all real inputs. It does not assume
that an abstract cone description is the feature image. The required rays and
their adjacent sums are evaluated explicitly.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

/-- A linear readout of the four invariant features of the mixed dictionary. -/
noncomputable def form (t A B C D q b c : ℝ) : ℝ :=
  A * relu q + B * relu b + C * relu c + D * relu (t * q - b)

/-- Two real values lie in one of the two closed sign half-lines. -/
def SameSign (a b : ℝ) : Prop :=
  (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)

lemma sameSign_of_relu_add {a b : ℝ}
    (h : relu (a + b) = relu a + relu b) : SameSign a b := by
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · rw [relu_of_nonneg ha, relu_of_nonpos hb, add_zero] at h
      rcases le_total 0 (a + b) with hab | hab
      · rw [relu_of_nonneg hab] at h
        exact Or.inl ⟨ha, by linarith⟩
      · rw [relu_of_nonpos hab] at h
        exact Or.inr ⟨by linarith, hb⟩
  · rcases le_total 0 b with hb | hb
    · rw [relu_of_nonpos ha, relu_of_nonneg hb, zero_add] at h
      rcases le_total 0 (a + b) with hab | hab
      · rw [relu_of_nonneg hab] at h
        exact Or.inl ⟨by linarith, hb⟩
      · rw [relu_of_nonpos hab] at h
        exact Or.inr ⟨ha, by linarith⟩
    · exact Or.inr ⟨ha, hb⟩

/-- The four-ray relation, also preserved by clipping, closes the sign chain. -/
lemma four_ray_same_sign {t v a b u : ℝ} (ht : 0 < t)
    (hva : SameSign v a) (hab : SameSign a b) (hbu : SameSign b u)
    (hlin : a + t * u = b + t * v)
    (hclip : relu a + t * relu u = relu b + t * relu v) :
    (0 ≤ v ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ u) ∨
      (v ≤ 0 ∧ a ≤ 0 ∧ b ≤ 0 ∧ u ≤ 0) := by
  rcases hva with ⟨hv, ha⟩ | ⟨hv, ha⟩
  · rcases hab with ⟨ha', hb⟩ | ⟨ha', hb⟩
    · rcases hbu with ⟨hb', hu⟩ | ⟨hb', hu⟩
      · exact Or.inl ⟨hv, ha, hb, hu⟩
      · rw [relu_of_nonneg ha, relu_of_nonpos hu, relu_of_nonpos hb',
          relu_of_nonneg hv] at hclip
        have hu' : 0 ≤ u := by nlinarith only [ht, hlin, hclip, hb]
        exact Or.inl ⟨hv, ha, hb, hu'⟩
    · rcases hbu with ⟨hb', hu⟩ | ⟨hb', hu⟩
      · exact Or.inl ⟨hv, ha, hb', hu⟩
      · rw [relu_of_nonpos ha', relu_of_nonpos hu, relu_of_nonpos hb,
          relu_of_nonneg hv] at hclip
        have hv' : v ≤ 0 := by nlinarith only [ht, hclip]
        exact Or.inr ⟨hv', ha', hb, hu⟩
  · rcases hab with ⟨ha', hb⟩ | ⟨ha', hb⟩
    · rcases hbu with ⟨hb', hu⟩ | ⟨hb', hu⟩
      · rw [relu_of_nonpos ha, relu_of_nonneg hu, relu_of_nonneg hb,
          relu_of_nonpos hv] at hclip
        have hv' : 0 ≤ v := by nlinarith only [ht, hlin, hclip, ha']
        exact Or.inl ⟨hv', ha', hb, hu⟩
      · exact Or.inr ⟨hv, ha, hb', hu⟩
    · rcases hbu with ⟨hb', hu⟩ | ⟨hb', hu⟩
      · rw [relu_of_nonpos ha, relu_of_nonneg hu, relu_of_nonpos hb,
          relu_of_nonpos hv] at hclip
        have hu' : u ≤ 0 := by nlinarith only [ht, hclip]
        exact Or.inr ⟨hv, ha, hb, hu'⟩
      · exact Or.inr ⟨hv, ha, hb, hu⟩

lemma form_v (t A B C D : ℝ) : form t A B C D 0 1 0 = B := by
  norm_num [form, relu]

lemma form_u (t A B C D : ℝ) : form t A B C D 0 (-1) 0 = D := by
  norm_num [form, relu]

lemma form_a {t : ℝ} (ht : 0 ≤ t) (A B C D : ℝ) :
    form t A B C D 1 t 0 = A + t * B := by
  simp only [form, mul_one, sub_self, relu_of_nonneg ht]
  norm_num [relu]
  ring

lemma form_b {t : ℝ} (ht : 0 ≤ t) (A B C D : ℝ) :
    form t A B C D 1 0 0 = A + t * D := by
  simp only [form, mul_one, sub_zero, relu_of_nonneg ht]
  norm_num [relu]
  ring

lemma form_w (t A B C D : ℝ) : form t A B C D 0 0 1 = C := by
  norm_num [form, relu]

lemma form_av {t : ℝ} (ht : 0 ≤ t) (A B C D : ℝ) :
    form t A B C D 1 (t + 1) 0 = (A + t * B) + B := by
  have htp : 0 ≤ t + 1 := by linarith
  have he : t * 1 - (t + 1) = -1 := by ring
  simp only [form, he, relu_of_nonneg htp]
  norm_num [relu]
  ring

lemma form_ab {t : ℝ} (ht : 0 ≤ t) (A B C D : ℝ) :
    form t A B C D 2 t 0 = (A + t * B) + (A + t * D) := by
  have he : t * 2 - t = t := by ring
  simp only [form, he, relu_of_nonneg ht]
  norm_num [relu]
  ring

lemma form_bu {t : ℝ} (ht : 0 ≤ t) (A B C D : ℝ) :
    form t A B C D 1 (-1) 0 = (A + t * D) + D := by
  have htp : 0 ≤ t + 1 := by linarith
  have he : t * 1 - -1 = t + 1 := by ring
  simp only [form, he, relu_of_nonneg htp]
  norm_num [relu]
  ring

lemma form_add_w (t A B C D q b : ℝ) :
    form t A B C D q b 1 = form t A B C D q b 0 + C := by
  simp only [form]
  norm_num [relu]
  ring

lemma form_nonneg {t A B C D : ℝ} (ht : 0 < t)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (ha : 0 ≤ A + t * B) (hb : 0 ≤ A + t * D) (q b c : ℝ) :
    0 ≤ form t A B C D q b c := by
  have hw : 0 ≤ C * relu c := mul_nonneg hC (relu_nonneg c)
  rcases le_total 0 q with hq | hq
  · rcases le_total (t * q) b with hqb | hqb
    · have hb0 : 0 ≤ b := (mul_nonneg ht.le hq).trans hqb
      have hzero : relu (t * q - b) = 0 := relu_of_nonpos (by linarith)
      rw [form, relu_of_nonneg hq, relu_of_nonneg hb0, hzero, mul_zero, add_zero]
      have h1 := mul_nonneg ha hq
      have h2 := mul_nonneg hB (sub_nonneg.mpr hqb)
      nlinarith only [h1, h2, hw]
    · rcases le_total 0 b with hb0 | hb0
      · rw [form, relu_of_nonneg hq, relu_of_nonneg hb0,
          relu_of_nonneg (sub_nonneg.mpr hqb)]
        have h1 := mul_nonneg ha hb0
        have h2 := mul_nonneg hb (sub_nonneg.mpr hqb)
        have h3 := mul_nonneg ht.le hw
        nlinarith only [ht, h1, h2, h3]
      · rw [form, relu_of_nonneg hq, relu_of_nonpos hb0,
          relu_of_nonneg (sub_nonneg.mpr hqb), mul_zero, add_zero]
        have h1 := mul_nonneg hb hq
        have h2 := mul_nonneg hD (neg_nonneg.mpr hb0)
        nlinarith only [h1, h2, hw]
  · rcases le_total 0 b with hb0 | hb0
    · have hzero : t * q - b ≤ 0 := by nlinarith only [ht, hq, hb0]
      rw [form, relu_of_nonpos hq, relu_of_nonneg hb0, relu_of_nonpos hzero]
      have h1 := mul_nonneg hB hb0
      nlinarith only [h1, hw]
    · rw [form, relu_of_nonpos hq, relu_of_nonpos hb0]
      have h1 := mul_nonneg hD (relu_nonneg (t * q - b))
      nlinarith only [h1, hw]

lemma form_neg (t A B C D q b c : ℝ) :
    form t (-A) (-B) (-C) (-D) q b c = -form t A B C D q b c := by
  unfold form
  ring

/-- Five exact ray inequalities describe the full cone of nonnegative
feature-linear functions. -/
theorem form_nonneg_iff {t A B C D : ℝ} (ht : 0 < t) :
    (∀ q b c : ℝ, 0 ≤ form t A B C D q b c) ↔
      0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ C ∧ 0 ≤ A + t * B ∧ 0 ≤ A + t * D := by
  constructor
  · intro h
    exact ⟨by simpa only [form_v] using h 0 1 0,
      by simpa only [form_u] using h 0 (-1) 0,
      by simpa only [form_w] using h 0 0 1,
      by simpa only [form_a ht.le] using h 1 t 0,
      by simpa only [form_b ht.le] using h 1 0 0⟩
  · rintro ⟨hB, hD, hC, ha, hb⟩
    exact form_nonneg ht hB hD hC ha hb

lemma nonpos_of_sameSign_neg_right {a b : ℝ} (h : SameSign a b) (hb : b < 0) :
    a ≤ 0 := by
  rcases h with ⟨_, hbp⟩ | ⟨ha, _⟩
  · exact False.elim (not_le_of_gt hb hbp)
  · exact ha

lemma nonneg_of_sameSign_pos_right {a b : ℝ} (h : SameSign a b) (hb : 0 < b) :
    0 ≤ a := by
  rcases h with ⟨ha, _⟩ | ⟨_, hbn⟩
  · exact ha
  · exact False.elim (not_le_of_gt hb hbn)

/-- If clipping stays in the actual mixed dictionary span, the readout has a
single global sign. All parameters and all inputs are arbitrary real numbers. -/
theorem form_clipping_rigid {t A B C D E F G H : ℝ} (ht : 0 < t)
    (h : ∀ q b c : ℝ, relu (form t A B C D q b c) = form t E F G H q b c) :
    (∀ q b c : ℝ, 0 ≤ form t A B C D q b c) ∨
      (∀ q b c : ℝ, form t A B C D q b c ≤ 0) := by
  have hv : relu B = F := by simpa only [form_v] using h 0 1 0
  have hu : relu D = H := by simpa only [form_u] using h 0 (-1) 0
  have ha : relu (A + t * B) = E + t * F := by
    simpa only [form_a ht.le] using h 1 t 0
  have hb : relu (A + t * D) = E + t * H := by
    simpa only [form_b ht.le] using h 1 0 0
  have hw : relu C = G := by simpa only [form_w] using h 0 0 1
  have hva : SameSign B (A + t * B) := by
    apply sameSign_of_relu_add
    have hx := h 1 (t + 1) 0
    rw [form_av ht.le, form_av ht.le] at hx
    rw [add_comm B, hv, ha]
    linarith only [hx]
  have hab : SameSign (A + t * B) (A + t * D) := by
    apply sameSign_of_relu_add
    have hx := h 2 t 0
    rw [form_ab ht.le, form_ab ht.le] at hx
    rw [ha, hb]
    linarith only [hx]
  have hbu : SameSign (A + t * D) D := by
    apply sameSign_of_relu_add
    have hx := h 1 (-1) 0
    rw [form_bu ht.le, form_bu ht.le] at hx
    rw [hb, hu]
    linarith only [hx]
  have hlin : (A + t * B) + t * D = (A + t * D) + t * B := by ring
  have hclip : relu (A + t * B) + t * relu D =
      relu (A + t * D) + t * relu B := by rw [ha, hb, hv, hu]; ring
  have hall := four_ray_same_sign ht hva hab hbu hlin hclip
  have hcw : ∀ q b, SameSign (form t A B C D q b 0) C := by
    intro q b
    apply sameSign_of_relu_add
    have hx := h q b 1
    rw [form_add_w, form_add_w] at hx
    rw [h q b 0, hw]
    exact hx
  have hvw : SameSign B C := by simpa only [form_v] using hcw 0 1
  have huw : SameSign D C := by simpa only [form_u] using hcw 0 (-1)
  have haw : SameSign (A + t * B) C := by
    simpa only [form_a ht.le] using hcw 1 t
  have hbw : SameSign (A + t * D) C := by
    simpa only [form_b ht.le] using hcw 1 0
  rcases hall with ⟨hB, hA, hD', hD⟩ | ⟨hB, hA, hD', hD⟩
  · by_cases hC : 0 ≤ C
    · exact Or.inl (form_nonneg ht hB hD hC hA hD')
    · have hCn : C < 0 := lt_of_not_ge hC
      right
      intro q b c
      have he := form_nonneg (A := -A) ht
        (neg_nonneg.mpr (nonpos_of_sameSign_neg_right hvw hCn))
        (neg_nonneg.mpr (nonpos_of_sameSign_neg_right huw hCn))
        (neg_nonneg.mpr hCn.le)
        (by linarith only [nonpos_of_sameSign_neg_right haw hCn])
        (by linarith only [nonpos_of_sameSign_neg_right hbw hCn]) q b c
      rw [form_neg] at he
      linarith only [he]
  · by_cases hC : C ≤ 0
    · right
      intro q b c
      have he := form_nonneg (A := -A) ht (neg_nonneg.mpr hB) (neg_nonneg.mpr hD)
        (neg_nonneg.mpr hC) (by linarith only [hA]) (by linarith only [hD']) q b c
      rw [form_neg] at he
      linarith only [he]
    · have hCp : 0 < C := lt_of_not_ge hC
      exact Or.inl (form_nonneg ht
        (nonneg_of_sameSign_pos_right hvw hCp)
        (nonneg_of_sameSign_pos_right huw hCp) hCp.le
        (nonneg_of_sameSign_pos_right haw hCp)
        (nonneg_of_sameSign_pos_right hbw hCp))

/-- Exact classification of which feature readouts remain in the same span
after ReLU. In particular, the hypothesis in `form_clipping_rigid` is a
genuine functional condition, not a chosen normal-form definition. -/
theorem form_clipping_in_span_iff {t A B C D : ℝ} (ht : 0 < t) :
    (∃ E F G H : ℝ, ∀ q b c : ℝ,
      relu (form t A B C D q b c) = form t E F G H q b c) ↔
    (∀ q b c : ℝ, 0 ≤ form t A B C D q b c) ∨
      (∀ q b c : ℝ, form t A B C D q b c ≤ 0) := by
  constructor
  · rintro ⟨E, F, G, H, h⟩
    exact form_clipping_rigid ht h
  · rintro (h | h)
    · exact ⟨A, B, C, D, fun q b c => relu_of_nonneg (h q b c)⟩
    · refine ⟨0, 0, 0, 0, ?_⟩
      intro q b c
      rw [relu_of_nonpos (h q b c)]
      simp [form]

/-- The four actual feature functions have no coefficient dependence. -/
theorem form_eq_zero_iff {t A B C D : ℝ} (ht : 0 < t) :
    (∀ q b c : ℝ, form t A B C D q b c = 0) ↔
      A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  constructor
  · intro h
    have hB : B = 0 := by simpa only [form_v] using h 0 1 0
    have hD : D = 0 := by simpa only [form_u] using h 0 (-1) 0
    have hC : C = 0 := by simpa only [form_w] using h 0 0 1
    have hA : A = 0 := by simpa only [form_a ht.le, hB, mul_zero, add_zero] using h 1 t 0
    exact ⟨hA, hB, hC, hD⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩ q b c
    simp [form]

end MaxCaterpillar.Fiber.Mixed65
