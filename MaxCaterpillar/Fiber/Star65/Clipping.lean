import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Clipping in the four-feature star-to-path dictionary

This module proves a function-space property needed by the physical-lift
classification. It does not state a connected-component count.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

/-- A feature-linear function for the star-to-path first hidden layer. -/
noncomputable def starLinearForm (r a b c d q v w : ℝ) : ℝ :=
  a * max 0 q + b * max 0 v + c * max 0 w + d * max 0 (q + r * v)

/-- A linear positive part on a two-ray cone cannot clip opposite signs. -/
theorem mul_nonneg_of_clip_add {a b : ℝ}
    (h : max 0 (a + b) = max 0 a + max 0 b) : 0 ≤ a * b := by
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · exact mul_nonneg ha hb
    · rw [max_eq_right ha, max_eq_left hb] at h
      rcases le_total 0 (a + b) with hab | hab
      · rw [max_eq_right hab] at h
        have : b = 0 := by linarith
        simp [this]
      · rw [max_eq_left hab] at h
        have : a = 0 := by linarith
        simp [this]
  · rcases le_total 0 b with hb | hb
    · rw [max_eq_left ha, max_eq_right hb] at h
      rcases le_total 0 (a + b) with hab | hab
      · rw [max_eq_right hab] at h
        have : a = 0 := by linarith
        simp [this]
      · rw [max_eq_left hab] at h
        have : b = 0 := by linarith
        simp [this]
    · exact mul_nonneg_of_nonpos_of_nonpos ha hb

/-- The four consecutive feature rays, together with their linear relation,
force one common weak sign when clipping is feature-linear. -/
theorem four_ray_one_sign {u a v w : ℝ}
    (hua : 0 ≤ u * a) (hav : 0 ≤ a * v) (hvw : 0 ≤ v * w)
    (hrel : a + w = u + v)
    (hclip : max 0 a + max 0 w = max 0 u + max 0 v) :
    (0 ≤ u ∧ 0 ≤ a ∧ 0 ≤ v ∧ 0 ≤ w) ∨
      (u ≤ 0 ∧ a ≤ 0 ∧ v ≤ 0 ∧ w ≤ 0) := by
  rcases lt_trichotomy 0 a with ha | ha | ha
  · have hu : 0 ≤ u := by nlinarith only [hua, ha]
    have hv : 0 ≤ v := by nlinarith only [hav, ha]
    rw [max_eq_right ha.le, max_eq_right hu, max_eq_right hv] at hclip
    have hw : 0 ≤ w := by
      have := le_max_left (0 : ℝ) w
      linarith only [this, hclip, hrel]
    exact Or.inl ⟨hu, ha.le, hv, hw⟩
  · have ha0 : a = 0 := ha.symm
    subst a
    rcases lt_trichotomy 0 v with hv | hv | hv
    · have hw : 0 ≤ w := by nlinarith only [hvw, hv]
      rw [max_self, max_eq_right hw, max_eq_right hv.le] at hclip
      have hu : 0 ≤ u := by
        have := le_max_left (0 : ℝ) u
        linarith only [this, hclip, hrel]
      exact Or.inl ⟨hu, le_rfl, hv.le, hw⟩
    · have hv0 : v = 0 := hv.symm
      subst v
      rcases le_total 0 u with hu | hu
      · exact Or.inl ⟨hu, le_rfl, le_rfl, by linarith only [hrel, hu]⟩
      · exact Or.inr ⟨hu, le_rfl, le_rfl, by linarith only [hrel, hu]⟩
    · have hw : w ≤ 0 := by nlinarith only [hvw, hv]
      rw [max_self, max_eq_left hw, max_eq_left hv.le] at hclip
      have hu : u ≤ 0 := by
        have := le_max_right (0 : ℝ) u
        linarith only [this, hclip]
      exact Or.inr ⟨hu, le_rfl, hv.le, hw⟩
  · have hu : u ≤ 0 := by nlinarith only [hua, ha]
    have hv : v ≤ 0 := by nlinarith only [hav, ha]
    rw [max_eq_left ha.le, max_eq_left hu, max_eq_left hv] at hclip
    have hw : w ≤ 0 := by
      have := le_max_right (0 : ℝ) w
      linarith only [this, hclip]
    exact Or.inr ⟨hu, ha.le, hv, hw⟩

/-- The independent nonnegative feature ray has the same weak sign as the
four-ray chain, unless all four chain values vanish. -/
theorem five_ray_one_sign {u a v w z : ℝ}
    (hua : 0 ≤ u * a) (hav : 0 ≤ a * v) (hvw : 0 ≤ v * w)
    (hrel : a + w = u + v)
    (hclip : max 0 a + max 0 w = max 0 u + max 0 v)
    (huz : 0 ≤ u * z) (haz : 0 ≤ a * z)
    (hvz : 0 ≤ v * z) (hwz : 0 ≤ w * z) :
    (0 ≤ u ∧ 0 ≤ a ∧ 0 ≤ v ∧ 0 ≤ w ∧ 0 ≤ z) ∨
      (u ≤ 0 ∧ a ≤ 0 ∧ v ≤ 0 ∧ w ≤ 0 ∧ z ≤ 0) := by
  rcases lt_trichotomy 0 z with hz | hz | hz
  · exact Or.inl ⟨by nlinarith only [huz, hz], by nlinarith only [haz, hz],
      by nlinarith only [hvz, hz], by nlinarith only [hwz, hz], hz.le⟩
  · have hz0 : z = 0 := hz.symm
    subst z
    rcases four_ray_one_sign hua hav hvw hrel hclip with h | h
    · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, le_rfl⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, le_rfl⟩
  · exact Or.inr ⟨by nlinarith only [huz, hz], by nlinarith only [haz, hz],
      by nlinarith only [hvz, hz], by nlinarith only [hwz, hz], hz.le⟩

/-- The five ray inequalities suffice for nonnegativity on every input. -/
theorem starLinearForm_nonneg {r a b c d : ℝ} (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (had : 0 ≤ a + d) (hbd : 0 ≤ b + r * d) (q v w : ℝ) :
    0 ≤ starLinearForm r a b c d q v w := by
  have hq := le_max_left (0 : ℝ) q
  have hv := le_max_left (0 : ℝ) v
  have hw := le_max_left (0 : ℝ) w
  have ht := le_max_left (0 : ℝ) (q + r * v)
  unfold starLinearForm
  rcases le_total 0 d with hd | hd
  · exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg ha hq)
      (mul_nonneg hb hv)) (mul_nonneg hc hw)) (mul_nonneg hd ht)
  · have hsub : max 0 (q + r * v) ≤ max 0 q + r * max 0 v := by
      apply max_le
      · exact add_nonneg hq (mul_nonneg hr hv)
      · have hqr := le_max_right (0 : ℝ) q
        have hvr := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) v) hr
        linarith only [hqr, hvr]
    have hmul := mul_le_mul_of_nonpos_left hsub hd
    have h1 := mul_nonneg had hq
    have h2 := mul_nonneg hbd hv
    have h3 := mul_nonneg hc hw
    nlinarith only [hmul, h1, h2, h3]

private theorem starLinearForm_u {r : ℝ} (hr : 0 ≤ r) (a b c d z : ℝ) :
    starLinearForm r a b c d r (-1) z = r * a + c * max 0 z := by
  simp [starLinearForm, max_eq_right hr]
  ring

private theorem starLinearForm_a {r : ℝ} (hr : 0 ≤ r) (a b c d z : ℝ) :
    starLinearForm r a b c d r 0 z = r * a + r * d + c * max 0 z := by
  simp [starLinearForm, max_eq_right hr]
  ring

private theorem starLinearForm_v {r : ℝ} (hr : 0 ≤ r) (a b c d z : ℝ) :
    starLinearForm r a b c d 0 1 z = b + r * d + c * max 0 z := by
  simp [starLinearForm, max_eq_right hr]
  ring

private theorem starLinearForm_w {r : ℝ} (hr : 0 ≤ r) (a b c d z : ℝ) :
    starLinearForm r a b c d (-r) 1 z = b + c * max 0 z := by
  have hn : -r ≤ 0 := neg_nonpos.mpr hr
  simp [starLinearForm, max_eq_left hn]

private theorem starLinearForm_z (r a b c d : ℝ) :
    starLinearForm r a b c d 0 0 1 = c := by
  simp [starLinearForm]

private theorem starLinearForm_ua {r : ℝ} (hr : 0 ≤ r) (a b c d : ℝ) :
    starLinearForm r a b c d (2 * r) (-1) 0 =
      r * a + (r * a + r * d) := by
  have hr2 : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr
  have he : 2 * r + r * (-1) = r := by ring
  simp [starLinearForm, he, max_eq_right hr, max_eq_right hr2]
  rw [show 2 * r + -r = r by ring, max_eq_right hr]
  ring

private theorem starLinearForm_av {r : ℝ} (hr : 0 ≤ r) (a b c d : ℝ) :
    starLinearForm r a b c d r 1 0 =
      (r * a + r * d) + (b + r * d) := by
  have hr2 : 0 ≤ r + r := add_nonneg hr hr
  simp [starLinearForm, max_eq_right hr, max_eq_right hr2]
  ring

private theorem starLinearForm_vw {r : ℝ} (hr : 0 ≤ r) (a b c d : ℝ) :
    starLinearForm r a b c d (-r) 2 0 = (b + r * d) + b := by
  have hn : -r ≤ 0 := neg_nonpos.mpr hr
  have he : -r + r * 2 = r := by ring
  simp [starLinearForm, he, max_eq_left hn, max_eq_right hr]
  norm_num
  ring

/-- **Strong clipping lemma.** If the positive part of a feature-linear
function is again feature-linear in the star-to-path dictionary, then the
original function has one global weak sign. All coefficients are arbitrary
real numbers, and every input is quantified. -/
theorem starLinearForm_clipping {r a b c d A B C D : ℝ} (hr : 0 < r)
    (h : ∀ q v w : ℝ, max 0 (starLinearForm r a b c d q v w) =
      starLinearForm r A B C D q v w) :
    (∀ q v w : ℝ, 0 ≤ starLinearForm r a b c d q v w) ∨
      (∀ q v w : ℝ, starLinearForm r a b c d q v w ≤ 0) := by
  have hu : max 0 (r * a) = r * A := by
    simpa only [starLinearForm_u hr.le, max_self, mul_zero, add_zero] using h r (-1) 0
  have ha : max 0 (r * a + r * d) = r * A + r * D := by
    simpa only [starLinearForm_a hr.le, max_self, mul_zero, add_zero] using h r 0 0
  have hv : max 0 (b + r * d) = B + r * D := by
    simpa only [starLinearForm_v hr.le, max_self, mul_zero, add_zero] using h 0 1 0
  have hw : max 0 b = B := by
    simpa only [starLinearForm_w hr.le, max_self, mul_zero, add_zero] using h (-r) 1 0
  have hz : max 0 c = C := by
    simpa only [starLinearForm_z] using h 0 0 1
  have hua : 0 ≤ (r * a) * (r * a + r * d) := by
    apply mul_nonneg_of_clip_add
    rw [hu, ha]
    simpa only [starLinearForm_ua hr.le] using h (2 * r) (-1) 0
  have hav : 0 ≤ (r * a + r * d) * (b + r * d) := by
    apply mul_nonneg_of_clip_add
    rw [ha, hv]
    simpa only [starLinearForm_av hr.le] using h r 1 0
  have hvw : 0 ≤ (b + r * d) * b := by
    apply mul_nonneg_of_clip_add
    rw [hv, hw]
    simpa only [starLinearForm_vw hr.le] using h (-r) 2 0
  have hrel : (r * a + r * d) + b = r * a + (b + r * d) := by ring
  have hclip : max 0 (r * a + r * d) + max 0 b =
      max 0 (r * a) + max 0 (b + r * d) := by rw [ha, hw, hu, hv]; ring
  have huz : 0 ≤ (r * a) * c := by
    apply mul_nonneg_of_clip_add
    rw [hu, hz]
    simpa only [starLinearForm_u hr.le, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      mul_one] using h r (-1) 1
  have haz : 0 ≤ (r * a + r * d) * c := by
    apply mul_nonneg_of_clip_add
    rw [ha, hz]
    simpa only [starLinearForm_a hr.le, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      mul_one] using h r 0 1
  have hvz : 0 ≤ (b + r * d) * c := by
    apply mul_nonneg_of_clip_add
    rw [hv, hz]
    simpa only [starLinearForm_v hr.le, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      mul_one] using h 0 1 1
  have hwz : 0 ≤ b * c := by
    apply mul_nonneg_of_clip_add
    rw [hw, hz]
    simpa only [starLinearForm_w hr.le, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      mul_one] using h (-r) 1 1
  rcases five_ray_one_sign hua hav hvw hrel hclip huz haz hvz hwz with hs | hs
  · have h0a : 0 ≤ a := by nlinarith only [hr, hs.1]
    have h0ad : 0 ≤ a + d := by nlinarith only [hr, hs.2.1]
    exact Or.inl (starLinearForm_nonneg hr.le h0a hs.2.2.2.1 hs.2.2.2.2 h0ad hs.2.2.1)
  · have h0a : 0 ≤ -a := by nlinarith only [hr, hs.1]
    have h0b : 0 ≤ -b := by linarith only [hs.2.2.2.1]
    have h0c : 0 ≤ -c := by linarith only [hs.2.2.2.2]
    have h0ad : 0 ≤ -a + -d := by nlinarith only [hr, hs.2.1]
    have h0bd : 0 ≤ -b + r * -d := by nlinarith only [hs.2.2.1]
    right
    intro q v w
    have hn := starLinearForm_nonneg hr.le h0a h0b h0c h0ad h0bd q v w
    unfold starLinearForm at hn ⊢
    nlinarith only [hn]

/-- Exact coefficient description of the cone of nonnegative feature-linear
functions, without sampling or strict-sign exclusions. -/
theorem starLinearForm_nonneg_iff {r a b c d : ℝ} (hr : 0 < r) :
    (∀ q v w : ℝ, 0 ≤ starLinearForm r a b c d q v w) ↔
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ a + d ∧ 0 ≤ b + r * d := by
  constructor
  · intro h
    have hu : 0 ≤ r * a := by
      simpa only [starLinearForm_u hr.le, max_self, mul_zero, add_zero] using h r (-1) 0
    have ha : 0 ≤ r * a + r * d := by
      simpa only [starLinearForm_a hr.le, max_self, mul_zero, add_zero] using h r 0 0
    have hv : 0 ≤ b + r * d := by
      simpa only [starLinearForm_v hr.le, max_self, mul_zero, add_zero] using h 0 1 0
    have hw : 0 ≤ b := by
      simpa only [starLinearForm_w hr.le, max_self, mul_zero, add_zero] using h (-r) 1 0
    have hz : 0 ≤ c := by simpa only [starLinearForm_z] using h 0 0 1
    exact ⟨by nlinarith only [hr, hu], hw, hz, by nlinarith only [hr, ha], hv⟩
  · rintro ⟨ha, hb, hc, had, hbd⟩
    exact starLinearForm_nonneg hr.le ha hb hc had hbd

/-- The four feature functions are linearly independent at every positive
parameter, including the star endpoint. -/
theorem starLinearForm_coefficients {r a b c d A B C D : ℝ} (hr : 0 < r)
    (h : ∀ q v w : ℝ, starLinearForm r a b c d q v w =
      starLinearForm r A B C D q v w) : a = A ∧ b = B ∧ c = C ∧ d = D := by
  have hu : r * a = r * A := by
    simpa only [starLinearForm_u hr.le, max_self, mul_zero, add_zero] using h r (-1) 0
  have hv : b + r * d = B + r * D := by
    simpa only [starLinearForm_v hr.le, max_self, mul_zero, add_zero] using h 0 1 0
  have hw : b = B := by
    simpa only [starLinearForm_w hr.le, max_self, mul_zero, add_zero] using h (-r) 1 0
  have hz : c = C := by simpa only [starLinearForm_z] using h 0 0 1
  exact ⟨by nlinarith only [hr, hu], hw, hz, by nlinarith only [hr, hv, hw]⟩

/-- Feature-linearity of clipping is equivalent to the original function
having one global weak sign. -/
theorem starLinearForm_clipping_iff {r a b c d : ℝ} (hr : 0 < r) :
    (∃ A B C D : ℝ, ∀ q v w : ℝ,
      max 0 (starLinearForm r a b c d q v w) = starLinearForm r A B C D q v w) ↔
      (∀ q v w : ℝ, 0 ≤ starLinearForm r a b c d q v w) ∨
        (∀ q v w : ℝ, starLinearForm r a b c d q v w ≤ 0) := by
  constructor
  · rintro ⟨A, B, C, D, h⟩
    exact starLinearForm_clipping hr h
  · rintro (h | h)
    · exact ⟨a, b, c, d, fun q v w => max_eq_right (h q v w)⟩
    · refine ⟨0, 0, 0, 0, ?_⟩
      intro q v w
      rw [max_eq_left (h q v w)]
      simp [starLinearForm]

end MaxCaterpillar.Fiber.Star65
