import MaxCaterpillar.Fiber.Star65.Clipping
import MaxCaterpillar.Fiber.Star65.Independence
import MaxCaterpillar.Fiber.Mixed65.SignSpans

/-! # Full spans of star-to-path sign domains

A positive value at either middle ray of the actual three-cone feature image
forces its entire strict positive sign domain to span all four readout
coefficients. A negative independent-ray coefficient gives the analogous
negative-domain assertion. These criteria include all residual core directions.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Star
open MaxCaterpillar.Fiber.Star65

lemma form_a_plus_u {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A B C D : ℝ) :
    starLinearForm r A B C D (r * (1 + s)) (-s) 0 =
      (r * A + r * D) + s * (r * A) := by
  have hq : 0 ≤ r * (1 + s) := mul_nonneg hr (by linarith only [hs])
  have he : r * (1 + s) + r * (-s) = r := by ring
  simp only [starLinearForm, max_eq_right hq, max_eq_left (neg_nonpos.mpr hs),
    he, max_eq_right hr, max_self, mul_zero, add_zero]
  ring

lemma form_a_plus_v {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A B C D : ℝ) :
    starLinearForm r A B C D r s 0 =
      (r * A + r * D) + s * (B + r * D) := by
  have ht : 0 ≤ r + r * s := add_nonneg hr (mul_nonneg hr hs)
  simp only [starLinearForm, max_eq_right hr, max_eq_right hs,
    max_eq_right ht, max_eq_right (show 0 ≤ r + r * s by nlinarith only [hr, mul_nonneg hr hs]), max_self, mul_zero, add_zero]
  ring

lemma form_v_plus_a {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A B C D : ℝ) :
    starLinearForm r A B C D (r * s) 1 0 =
      (B + r * D) + s * (r * A + r * D) := by
  have hq : 0 ≤ r * s := mul_nonneg hr hs
  have ht : 0 ≤ r * s + r * 1 := add_nonneg hq (by simpa using hr)
  unfold starLinearForm
  rw [max_eq_right hq,max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    max_self,max_eq_right ht]
  ring

lemma form_v_plus_w {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (A B C D : ℝ) :
    starLinearForm r A B C D (-r * s) (1 + s) 0 =
      (B + r * D) + s * B := by
  have hq : -r * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) hs
  have hv : 0 ≤ 1 + s := by linarith only [hs]
  have he : -r * s + r * (1 + s) = r := by ring
  simp only [starLinearForm, max_eq_left hq, max_eq_right hv, he,
    max_eq_right hr, max_self, mul_zero, zero_add, add_zero]
  ring

lemma form_a_plus_independent {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (A B C D : ℝ) :
    starLinearForm r A B C D r 0 s = (r * A + r * D) + s * C := by
  simp only [starLinearForm, max_eq_right hr, max_eq_right hs,
    max_self, mul_zero, add_zero]
  ring

lemma form_v_plus_independent {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (A B C D : ℝ) :
    starLinearForm r A B C D 0 1 s = (B + r * D) + s * C := by
  simp only [starLinearForm, max_eq_right hr, max_eq_right hs,
    max_self, mul_zero, zero_add, mul_one]
  norm_num
  ring

/-- Positivity at the first middle ray suffices for the complete coefficient span. -/
theorem coefficients_zero_of_vanish_positive_a {r A B C D a b c d : ℝ}
    (hr : 0 < r) (hga : 0 < r * a + r * d)
    (H : ∀ q v w : ℝ, 0 < starLinearForm r a b c d q v w →
      starLinearForm r A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hu := Mixed65.affine_coefficients_zero_of_vanish_positive hga (by
    intro s hs hg
    have he := H (r * (1 + s)) (-s) 0 (by
      simpa only [form_a_plus_u hr.le hs] using hg)
    simpa only [form_a_plus_u hr.le hs] using he)
  have hv := Mixed65.affine_coefficients_zero_of_vanish_positive hga (by
    intro s hs hg
    have he := H r s 0 (by simpa only [form_a_plus_v hr.le hs] using hg)
    simpa only [form_a_plus_v hr.le hs] using he)
  have hw := Mixed65.affine_coefficients_zero_of_vanish_positive hga (by
    intro s hs hg
    have he := H r 0 s (by simpa only [form_a_plus_independent hr.le hs] using hg)
    simpa only [form_a_plus_independent hr.le hs] using he)
  have hA : A = 0 := (mul_eq_zero.mp hu.2).resolve_left (ne_of_gt hr)
  have hD : D = 0 := by
    have he : r * D = 0 := by simpa only [hA, mul_zero, zero_add] using hu.1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hr)
  have hB : B = 0 := by simpa only [hD, mul_zero, add_zero] using hv.2
  exact ⟨hA, hB, hw.2, hD⟩

/-- Positivity at the other middle ray gives the same conclusion. -/
theorem coefficients_zero_of_vanish_positive_v {r A B C D a b c d : ℝ}
    (hr : 0 < r) (hgv : 0 < b + r * d)
    (H : ∀ q v w : ℝ, 0 < starLinearForm r a b c d q v w →
      starLinearForm r A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have ha := Mixed65.affine_coefficients_zero_of_vanish_positive hgv (by
    intro s hs hg
    have he := H (r * s) 1 0 (by simpa only [form_v_plus_a hr.le hs] using hg)
    simpa only [form_v_plus_a hr.le hs] using he)
  have hw := Mixed65.affine_coefficients_zero_of_vanish_positive hgv (by
    intro s hs hg
    have he := H (-r * s) (1 + s) 0 (by
      simpa only [form_v_plus_w hr.le hs] using hg)
    simpa only [form_v_plus_w hr.le hs] using he)
  have hc := Mixed65.affine_coefficients_zero_of_vanish_positive hgv (by
    intro s hs hg
    have he := H 0 1 s (by simpa only [form_v_plus_independent hr.le hs] using hg)
    simpa only [form_v_plus_independent hr.le hs] using he)
  have hD : D = 0 := by
    have he : r * D = 0 := by simpa only [hw.2, zero_add] using hw.1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hr)
  have hA : A = 0 := by
    have he : r * A = 0 := by simpa only [hD, mul_zero, add_zero] using ha.2
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hr)
  exact ⟨hA, hw.2, hc.2, hD⟩

/-- A negative coefficient on the independent nonnegative ray gives complete
span of the strict negative sign domain, without any support restriction. -/
theorem coefficients_zero_of_vanish_negative_independent {r A B C D a b c d : ℝ}
    (hr : 0 < r) (hc : c < 0)
    (H : ∀ q v w : ℝ, starLinearForm r a b c d q v w < 0 →
      starLinearForm r A B C D q v w = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hC := H 0 0 1 (by simpa [starLinearForm] using hc)
  have hC0 : C = 0 := by simpa [starLinearForm] using hC
  apply features_independent hr
  intro q v w
  let z : ℝ := max 0 ((starLinearForm r a b c d q v 0 + 1) / (-c))
  have hz : 0 ≤ z := le_max_left _ _
  have hb : starLinearForm r a b c d q v 0 + 1 ≤ z * (-c) :=
    (div_le_iff (neg_pos.mpr hc)).mp (le_max_right _ _)
  have hg : starLinearForm r a b c d q v z < 0 := by
    change starLinearForm r a b c d q v z < 0
    have he : starLinearForm r a b c d q v z =
        starLinearForm r a b c d q v 0 + c * z := by
      unfold starLinearForm
      rw [max_eq_right hz,max_self]
      ring
    rw [he]
    nlinarith only [hb]
  have he := H q v z hg
  simpa only [starLinearForm, hC0, zero_mul, add_zero] using he

/-- Both strict sign domains span the full actual feature coefficient space. -/
def FullSignSpan (r : ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ A B C D : ℝ,
    ((∀ q v w : ℝ, 0 < g q v w → starLinearForm r A B C D q v w = 0) →
      A=0 ∧ B=0 ∧ C=0 ∧ D=0) ∧
    ((∀ q v w : ℝ, g q v w < 0 → starLinearForm r A B C D q v w = 0) →
      A=0 ∧ B=0 ∧ C=0 ∧ D=0)

lemma fullSignSpan_congr {r : ℝ} {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ q v w, f q v w = g q v w) : FullSignSpan r f ↔ FullSignSpan r g := by
  simp only [FullSignSpan]
  simp_rw [h]

theorem fullSignSpan_of_middle_a {r a b c d : ℝ} (hr : 0 < r)
    (ha : 0 < r*a+r*d) (hc : c < 0) :
    FullSignSpan r (starLinearForm r a b c d) := by
  intro A B C D
  exact ⟨coefficients_zero_of_vanish_positive_a hr ha,
    coefficients_zero_of_vanish_negative_independent hr hc⟩

theorem fullSignSpan_of_middle_v {r a b c d : ℝ} (hr : 0 < r)
    (hv : 0 < b+r*d) (hc : c < 0) :
    FullSignSpan r (starLinearForm r a b c d) := by
  intro A B C D
  exact ⟨coefficients_zero_of_vanish_positive_v hr hv,
    coefficients_zero_of_vanish_negative_independent hr hc⟩

/-- Every forced left carrier has full strict sign domains, even before
its free coefficient is restricted by the residual identity. -/
theorem left_core_fullSignSpan {r : ℝ} (hr : 0 < r) (h : ℝ) :
    FullSignSpan r (fun q v w => comparison r q v - max 0 w + h*max 0 v) := by
  have he : ∀ q v w : ℝ,
      comparison r q v-max 0 w+h*max 0 v =
        starLinearForm r ((r-1)/r) h (-1) (1/r) q v w := by
    intro q v w
    unfold comparison starLinearForm
    field_simp [ne_of_gt hr]
    ring
  apply (fullSignSpan_congr he).mpr
  apply fullSignSpan_of_middle_a hr ?_ (by norm_num)
  have hid : r*((r-1)/r)+r*(1/r)=r := by field_simp [ne_of_gt hr]; ring
  rwa [hid]

/-- The other forced positive carrier has the same property. -/
theorem right_core_fullSignSpan {r : ℝ} (hr : 0 < r) (k : ℝ) :
    FullSignSpan r (fun q v w => max 0 v-max 0 w+k*max 0 q) := by
  have he : ∀ q v w : ℝ,
      max 0 v-max 0 w+k*max 0 q = starLinearForm r k 1 (-1) 0 q v w := by
    intro q v w
    unfold starLinearForm
    ring
  apply (fullSignSpan_congr he).mpr
  apply fullSignSpan_of_middle_v hr <;> norm_num

/-- The first branch's negative core has full sign domains for every slack,
including the branch boundary. -/
theorem branchI_negative_fullSignSpan {r : ℝ} (hr : 0 < r) (k : ℝ) :
    FullSignSpan r (fun q v w =>
      comparison r q v-max 0 q-max 0 w+k*max 0 q) := by
  have he : ∀ q v w : ℝ,
      comparison r q v-max 0 q-max 0 w+k*max 0 q =
        starLinearForm r (k-1/r) 0 (-1) (1/r) q v w := by
    intro q v w
    unfold comparison starLinearForm
    field_simp [ne_of_gt hr]
    ring
  apply (fullSignSpan_congr he).mpr
  apply fullSignSpan_of_middle_v hr ?_ (by norm_num)
  have hid : (0 : ℝ)+r*(1/r)=1 := by field_simp [ne_of_gt hr]
  rw [hid]
  norm_num

/-- The second branch's negative core has the same full-span property. -/
theorem branchII_negative_fullSignSpan {r : ℝ} (hr : 0 < r) (h : ℝ) :
    FullSignSpan r (fun q v w => max 0 q+(1+h)*max 0 v-max 0 w) := by
  have he : ∀ q v w : ℝ,
      max 0 q+(1+h)*max 0 v-max 0 w = starLinearForm r 1 (1+h) (-1) 0 q v w := by
    intro q v w
    unfold starLinearForm
    ring
  apply (fullSignSpan_congr he).mpr
  apply fullSignSpan_of_middle_a hr ?_ (by norm_num)
  simpa using hr

/-- Both sign-domain conclusions are invariant under every nonzero scale,
so they apply to the original oriented physical cores. -/
theorem fullSignSpan_scale {r s : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hs : s ≠ 0) (hg : FullSignSpan r g) :
    FullSignSpan r (fun q v w => s*g q v w) := by
  intro A B C D
  rcases hg A B C D with ⟨hp,hn⟩
  rcases lt_or_gt_of_ne hs with hs | hs
  · refine ⟨?_,?_⟩
    · intro H
      apply hn
      intro q v w h
      exact H q v w (mul_pos_of_neg_of_neg hs h)
    · intro H
      apply hp
      intro q v w h
      exact H q v w (mul_neg_of_neg_of_pos hs h)
  · refine ⟨?_,?_⟩
    · intro H
      apply hp
      intro q v w h
      exact H q v w (mul_pos hs h)
    · intro H
      apply hn
      intro q v w h
      exact H q v w (mul_neg_of_pos_of_neg hs h)

end MaxCaterpillar.Fiber.Count65.Star
