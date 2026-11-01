import MaxCaterpillar.Frontier.Basic

/-! # Exact two-head reconstruction identities

These are identities for the two physical neurons carrying a signed translation
coordinate. They establish the signed, split, and hybrid constructions, including
inactive-side coefficient freedom, and prove their exhaustion over any
clipping-rigid invariant function space. Extracting two such heads from an
arbitrary five-neuron network remains a separate theorem.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

/-- Two second-hidden-layer neurons with normalized output coefficients `+1,-1`.
The first-layer inputs carrying the translation are `relu z` and `relu (-z)`.
The functions `A,B` are the invariant parts of the two preactivations. -/
structure Heads (α : Type*) where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  A : α → ℝ
  B : α → ℝ

noncomputable def Heads.eval {α : Type*} (h : Heads α) (x : α) (z : ℝ) : ℝ :=
  relu (h.a * relu z + h.b * relu (-z) + h.A x) -
    relu (h.c * relu z + h.d * relu (-z) + h.B x)

/-- Exact reconstruction on every invariant state and every translation. -/
def Heads.Reconstructs {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  ∀ x z, h.eval x z = z + L x

/-- Signed reconstruction, including coefficients invisible on an inactive half-line. -/
def Heads.IsSigned {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  h.A = L ∧ h.B = (fun x => -L x) ∧ h.a = 1 ∧ h.d = 1 ∧
    h.b ≤ 0 ∧ h.c ≤ 0 ∧
    ((∃ x, 0 < L x) → h.b = -1) ∧ ((∃ x, L x < 0) → h.c = -1)

/-- Both invariant intercepts and both cross coefficients are nonnegative. -/
def Heads.IsSplit {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  h.a = 1 + h.c ∧ h.d = 1 + h.b ∧ 0 ≤ h.b ∧ 0 ≤ h.c ∧
    (∀ x, 0 ≤ h.A x) ∧ (∀ x, 0 ≤ h.B x) ∧ (∀ x, h.A x - h.B x = L x)

/-- Hybrid face when the reconstructed invariant remainder is nonnegative. -/
def Heads.IsPositiveHybrid {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  h.A = L ∧ h.B = 0 ∧ h.a = 1 ∧ h.d = 1 + h.b ∧
    0 ≤ h.b ∧ h.c ≤ 0 ∧ ∀ x, 0 ≤ L x

/-- Hybrid face when the reconstructed invariant remainder is nonpositive. -/
def Heads.IsNegativeHybrid {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  h.A = 0 ∧ h.B = (fun x => -L x) ∧ h.a = 1 + h.c ∧ h.d = 1 ∧
    h.b ≤ 0 ∧ 0 ≤ h.c ∧ ∀ x, L x ≤ 0

/-- The split family together with its two possible inactive-side attachments. -/
def Heads.IsSplitHybrid {α : Type*} (h : Heads α) (L : α → ℝ) : Prop :=
  h.IsSplit L ∨ h.IsPositiveHybrid L ∨ h.IsNegativeHybrid L

lemma signed_scalar (z L b c : ℝ) (hb : b ≤ 0) (hc : c ≤ 0)
    (hbp : 0 < L → b = -1) (hcn : L < 0 → c = -1) :
    relu (relu z + b * relu (-z) + L) -
      relu (c * relu z + relu (-z) - L) = z + L := by
  rcases le_total 0 z with hz | hz
  · rw [relu_of_nonneg hz, relu_of_nonpos (neg_nonpos.mpr hz)]
    simp only [mul_zero, add_zero]
    rcases le_or_gt 0 L with hL | hL
    · rw [relu_of_nonneg (by linarith),
        relu_of_nonpos (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hz])]
      ring
    · rw [hcn hL]
      have heq : -1 * z - L = -(z + L) := by ring
      rw [heq, relu_sub_relu_neg]
  · rw [relu_of_nonpos hz, relu_of_nonneg (neg_nonneg.mpr hz)]
    simp only [mul_zero, zero_add]
    rcases le_or_gt L 0 with hL | hL
    · rw [relu_of_nonpos (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hb (neg_nonneg.mpr hz)]),
        relu_of_nonneg (by linarith)]
      ring
    · rw [hbp hL]
      have heq : -1 * -z + L = z + L := by ring
      have heq' : -z - L = -(z + L) := by ring
      rw [heq, heq', relu_sub_relu_neg]

lemma Heads.IsSigned.reconstructs {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSigned L) : h.Reconstructs L := by
  rcases hh with ⟨hA, hB, ha, hd, hb, hc, hbp, hcn⟩
  intro x z
  simp only [Heads.eval, hA, hB, ha, hd, one_mul]
  exact signed_scalar z (L x) h.b h.c hb hc
    (fun hx => hbp ⟨x, hx⟩) (fun hx => hcn ⟨x, hx⟩)

lemma Heads.IsSplit.reconstructs {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplit L) : h.Reconstructs L := by
  rcases hh with ⟨ha, hd, hb, hc, hA, hB, hL⟩
  intro x z
  have hp := relu_nonneg z
  have hn := relu_nonneg (-z)
  have hfirst : 0 ≤ (1 + h.c) * relu z + h.b * relu (-z) + h.A x := by
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hp) (mul_nonneg hb hn)) (hA x)
  have hsecond : 0 ≤ h.c * relu z + (1 + h.b) * relu (-z) + h.B x := by
    exact add_nonneg (add_nonneg (mul_nonneg hc hp) (mul_nonneg (by linarith) hn)) (hB x)
  rw [Heads.eval, ha, hd, relu_of_nonneg hfirst, relu_of_nonneg hsecond]
  have hz := relu_sub_relu_neg z
  linarith [hL x]

lemma Heads.IsPositiveHybrid.reconstructs {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsPositiveHybrid L) : h.Reconstructs L := by
  rcases hh with ⟨hA, hB, ha, hd, hb, hc, hL⟩
  intro x z
  simp only [Heads.eval, hA, hB, ha, hd, one_mul, Pi.zero_apply, add_zero]
  rcases le_total 0 z with hz | hz
  · rw [relu_of_nonneg hz, relu_of_nonpos (neg_nonpos.mpr hz)]
    simp only [mul_zero, add_zero]
    rw [relu_of_nonneg (add_nonneg hz (hL x)),
      relu_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc hz)]
    ring
  · rw [relu_of_nonpos hz, relu_of_nonneg (neg_nonneg.mpr hz)]
    simp only [mul_zero, zero_add]
    rw [relu_of_nonneg (add_nonneg (mul_nonneg hb (neg_nonneg.mpr hz)) (hL x)),
      relu_of_nonneg (mul_nonneg (by linarith) (neg_nonneg.mpr hz))]
    ring

lemma Heads.IsNegativeHybrid.reconstructs {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsNegativeHybrid L) : h.Reconstructs L := by
  rcases hh with ⟨hA, hB, ha, hd, hb, hc, hL⟩
  intro x z
  simp only [Heads.eval, hA, hB, ha, hd, one_mul, Pi.zero_apply, add_zero]
  rcases le_total 0 z with hz | hz
  · rw [relu_of_nonneg hz, relu_of_nonpos (neg_nonpos.mpr hz)]
    simp only [mul_zero, add_zero]
    rw [relu_of_nonneg (mul_nonneg (by linarith) hz),
      relu_of_nonneg (add_nonneg (mul_nonneg hc hz) (neg_nonneg.mpr (hL x)))]
    ring
  · rw [relu_of_nonpos hz, relu_of_nonneg (neg_nonneg.mpr hz)]
    simp only [mul_zero, zero_add]
    rw [relu_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hb (neg_nonneg.mpr hz)),
      relu_of_nonneg (add_nonneg (neg_nonneg.mpr hz) (neg_nonneg.mpr (hL x)))]
    ring

lemma Heads.IsSplitHybrid.reconstructs {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) : h.Reconstructs L := by
  rcases hh with hh | hh | hh
  · exact hh.reconstructs
  · exact hh.reconstructs
  · exact hh.reconstructs

lemma Heads.IsSplitHybrid.intercepts_nonneg {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) : (∀ x, 0 ≤ h.A x) ∧ (∀ x, 0 ≤ h.B x) := by
  rcases hh with hh | hh | hh
  · exact ⟨hh.2.2.2.2.1, hh.2.2.2.2.2.1⟩
  · rcases hh with ⟨hA, hB, _ha, _hd, _hb, _hc, hL⟩
    simpa only [hA, hB, Pi.zero_apply] using And.intro hL (fun _ : α => le_refl (0 : ℝ))
  · rcases hh with ⟨hA, hB, _ha, _hd, _hb, _hc, hL⟩
    simp only [hA, hB, Pi.zero_apply]
    exact ⟨fun _ => le_refl _, fun x => neg_nonneg.mpr (hL x)⟩

/-- Nonzero remainders prevent an intersection of the two declared reconstruction types. -/
lemma Heads.signed_not_splitHybrid {α : Type*} {h : Heads α} {L : α → ℝ}
    (hL : ∃ x, L x ≠ 0) (hs : h.IsSigned L) : ¬ h.IsSplitHybrid L := by
  intro ht
  obtain ⟨x, hx⟩ := hL
  obtain ⟨hA, hB⟩ := ht.intercepts_nonneg
  have hp : 0 ≤ L x := by simpa only [hs.1] using hA x
  have hn : 0 ≤ -L x := by simpa only [hs.2.1] using hB x
  exact hx (by linarith)

/-- The eventual constant term of a ReLU applied to an affine function on a ray. -/
noncomputable def affineTail (a A : ℝ) : ℝ :=
  if 0 < a then A else if a = 0 then relu A else 0

lemma eventually_relu_affine (a A : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ p, P ≤ p →
      relu (a * p + A) = relu a * p + affineTail a A := by
  by_cases ha : 0 < a
  · refine ⟨max 0 ((1 - A) / a), le_max_left _ _, ?_⟩
    intro p hp
    have hbound : 1 - A ≤ p * a :=
      (div_le_iff ha).mp ((le_max_right _ _).trans hp)
    rw [relu_of_nonneg (by nlinarith), relu_of_nonneg ha.le]
    simp only [affineTail, if_pos ha]
  · by_cases haz : a = 0
    · refine ⟨0, le_refl _, ?_⟩
      intro p _hp
      simp [haz, affineTail, relu]
    · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) haz
      refine ⟨max 0 ((A + 1) / (-a)), le_max_left _ _, ?_⟩
      intro p hp
      have hbound : A + 1 ≤ p * (-a) :=
        (div_le_iff (neg_pos.mpr han)).mp ((le_max_right _ _).trans hp)
      rw [relu_of_nonpos (by nlinarith), relu_of_nonpos han.le]
      simp only [affineTail, if_neg ha, if_neg haz, zero_mul, add_zero]

/-- Equality on the entire nonnegative ray identifies both eventual affine coefficients. -/
lemma halfLine_slopes (a A c B L : ℝ)
    (h : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu (c * p + B) = p + L) :
    relu a - relu c = 1 ∧ affineTail a A - affineTail c B = L := by
  obtain ⟨P, hP, hpa⟩ := eventually_relu_affine a A
  obtain ⟨Q, _hQ, hpc⟩ := eventually_relu_affine c B
  let s := max P Q
  have hs : 0 ≤ s := hP.trans (le_max_left _ _)
  have hPs : P ≤ s := le_max_left _ _
  have hQs : Q ≤ s := le_max_right _ _
  have h0 := h s hs
  have h1 := h (s + 1) (by linarith)
  rw [hpa s hPs, hpc s hQs] at h0
  rw [hpa (s + 1) (by linarith), hpc (s + 1) (by linarith)] at h1
  have hsl : relu a - relu c = 1 := by nlinarith only [h0, h1]
  constructor
  · exact hsl
  · have hmul := congrArg (fun v : ℝ => v * s) hsl
    dsimp only at hmul
    nlinarith only [h0, hmul]

lemma halfLine_first_slope_pos (a A c B L : ℝ)
    (h : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu (c * p + B) = p + L) :
    0 < a := by
  have hs := (halfLine_slopes a A c B L h).1
  by_contra hn
  rw [relu_of_nonpos (le_of_not_gt hn)] at hs
  linarith [relu_nonneg c]

lemma halfLine_positive_second (a A c B L : ℝ) (hc : 0 < c)
    (h : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu (c * p + B) = p + L) :
    a = 1 + c ∧ A - B = L ∧ 0 ≤ A ∧ 0 ≤ B := by
  have ha := halfLine_first_slope_pos a A c B L h
  obtain ⟨hsl, hi⟩ := halfLine_slopes a A c B L h
  rw [relu_of_nonneg ha.le, relu_of_nonneg hc.le] at hsl
  simp only [affineTail, if_pos ha, if_pos hc] at hi
  have hzero := h 0 (le_refl _)
  simp only [mul_zero, zero_add] at hzero
  have hA : 0 ≤ A := by
    by_contra hAn
    have hAn : A < 0 := lt_of_not_ge hAn
    rw [relu_of_nonpos hAn.le] at hzero
    have hBn : B < 0 := by
      by_contra hBn
      rw [relu_of_nonneg (le_of_not_gt hBn)] at hzero
      linarith
    rw [relu_of_nonpos hBn.le] at hzero
    have hAB : A = B := by linarith
    let p := -A / (2 * a)
    have hp : 0 < p := div_pos (neg_pos.mpr hAn) (mul_pos (by norm_num) ha)
    have hpA : p * (2 * a) = -A := div_mul_cancel _ (ne_of_gt (mul_pos (by norm_num) ha))
    have hca : c < a := by linarith
    have hcap := mul_pos (sub_pos.mpr hca) hp
    have hx := h p hp.le
    rw [relu_of_nonpos (by nlinarith only [hpA, hAn]),
      relu_of_nonpos (by nlinarith only [hpA, hAn, hAB, hcap])] at hx
    linarith
  rw [relu_of_nonneg hA] at hzero
  have hB : 0 ≤ B := by
    have hBEq : relu B = B := by linarith
    rw [← hBEq]
    exact relu_nonneg B
  exact ⟨by linarith, hi, hA, hB⟩

lemma halfLine_zero_second (a A B L : ℝ)
    (h : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu B = p + L) :
    a = 1 ∧ A = L + relu B ∧ 0 ≤ A := by
  have h' : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu (0 * p + B) = p + L := by
    simpa only [zero_mul, zero_add] using h
  have ha := halfLine_first_slope_pos a A 0 B L h'
  obtain ⟨hsl, hi⟩ := halfLine_slopes a A 0 B L h'
  rw [relu_of_nonneg ha.le, relu_of_nonpos (le_refl (0 : ℝ)), sub_zero] at hsl
  simp only [affineTail, if_pos ha, if_neg (lt_irrefl (0 : ℝ)), if_pos rfl, if_true] at hi
  have hzero := h 0 (le_refl _)
  simp only [mul_zero, zero_add] at hzero
  have hAEq : relu A = A := by linarith
  exact ⟨hsl, by linarith, hAEq ▸ relu_nonneg A⟩

lemma halfLine_negative_second (a A c B L : ℝ) (hc : c < 0)
    (h : ∀ p : ℝ, 0 ≤ p → relu (a * p + A) - relu (c * p + B) = p + L) :
    a = 1 ∧ A = L ∧
      ((0 ≤ L ∧ B ≤ 0) ∨ (L < 0 ∧ B = -L ∧ c = -1)) := by
  have ha := halfLine_first_slope_pos a A c B L h
  obtain ⟨hsl, hi⟩ := halfLine_slopes a A c B L h
  rw [relu_of_nonneg ha.le, relu_of_nonpos hc.le] at hsl
  simp only [sub_zero] at hsl
  simp only [affineTail, if_pos ha, if_neg (not_lt_of_ge hc.le),
    if_neg hc.ne, sub_zero] at hi
  have hzero := h 0 (le_refl _)
  simp only [mul_zero, zero_add] at hzero
  rw [hi] at hzero
  refine ⟨hsl, hi, ?_⟩
  rcases le_or_gt 0 L with hL | hL
  · left
    refine ⟨hL, ?_⟩
    rw [relu_of_nonneg hL] at hzero
    by_contra hn
    rw [relu_of_nonneg (le_of_lt (lt_of_not_ge hn))] at hzero
    linarith
  · right
    rw [relu_of_nonpos hL.le] at hzero
    have hB : 0 < B := by
      by_contra hn
      rw [relu_of_nonpos (le_of_not_gt hn)] at hzero
      linarith
    rw [relu_of_nonneg hB.le] at hzero
    have hBL : B = -L := by linarith
    refine ⟨hL, hBL, ?_⟩
    let p := -L / 2
    have hp : 0 < p := by dsimp [p]; linarith
    have hpL : p + L < 0 := by dsimp [p]; linarith
    have hx := h p hp.le
    rw [hsl, hi, one_mul, relu_of_nonpos hpL.le] at hx
    have hcp : 0 < c * p + B := by
      by_contra hn
      rw [relu_of_nonpos (le_of_not_gt hn)] at hx
      linarith
    rw [relu_of_nonneg hcp.le] at hx
    have hprod : (c + 1) * p = 0 := by nlinarith only [hx, hBL]
    rcases mul_eq_zero.mp hprod with hz | hz
    · linarith
    · exact (ne_of_gt hp hz).elim

lemma Heads.Reconstructs.positive_halfLine {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.Reconstructs L) (x : α) :
    ∀ p : ℝ, 0 ≤ p → relu (h.a * p + h.A x) - relu (h.c * p + h.B x) = p + L x := by
  intro p hp
  have hx := hh x p
  simpa only [Heads.eval, relu_of_nonneg hp, relu_of_nonpos (neg_nonpos.mpr hp),
    mul_zero, add_zero] using hx

lemma Heads.Reconstructs.negative_halfLine {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.Reconstructs L) (x : α) :
    ∀ p : ℝ, 0 ≤ p → relu (h.d * p + h.B x) - relu (h.b * p + h.A x) = p + (-L x) := by
  intro p hp
  have hx := hh x (-p)
  simp only [Heads.eval, relu_of_nonpos (neg_nonpos.mpr hp), neg_neg,
    relu_of_nonneg hp, mul_zero, zero_add] at hx
  linarith

/-- A function space has clipping rigidity when clipping cannot preserve membership
unless the original function has a single global sign. -/
def ClippingRigid {α : Type*} (E : Submodule ℝ (α → ℝ)) : Prop :=
  ∀ C ∈ E, (fun x => relu (C x)) ∈ E →
    (∀ x, 0 ≤ C x) ∨ (∀ x, C x ≤ 0)

/-- Complete two-head classification over any clipping-rigid invariant function space.
The nonempty state domain is necessary: an empty domain imposes no constraints on slopes. -/
theorem Heads.reconstructs_iff_signed_or_splitHybrid {α : Type*} [Nonempty α]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (h : Heads α) (L : α → ℝ)
    (hAm : h.A ∈ E) (hBm : h.B ∈ E) (hLm : L ∈ E) :
    h.Reconstructs L ↔ h.IsSigned L ∨ h.IsSplitHybrid L := by
  constructor
  · intro hh
    classical
    let x₀ : α := Classical.choice inferInstance
    have hp := hh.positive_halfLine
    have hn := hh.negative_halfLine
    rcases lt_trichotomy h.c 0 with hc | hc | hc
    · have pc := fun x => halfLine_negative_second h.a (h.A x) h.c (h.B x) (L x) hc (hp x)
      have ha := (pc x₀).1
      have hA : h.A = L := funext fun x => (pc x).2.1
      have hc_need : (∃ x, L x < 0) → h.c = -1 := by
        rintro ⟨x, hx⟩
        rcases (pc x).2.2 with hx' | hx'
        · exact (not_lt_of_ge hx'.1 hx).elim
        · exact hx'.2.2
      rcases lt_trichotomy h.b 0 with hb | hb | hb
      · have nb := fun x => halfLine_negative_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        have hd := (nb x₀).1
        have hB : h.B = fun x => -L x := funext fun x => (nb x).2.1
        left
        refine ⟨hA, hB, ha, hd, hb.le, hc.le, ?_, hc_need⟩
        rintro ⟨x, hx⟩
        rcases (nb x).2.2 with hx' | hx'
        · exfalso; linarith [hx'.1]
        · exact hx'.2.2
      · have nb : ∀ x, h.d = 1 ∧ h.B x = -L x + relu (h.A x) ∧ 0 ≤ h.B x := by
          intro x
          apply halfLine_zero_second
          simpa only [hb, zero_mul, zero_add] using hn x
        have hd := (nb x₀).1
        have hBclip : h.B = fun x => relu (-L x) := by
          funext x
          have hx := (nb x).2.1
          rw [hA] at hx
          linarith [relu_sub_relu_neg (L x)]
        have hnegLm : (fun x => -L x) ∈ E := E.neg_mem hLm
        have hclip := hE (fun x => -L x) hnegLm (hBclip ▸ hBm)
        rcases hclip with hLn | hLp
        · left
          dsimp only at hLn
          have hB : h.B = fun x => -L x := by
            funext x
            rw [hBclip]
            exact relu_of_nonneg (hLn x)
          refine ⟨hA, hB, ha, hd, hb.le, hc.le, ?_, hc_need⟩
          rintro ⟨x, hx⟩
          exfalso; linarith [hLn x]
        · right; right; left
          dsimp only at hLp
          have hB : h.B = 0 := by
            funext x
            rw [hBclip]
            exact relu_of_nonpos (hLp x)
          exact ⟨hA, hB, ha, by linarith, hb.ge, hc.le, fun x => by linarith [hLp x]⟩
      · have nb := fun x => halfLine_positive_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        right; right; left
        have hB : h.B = 0 := by
          funext x
          have hx := (nb x).2.1
          rw [hA] at hx
          change h.B x = 0
          linarith
        exact ⟨hA, hB, ha, (nb x₀).1, hb.le, hc.le, fun x => by simpa only [hA] using (nb x).2.2.2⟩
    · have pc : ∀ x, h.a = 1 ∧ h.A x = L x + relu (h.B x) ∧ 0 ≤ h.A x := by
        intro x
        apply halfLine_zero_second
        simpa only [hc, zero_mul, zero_add] using hp x
      have ha := (pc x₀).1
      rcases lt_trichotomy h.b 0 with hb | hb | hb
      · have nb := fun x => halfLine_negative_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        have hd := (nb x₀).1
        have hB : h.B = fun x => -L x := funext fun x => (nb x).2.1
        have hb_need : (∃ x, 0 < L x) → h.b = -1 := by
          rintro ⟨x, hx⟩
          rcases (nb x).2.2 with hx' | hx'
          · exfalso; linarith [hx'.1]
          · exact hx'.2.2
        have hAclip : h.A = fun x => relu (L x) := by
          funext x
          have hx := (pc x).2.1
          rw [hB] at hx
          linarith [relu_sub_relu_neg (L x)]
        rcases hE L hLm (hAclip ▸ hAm) with hLp | hLn
        · left
          have hA : h.A = L := by
            funext x
            rw [hAclip]
            exact relu_of_nonneg (hLp x)
          refine ⟨hA, hB, ha, hd, hb.le, hc.le, hb_need, ?_⟩
          rintro ⟨x, hx⟩
          exact (not_lt_of_ge (hLp x) hx).elim
        · right; right; right
          have hA : h.A = 0 := by
            funext x
            rw [hAclip]
            exact relu_of_nonpos (hLn x)
          exact ⟨hA, hB, by linarith, hd, hb.le, hc.ge, hLn⟩
      · have nb : ∀ x, h.d = 1 ∧ h.B x = -L x + relu (h.A x) ∧ 0 ≤ h.B x := by
          intro x
          apply halfLine_zero_second
          simpa only [hb, zero_mul, zero_add] using hn x
        right; left
        refine ⟨by linarith, by linarith [(nb x₀).1], hb.ge, hc.ge,
          fun x => (pc x).2.2, fun x => (nb x).2.2, ?_⟩
        intro x
        have hx := (pc x).2.1
        rw [relu_of_nonneg (nb x).2.2] at hx
        linarith
      · have nb := fun x => halfLine_positive_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        right; left
        refine ⟨by linarith, (nb x₀).1, hb.le, hc.ge,
          fun x => (nb x).2.2.2, fun x => (nb x).2.2.1, ?_⟩
        intro x
        linarith [(nb x).2.1]
    · have pc := fun x => halfLine_positive_second h.a (h.A x) h.c (h.B x) (L x) hc (hp x)
      rcases lt_trichotomy h.b 0 with hb | hb | hb
      · have nb := fun x => halfLine_negative_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        right; right; right
        have hB : h.B = fun x => -L x := funext fun x => (nb x).2.1
        have hA : h.A = 0 := by
          funext x
          have hx := (pc x).2.1
          rw [hB] at hx
          dsimp only at hx
          change h.A x = 0
          linarith
        exact ⟨hA, hB, (pc x₀).1, (nb x₀).1, hb.le, hc.le,
          fun x => by have hx := (pc x).2.2.2; rw [hB] at hx; dsimp only at hx; linarith⟩
      · have nb : ∀ x, h.d = 1 ∧ h.B x = -L x + relu (h.A x) ∧ 0 ≤ h.B x := by
          intro x
          apply halfLine_zero_second
          simpa only [hb, zero_mul, zero_add] using hn x
        right; left
        exact ⟨(pc x₀).1, by linarith [(nb x₀).1], hb.ge, hc.le,
          fun x => (pc x).2.2.1, fun x => (pc x).2.2.2, fun x => (pc x).2.1⟩
      · have nb := fun x => halfLine_positive_second h.d (h.B x) h.b (h.A x) (-L x) hb (hn x)
        right; left
        exact ⟨(pc x₀).1, (nb x₀).1, hb.le, hc.le,
          fun x => (pc x).2.2.1, fun x => (pc x).2.2.2, fun x => (pc x).2.1⟩
  · rintro (hh | hh)
    · exact hh.reconstructs
    · exact hh.reconstructs

lemma Heads.IsSplitHybrid.b_nonneg_of_pos {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) (hL : ∃ x, 0 < L x) : 0 ≤ h.b := by
  rcases hh with hh | hh | hh
  · exact hh.2.2.1
  · exact hh.2.2.2.2.1
  · obtain ⟨x, hx⟩ := hL
    exact (not_lt_of_ge (hh.2.2.2.2.2.2 x) hx).elim

lemma Heads.IsSplitHybrid.c_nonneg_of_neg {α : Type*} {h : Heads α} {L : α → ℝ}
    (hh : h.IsSplitHybrid L) (hL : ∃ x, L x < 0) : 0 ≤ h.c := by
  rcases hh with hh | hh | hh
  · exact hh.2.2.2.1
  · obtain ⟨x, hx⟩ := hL
    exact (not_lt_of_ge (hh.2.2.2.2.2.2 x) hx).elim
  · exact hh.2.2.2.2.2.1

/-- On a positive remainder value, the two reconstruction families are separated by
the open interval of cross coefficients between `-1` and `0`. -/
theorem Heads.signed_iff_b_lt_neg_half {α : Type*} [Nonempty α]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (h : Heads α) (L : α → ℝ)
    (hAm : h.A ∈ E) (hBm : h.B ∈ E) (hLm : L ∈ E)
    (hh : h.Reconstructs L) (hL : ∃ x, 0 < L x) :
    h.IsSigned L ↔ h.b < -(1 / 2 : ℝ) := by
  constructor
  · intro hs
    rw [hs.2.2.2.2.2.2.1 hL]
    norm_num
  · intro hb
    rcases (Heads.reconstructs_iff_signed_or_splitHybrid E hE h L hAm hBm hLm).mp hh with hs | ht
    · exact hs
    · have hn := ht.b_nonneg_of_pos hL
      linarith

theorem Heads.signed_iff_c_lt_neg_half {α : Type*} [Nonempty α]
    (E : Submodule ℝ (α → ℝ)) (hE : ClippingRigid E) (h : Heads α) (L : α → ℝ)
    (hAm : h.A ∈ E) (hBm : h.B ∈ E) (hLm : L ∈ E)
    (hh : h.Reconstructs L) (hL : ∃ x, L x < 0) :
    h.IsSigned L ↔ h.c < -(1 / 2 : ℝ) := by
  constructor
  · intro hs
    rw [hs.2.2.2.2.2.2.2 hL]
    norm_num
  · intro hc
    rcases (Heads.reconstructs_iff_signed_or_splitHybrid E hE h L hAm hBm hLm).mp hh with hs | ht
    · exact hs
    · have hn := ht.c_nonneg_of_neg hL
      linarith

/-- The usual signed reconstruction gives a witness for every remainder. -/
noncomputable def signedHeads {α : Type*} (L : α → ℝ) : Heads α :=
  ⟨1, -1, -1, 1, L, fun x => -L x⟩

lemma signedHeads_isSigned {α : Type*} (L : α → ℝ) : (signedHeads L).IsSigned L := by
  exact ⟨rfl, rfl, rfl, rfl, by norm_num [signedHeads], by norm_num [signedHeads],
    fun _ => rfl, fun _ => rfl⟩

lemma signedHeads_reconstructs {α : Type*} (L : α → ℝ) : (signedHeads L).Reconstructs L :=
  (signedHeads_isSigned L).reconstructs

/-- A nonnegative decomposition of the remainder supplies a split reconstruction. -/
noncomputable def splitHeads {α : Type*} (A B : α → ℝ) : Heads α :=
  ⟨1, 0, 0, 1, A, B⟩

lemma splitHeads_isSplit {α : Type*} (A B : α → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) :
    (splitHeads A B).IsSplit (fun x => A x - B x) := by
  exact ⟨by norm_num [splitHeads], by norm_num [splitHeads], le_refl _, le_refl _, hA, hB, fun _ => rfl⟩

lemma splitHeads_reconstructs {α : Type*} (A B : α → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) :
    (splitHeads A B).Reconstructs (fun x => A x - B x) :=
  (splitHeads_isSplit A B hA hB).reconstructs

end MaxCaterpillar.Fiber.Mixed65
