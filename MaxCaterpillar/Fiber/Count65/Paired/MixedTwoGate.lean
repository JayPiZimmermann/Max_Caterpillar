import MaxCaterpillar.Fiber.Count65.Paired.TwoGate

/-! # Uniform two-gate classification with mixed independent increments

The two preactivations may have arbitrary anchor-dependent intercepts. Their
increment coefficients are fixed. A target with one positive and one negative
increment coefficient forces the same signed/split branch at every anchor.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Frontier

private def quadrant : Set (ℝ×ℝ) := {p | 0≤p.1 ∧ 0≤p.2}

private lemma quadrant_convex : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)⟩

private def affineQR (C a b : ℝ) : (ℝ×ℝ) →ᵃ[ℝ] ℝ where
  toFun := fun p => C+a*p.1+b*p.2
  linear :=
    { toFun := fun p => a*p.1+b*p.2
      map_add' := by intro x y; dsimp; ring
      map_smul' := by
        intro t x
        change a*(t*x.1)+b*(t*x.2)=t*(a*x.1+b*x.2)
        ring }
  map_vadd' := by intro p v; dsimp; ring

private lemma affineQR_nonnegative_coefficients (C a b : ℝ)
    (h : ∀ q r : ℝ, 0≤q → 0≤r → 0≤C+a*q+b*r) : 0≤a ∧ 0≤b := by
  have hC := h 0 0 (by norm_num) (by norm_num)
  simp only [mul_zero,add_zero] at hC
  constructor
  · by_contra ha
    have ha0 : a<0 := lt_of_not_ge ha
    have hq : 0≤ -(C+1)/a := div_nonneg_of_nonpos (by linarith only [hC]) ha0.le
    have he : a*(-(C+1)/a)= -(C+1) := by field_simp [ne_of_lt ha0]; ring
    have hh := h (-(C+1)/a) 0 hq (by norm_num)
    rw [he] at hh
    norm_num at hh
  · by_contra hb
    have hb0 : b<0 := lt_of_not_ge hb
    have hr : 0≤ -(C+1)/b := div_nonneg_of_nonpos (by linarith only [hC]) hb0.le
    have he : b*(-(C+1)/b)= -(C+1) := by field_simp [ne_of_lt hb0]; ring
    have hh := h 0 (-(C+1)/b) (by norm_num) hr
    rw [he] at hh
    norm_num at hh

private lemma mixedQR_signs (C a b : ℝ) (ha : 0<a) (hb : b<0) :
    (∃ p∈quadrant, 0<affineQR C a b p) ∧
      (∃ p∈quadrant, affineQR C a b p<0) := by
  have hq : 0≤(|C|+1)/a := div_nonneg (by positivity) ha.le
  have hr : 0≤-(|C|+1)/b := div_nonneg_of_nonpos (by linarith only [abs_nonneg C]) hb.le
  have heq : a*((|C|+1)/a)=|C|+1 := by field_simp [ne_of_gt ha]; ring
  have her : b*(-(|C|+1)/b)= -(|C|+1) := by field_simp [ne_of_lt hb]; ring
  constructor
  · refine ⟨((|C|+1)/a,0),⟨hq,le_refl 0⟩,?_⟩
    change 0<C+a*((|C|+1)/a)+b*0
    rw [heq]
    have hh := neg_abs_le_self C
    linarith only [hh]
  · refine ⟨(0,-(|C|+1)/b),⟨le_refl 0,hr⟩,?_⟩
    change C+a*0+b*(-(|C|+1)/b)<0
    rw [her]
    have hh := le_abs_self C
    linarith only [hh]

/-- Fixed opposite increment signs make the branch global in the anchor
parameter, despite an arbitrary and possibly nonlinear intercept dependence. -/
theorem mixed_two_gate_uniform {X : Type*} (G H C : X→ℝ)
    (a b c d l n : ℝ) (hl : 0<l) (hn : n<0)
    (heq : ∀ x q r, 0≤q → 0≤r →
      relu (G x+a*q+b*r)-relu (H x+c*q+d*r)=C x+l*q+n*r) :
    (∀ x q r, 0≤q → 0≤r →
      G x+a*q+b*r=C x+l*q+n*r ∧ H x+c*q+d*r= -(C x+l*q+n*r)) ∨
    (∀ x q r, 0≤q → 0≤r →
      0≤G x+a*q+b*r ∧ 0≤H x+c*q+d*r ∧
        (G x+a*q+b*r)-(H x+c*q+d*r)=C x+l*q+n*r) := by
  classical
  have hc : ∀ x, (∀ q r, 0≤q → 0≤r →
        G x+a*q+b*r=C x+l*q+n*r ∧ H x+c*q+d*r= -(C x+l*q+n*r)) ∨
      (∀ q r, 0≤q → 0≤r →
        0≤G x+a*q+b*r ∧ 0≤H x+c*q+d*r ∧
          (G x+a*q+b*r)-(H x+c*q+d*r)=C x+l*q+n*r) := by
    intro x
    have hs := mixedQR_signs (C x) l n hl hn
    have hh := two_gate_affine_classification quadrant quadrant_convex
      (affineQR (G x) a b) (affineQR (H x) c d) (affineQR (C x) l n)
      hs.1 hs.2 (fun p hp => heq x p.1 p.2 hp.1 hp.2)
    exact hh.imp (fun h q r hq hr => h (q,r) ⟨hq,hr⟩)
      (fun h q r hq hr => h (q,r) ⟨hq,hr⟩)
  by_cases hs : ∃ x, ∀ q r, 0≤q → 0≤r →
      G x+a*q+b*r=C x+l*q+n*r ∧ H x+c*q+d*r= -(C x+l*q+n*r)
  · obtain ⟨x,hx0⟩ := hs
    have h00 := (hx0 0 0 (by norm_num) (by norm_num)).1
    have h01 := (hx0 0 1 (by norm_num) (by norm_num)).1
    have hb : b=n := by linarith only [h00,h01]
    refine Or.inl (fun y => (hc y).resolve_right ?_)
    intro hy
    have hpos := affineQR_nonnegative_coefficients (G y) a b
      (fun q r hq hr => (hy q r hq hr).1)
    linarith only [hpos.2,hb,hn]
  · refine Or.inr (fun x => (hc x).resolve_left ?_)
    intro hx
    exact hs ⟨x,hx⟩

/-- The same uniform branch statement when the negative increment is first. -/
theorem mixed_two_gate_uniform_negative_first {X : Type*} (G H C : X→ℝ)
    (a b c d l n : ℝ) (hl : l<0) (hn : 0<n)
    (heq : ∀ x q r, 0≤q → 0≤r →
      relu (G x+a*q+b*r)-relu (H x+c*q+d*r)=C x+l*q+n*r) :
    (∀ x q r, 0≤q → 0≤r →
      G x+a*q+b*r=C x+l*q+n*r ∧ H x+c*q+d*r= -(C x+l*q+n*r)) ∨
    (∀ x q r, 0≤q → 0≤r →
      0≤G x+a*q+b*r ∧ 0≤H x+c*q+d*r ∧
        (G x+a*q+b*r)-(H x+c*q+d*r)=C x+l*q+n*r) := by
  have hh := mixed_two_gate_uniform G H C b a d c n l hn hl
    (fun x q r hq hr => by
      simpa only [add_comm,add_left_comm,add_assoc] using heq x r q hr hq)
  exact hh.imp (fun h x q r hq hr => by
    simpa only [add_comm,add_left_comm,add_assoc] using h x r q hr hq)
    (fun h x q r hq hr => by
      simpa only [add_comm,add_left_comm,add_assoc] using h x r q hr hq)

end MaxCaterpillar.Fiber.Count65.Paired
