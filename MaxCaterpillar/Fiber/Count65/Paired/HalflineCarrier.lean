import MaxCaterpillar.Frontier.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Contracting one half-line of a nonnegative carrier

The nonnegativity assumption is on the whole actual quadrant times both real
anchor coordinates. Coordinate probes recover every required coefficient
constraint. The homotopy proof is then a convex coefficient interpolation.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired

open Frontier

/-- The carrier left after the offset vector has only one code coordinate. -/
noncomputable def halflineCarrier (s l m kp kn u v q r : ℝ) : ℝ :=
  s*q + (1-s)*r + l*u + m*v - kp*relu u - kn*relu (-u)

lemma halflineCarrier_expansion (s l m kp kn u v q r : ℝ) :
    halflineCarrier s l m kp kn u v q r =
      s*q + (1-s)*r + m*v + (l-kp)*relu u + (-l-kn)*relu (-u) := by
  have h := relu_sub_relu_neg u
  unfold halflineCarrier
  linear_combination -l * h

/-- Positivity gives all constraints, including the vanishing other code
coordinate. No support or genericity hypothesis is needed. -/
theorem halflineCarrier_coefficients (s l m kp kn : ℝ)
    (h : ∀ u v q r : ℝ, 0 ≤ q → 0 ≤ r →
      0 ≤ halflineCarrier s l m kp kn u v q r) :
    0 ≤ s ∧ s ≤ 1 ∧ m = 0 ∧ 0 ≤ l-kp ∧ 0 ≤ -l-kn := by
  have hs := h 0 0 1 0 (by norm_num) (by norm_num)
  have hs' := h 0 0 0 1 (by norm_num) (by norm_num)
  have hm := h 0 1 0 0 (by norm_num) (by norm_num)
  have hm' := h 0 (-1) 0 0 (by norm_num) (by norm_num)
  have hp := h 1 0 0 0 (by norm_num) (by norm_num)
  have hn := h (-1) 0 0 0 (by norm_num) (by norm_num)
  norm_num [halflineCarrier, relu] at hs hs' hm hm' hp hn
  exact ⟨hs, by linarith only [hs'], by linarith only [hm,hm'], by linarith only [hp], by linarith only [hn]⟩

lemma halflineCarrier_nonneg (s l kp kn u q r : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hp : 0 ≤ l-kp) (hn : 0 ≤ -l-kn)
    (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ halflineCarrier s l 0 kp kn u 0 q r := by
  rw [halflineCarrier_expansion]
  simp only [zero_mul, add_zero]
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hs hq)
    (mul_nonneg (sub_nonneg.mpr hs') hr)) (mul_nonneg hp (relu_nonneg u)))
    (mul_nonneg hn (relu_nonneg (-u)))

/-- If the positive-side linear coefficient is nonnegative, that half-line
can be contracted without violating positivity anywhere. -/
theorem contract_positive_halfline (s l m kp kn : ℝ)
    (h : ∀ u v q r : ℝ, 0 ≤ q → 0 ≤ r →
      0 ≤ halflineCarrier s l m kp kn u v q r)
    (hl : 0 ≤ l) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ u v q r : ℝ, 0 ≤ q → 0 ≤ r →
      0 ≤ halflineCarrier s l m ((1-t)*kp) kn u v q r := by
  obtain ⟨hs, hs', rfl, hp, hn⟩ := halflineCarrier_coefficients s l m kp kn h
  intro u v q r hq hr
  have hp' : 0 ≤ l-(1-t)*kp := by
    have he : l-(1-t)*kp = (1-t)*(l-kp)+t*l := by ring
    rw [he]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hp) (mul_nonneg ht0 hl)
  simpa only [halflineCarrier, zero_mul, add_zero] using
    halflineCarrier_nonneg s l ((1-t)*kp) kn u q r hs hs' hp' hn hq hr

/-- The negative-side case is symmetric and includes its zero boundary. -/
theorem contract_negative_halfline (s l m kp kn : ℝ)
    (h : ∀ u v q r : ℝ, 0 ≤ q → 0 ≤ r →
      0 ≤ halflineCarrier s l m kp kn u v q r)
    (hl : l ≤ 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ u v q r : ℝ, 0 ≤ q → 0 ≤ r →
      0 ≤ halflineCarrier s l m kp ((1-t)*kn) u v q r := by
  obtain ⟨hs, hs', rfl, hp, hn⟩ := halflineCarrier_coefficients s l m kp kn h
  intro u v q r hq hr
  have hn' : 0 ≤ -l-(1-t)*kn := by
    have he : -l-(1-t)*kn = (1-t)*(-l-kn)+t*(-l) := by ring
    rw [he]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hn)
      (mul_nonneg ht0 (neg_nonneg.mpr hl))
  simpa only [halflineCarrier, zero_mul, add_zero] using
    halflineCarrier_nonneg s l kp ((1-t)*kn) u q r hs hs' hp hn' hq hr

end MaxCaterpillar.Fiber.Count65.Paired
