import MaxCaterpillar.Fiber.Star65.Residual

/-! # Independence of the star-to-path features and residual directions

The linear remainder and the three residual core functions are independent
throughout each admitted parameter domain, including its finite boundaries.
These are algebraic prerequisites for the physical lift classification;
they do not by themselves classify arbitrary network completions.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

/-- A linear relation among the four first-layer feature functions is trivial. -/
theorem features_independent {r : ℝ} (hr : 0 < r) (aU aV aW aT : ℝ)
    (H : ∀ q b c : ℝ, aU * max 0 q + aV * max 0 b + aW * max 0 c +
      aT * max 0 (q + r * b) = 0) :
    aU = 0 ∧ aV = 0 ∧ aW = 0 ∧ aT = 0 := by
  have hW := H 0 0 1
  norm_num at hW
  have hU := H r (-1) 0
  rw [max_eq_right hr.le] at hU
  norm_num at hU
  have hU' : aU = 0 := hU.resolve_right (ne_of_gt hr)
  have hV := H (-r) 1 0
  rw [max_eq_left (neg_nonpos.mpr hr.le)] at hV
  norm_num at hV
  have hT := H 1 0 0
  norm_num [hU'] at hT
  exact ⟨hU', hV, hW, hT⟩

/-- The remainder and the three normalized Branch I cores are independent. -/
theorem branchI_core_independent {r k : ℝ} (hr : 0 < r) (hk : k ≤ 0)
    (a b c d : ℝ)
    (H : ∀ q v w : ℝ,
      a * max 0 w +
      b * (comparison r q v - max 0 w) +
      c * (max 0 v - max 0 w + k * max 0 q) +
      d * (comparison r q v - max 0 q - max 0 w + k * max 0 q) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcoeff := features_independent hr
    (b * (r - 1) + c * k * r + d * (k * r - 1))
    (c * r) (r * (a - b - c - d)) (b + d) (by
      intro q v w
      have heq := H q v w
      unfold comparison at heq
      field_simp [hr0] at heq
      nlinarith only [heq])
  rcases hcoeff with ⟨hU, hV, hW, hT⟩
  have hc : c = 0 := (mul_eq_zero.mp hV).resolve_right hr0
  have hW' : a - b - c - d = 0 := (mul_eq_zero.mp hW).resolve_left hr0
  have hbd : b * (1 - k) * r = 0 := by
    rw [hc] at hU
    have hd : d = -b := by linarith only [hT]
    rw [hd] at hU
    nlinarith only [hU]
  have hb : b = 0 := by
    have hb' : b * (1 - k) = 0 := (mul_eq_zero.mp hbd).resolve_right hr0
    exact (mul_eq_zero.mp hb').resolve_right (by linarith only [hk])
  have hd : d = 0 := by linarith only [hT, hb]
  have ha : a = 0 := by linarith only [hW', hb, hc, hd]
  exact ⟨ha, hb, hc, hd⟩

/-- The remainder and the three normalized Branch II cores are independent. -/
theorem branchII_core_independent {r h : ℝ} (hr : 0 < r) (hh : h ≤ -1)
    (a b c d : ℝ)
    (H : ∀ q v w : ℝ,
      a * max 0 w +
      b * (comparison r q v - max 0 w + h * max 0 v) +
      c * (max 0 q + max 0 v - max 0 w) +
      d * (max 0 q + (1 + h) * max 0 v - max 0 w) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcoeff := features_independent hr
    (b * (r - 1) + c * r + d * r)
    (b * h * r + c * r + d * (1 + h) * r)
    (r * (a - b - c - d)) b (by
      intro q v w
      have heq := H q v w
      unfold comparison at heq
      field_simp [hr0] at heq
      nlinarith only [heq])
  rcases hcoeff with ⟨hU, hV, hW, hb⟩
  have hW' : a - b - c - d = 0 := (mul_eq_zero.mp hW).resolve_left hr0
  rw [hb] at hU hV
  have hcd : (c + d) * r = 0 := by nlinarith only [hU]
  have hcd' : c + d = 0 := (mul_eq_zero.mp hcd).resolve_right hr0
  have hdh : d * h * r = 0 := by nlinarith only [hU, hV]
  have hd : d = 0 := by
    have hdh' : d * h = 0 := (mul_eq_zero.mp hdh).resolve_right hr0
    exact (mul_eq_zero.mp hdh').resolve_right (by linarith only [hh])
  have hc : c = 0 := by linarith only [hcd', hd]
  have ha : a = 0 := by linarith only [hW', hb, hc, hd]
  exact ⟨ha, hb, hc, hd⟩

end MaxCaterpillar.Fiber.Star65
