import MaxCaterpillar.Fiber.Mixed65.ThreeGateWalls

/-! # Quantitative bounds forced by extraneous creases in the mixed dictionary

The branch bounds in this file concern arbitrary all-input residual identities,
not only the two explicit construction families. Vanishing of the negative
gate on an extraneous crease is derived from the residual identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

/-- An affine function vanishing throughout a nonempty interval except possibly
on the zero set of a nonzero affine function is identically zero. -/
theorem affine_zero_off_affine_zero (A B C D a b : ℝ) (hab : a < b)
    (hCD : ¬ (C = 0 ∧ D = 0))
    (h : ∀ x ∈ Set.Ioo a b, C + D*x ≠ 0 → A + B*x = 0) :
    A = 0 ∧ B = 0 := by
  have hcover : ∀ x ∈ Set.Ioo a b, ∃ i : Bool, True ∧
      (if i then C else A) + (if i then D else B)*x = 0 := by
    intro x hx
    by_cases hz : C + D*x = 0
    · exact ⟨true, trivial, hz⟩
    · exact ⟨false, trivial, h x hx hz⟩
  obtain ⟨i, _, hA, hB⟩ := exists_zero_affine_of_interval_cover_fintype
    (fun i : Bool => if i then C else A) (fun i : Bool => if i then D else B)
    (fun _ => True) hab hcover
  cases i
  · exact ⟨hA, hB⟩
  · exact (hCD ⟨hA, hB⟩).elim

/-- A positive affine value stays positive on an explicitly bounded interval.
The slope may be zero or have either sign. -/
theorem exists_positive_affine_radius (A k : ℝ) (hA : 0 < A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → 0 < A + k*x := by
  let δ := A / (|k| + 1)
  have hden : 0 < |k| + 1 := by linarith [abs_nonneg k]
  have hδ : 0 < δ := div_pos hA hden
  have heq : δ * (|k| + 1) = A := div_mul_cancel _ (ne_of_gt hden)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hbound : |k*x| < A := by
    rw [abs_mul]
    calc
      |k| * |x| ≤ |k| * δ := mul_le_mul_of_nonneg_left hx.le (abs_nonneg k)
      _ < A := by nlinarith only [heq, hδ]
  linarith only [(abs_lt.mp hbound).1]

/-- In the branch where the first positive carrier has zero `V` coefficient,
the second carrier's normalized `T` coefficient is at least `1/t`.
The negative-carrier coefficient relations are consequences of the first
extraneous wall; they are kept explicit so that the two geometric steps compose. -/
theorem ResidualSystem.right_coefficient_bound
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW1 : d.W 1 ≠ 0) (hU1 : d.U 1 = -d.W 1)
    (hV2 : d.V 2 = 0) (hU2 : d.U 2 = -(1+t)*d.W 2) (hW2 : d.W 2 ≠ 0) :
    1 ≤ t * (d.T 1 / d.W 1) := by
  by_contra hn
  let k := d.T 1 / d.W 1
  have hk : t*k < 1 := lt_of_not_ge hn
  have hcoeff : k * d.W 1 = d.T 1 := div_mul_cancel _ hW1
  obtain ⟨δ, hδ, hpos⟩ := exists_positive_affine_radius (1-t*k) k (by linarith only [hk])
  have hbad : ¬ (-t*k = 0 ∧ k-1 = 0) := by
    rintro ⟨hA, hB⟩
    have hk1 : k = 1 := by linarith only [hB]
    rw [hk1, mul_one] at hA
    linarith only [ht, hA]
  have hvanish : ∀ b ∈ Set.Ioo (-δ) 0, -t*k + (k-1)*b ≠ 0 →
      t*(d.T 2-(1+k)*d.W 2) + (k*d.W 2-d.T 2)*b = 0 := by
    intro b hb hneq
    let c := 1-t*k+k*b
    have hbabs : |b| < δ := by rw [abs_of_neg hb.2]; linarith only [hb.1]
    have hc : 0 < c := hpos b hbabs
    have hcneq : c ≠ max (1+b) b := by
      rw [max_eq_left (by linarith : b ≤ 1+b)]
      intro he
      apply hneq
      dsimp only [c] at he
      nlinarith only [he]
    have hTb : 0 ≤ t-b := by linarith only [ht, hb.2]
    have hgate : d.gate t 1 1 b c = 0 := by
      simp only [ResidualSystem.gate, form, hU1,
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
        relu_of_nonpos hb.2.le, relu_of_nonneg hc.le, relu_of_nonneg hTb,
        mul_zero, zero_add, add_zero, mul_one]
      linear_combination -(t-b)*hcoeff
    have hz := (d.third_gate_zero_at_spurious t h h0 h1 1 b c hc hcneq 1 h1 hgate hW1).1
    simp only [ResidualSystem.gate, form, hU2, hV2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos hb.2.le, relu_of_nonneg hc.le, relu_of_nonneg hTb,
      mul_zero, zero_add, add_zero, mul_one] at hz
    linear_combination hz
  obtain ⟨hA, hB⟩ := affine_zero_off_affine_zero
    (t*(d.T 2-(1+k)*d.W 2)) (k*d.W 2-d.T 2) (-t*k) (k-1)
    (-δ) 0 (by linarith only [hδ]) hbad hvanish
  have hT2 : d.T 2 = k*d.W 2 := by linarith only [hB]
  rw [hT2] at hA
  have hz : t*d.W 2 = 0 := by nlinarith only [hA]
  exact hW2 ((mul_eq_zero.mp hz).resolve_left (ne_of_gt ht))

/-- In the branch where the second positive carrier has zero `T` coefficient,
the first carrier's normalized `V` coefficient is at least `(1+t)/t`. -/
theorem ResidualSystem.left_coefficient_bound
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW0 : d.W 0 ≠ 0) (hU0 : d.U 0 = -(1+t)*d.W 0)
    (hT2 : d.T 2 = 0) (hU2 : d.U 2 = -d.W 2) (hW2 : d.W 2 ≠ 0) :
    1+t ≤ t * (d.V 0 / d.W 0) := by
  by_contra hn
  let r := d.V 0 / d.W 0
  have hr : t*r < 1+t := lt_of_not_ge hn
  have hcoeff : r*d.W 0 = d.V 0 := div_mul_cancel _ hW0
  obtain ⟨δ, hδ, hpos⟩ := exists_positive_affine_radius (1+t-r*t) (-r)
    (by nlinarith only [hr])
  have hbad : ¬ (t = 0 ∧ -(r+1) = 0) := fun he => (ne_of_gt ht) he.1
  have hvanish : ∀ b ∈ Set.Ioo t (t+δ), t + (-(r+1))*b ≠ 0 →
      t*d.W 2 + (d.V 2-r*d.W 2)*b = 0 := by
    intro b hb hneq
    let c := 1+t-r*b
    have hb0 : 0 < b := ht.trans hb.1
    have hdist : |b-t| < δ := by rw [abs_of_pos (sub_pos.mpr hb.1)]; linarith only [hb.2]
    have hc : 0 < c := by
      have hh := hpos (b-t) hdist
      dsimp only [c]
      nlinarith only [hh]
    have hcneq : c ≠ max (1+b) b := by
      rw [max_eq_left (by linarith : b ≤ 1+b)]
      intro he
      apply hneq
      dsimp only [c] at he
      nlinarith only [he]
    have hTb : t-b ≤ 0 := by linarith only [hb.1]
    have hgate : d.gate t 0 1 b c = 0 := by
      simp only [ResidualSystem.gate, form, hU0,
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
        relu_of_nonneg hb0.le, relu_of_nonneg hc.le, relu_of_nonpos hTb,
        mul_zero, zero_add, add_zero, mul_one]
      linear_combination -b*hcoeff
    have hz := (d.third_gate_zero_at_spurious t h h0 h1 1 b c hc hcneq 0 h0 hgate hW0).1
    simp only [ResidualSystem.gate, form, hU2, hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg hb0.le, relu_of_nonneg hc.le, relu_of_nonpos hTb,
      mul_zero, zero_add, add_zero, mul_one] at hz
    linear_combination hz
  obtain ⟨hA, _⟩ := affine_zero_off_affine_zero (t*d.W 2) (d.V 2-r*d.W 2)
    t (-(r+1)) t (t+δ) (by linarith only [hδ]) hbad hvanish
  exact hW2 ((mul_eq_zero.mp hA).resolve_left (ne_of_gt ht))

end MaxCaterpillar.Fiber.Mixed65
