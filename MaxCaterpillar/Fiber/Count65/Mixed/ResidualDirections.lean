import MaxCaterpillar.Fiber.Mixed65.ThreeGateOrdering
import MaxCaterpillar.Fiber.Mixed65.SpuriousBounds

/-!
# Exhaustive projective directions of the mixed three-gate residual

The input is an arbitrary all-real residual identity with three actual gates.
The carrier labels come from `exists_ordered_three_gate`; the branch shapes
are consequences, rather than hypotheses defining the target class.
This is a residual theorem, not yet a physical five-neuron classification.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open MaxCaterpillar.Frontier

/-- The remaining negative coefficient in the left branch is forced by an
actual spurious zero of the other positive gate. -/
theorem ResidualSystem.negative_T_left_branch
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW1 : d.W 1 ≠ 0) (hU1 : d.U 1 = -d.W 1) (hV1 : d.V 1 = -d.W 1)
    (hV2 : d.V 2 = 0) (hU2 : d.U 2 = -(1+t)*d.W 2) (hW2 : d.W 2 ≠ 0) :
    d.T 2 = (d.T 1 / d.W 1 + 1) * d.W 2 := by
  let k := d.T 1 / d.W 1
  have hcoeff : k * d.W 1 = d.T 1 := div_mul_cancel _ hW1
  have hkbound' : 1 ≤ t * k :=
    d.right_coefficient_bound t ht h h0 h1 hW1 hU1 hV2 hU2 hW2
  have hk : 0 < k := by
    by_contra hn
    have hm : t * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hn)
    linarith
  let e := t / (2 * (k + 1))
  have hden : 0 < 2 * (k + 1) := by linarith
  have he : 0 < e := div_pos ht hden
  have heq : e * (2 * (k + 1)) = t := div_mul_cancel _ hden.ne'
  have hek : 0 < e * k := mul_pos he hk
  have heb : 0 < t - e := by nlinarith only [heq, he, hk, hek]
  have hc : 0 < 1 + t / 2 := by linarith
  have hneq : 1 + t / 2 ≠ max (1 + (t-e)) (t-e) := by
    rw [max_eq_left (by linarith : t-e ≤ 1+(t-e))]
    intro hz
    nlinarith only [hz, heq, hek]
  have hgate : d.gate t 1 1 (t-e) (1+t/2) = 0 := by
    simp only [ResidualSystem.gate, form, hU1, hV1,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg heb.le, relu_of_nonneg hc.le,
      show t * 1 - (t-e) = e by ring, relu_of_nonneg he.le]
    linear_combination (d.W 1 / 2) * heq - e * hcoeff
  have hz := (d.third_gate_zero_at_spurious t h h0 h1 1 (t-e) (1+t/2)
    hc hneq 1 h1 hgate hW1).1
  simp only [ResidualSystem.gate, form, hU2, hV2, zero_mul,
    relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    relu_of_nonneg hc.le,
    show t * 1 - (t-e) = e by ring, relu_of_nonneg he.le] at hz
  have hz' : e * (d.T 2 - (k+1)*d.W 2) = 0 := by
    linear_combination hz - (d.W 2 / 2) * heq
  have hh := (mul_eq_zero.mp hz').resolve_left he.ne'
  dsimp only [k] at hh ⊢
  linarith

/-- The remaining negative coefficient in the right branch is likewise forced. -/
theorem ResidualSystem.negative_V_right_branch
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1)
    (hW0 : d.W 0 ≠ 0) (hU0 : d.U 0 = -(1+t)*d.W 0) (hT0 : d.T 0 = d.W 0)
    (hT2 : d.T 2 = 0) (hU2 : d.U 2 = -d.W 2) (hW2 : d.W 2 ≠ 0) :
    d.V 2 = (d.V 0 / d.W 0 - 1) * d.W 2 := by
  let r := d.V 0 / d.W 0
  have hcoeff : r * d.W 0 = d.V 0 := div_mul_cancel _ hW0
  have hrbound : 1+t ≤ t * r :=
    d.left_coefficient_bound t ht h h0 h1 hW0 hU0 hT2 hU2 hW2
  have hr : 1 < r := by nlinarith only [hrbound, ht]
  let b := 1 / (2 * (r-1))
  have hden : 0 < 2 * (r-1) := by linarith
  have hb : 0 < b := div_pos (by norm_num) hden
  have hbeq : b * (2 * (r-1)) = 1 := div_mul_cancel _ hden.ne'
  have htb : b < t := by
    have hprod := mul_le_mul_of_nonneg_left hrbound hb.le
    nlinarith only [hprod, hbeq, ht, hb]
  have hgate : d.gate t 0 1 b (1/2) = 0 := by
    simp only [ResidualSystem.gate, form, hU0, hT0,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg hb.le, relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
      relu_of_nonneg (by linarith : 0 ≤ t * 1 - b)]
    linear_combination (d.W 0 / 2) * hbeq - b * hcoeff
  have hz := (d.third_gate_zero_at_spurious t h h0 h1 1 b (1/2)
    (by norm_num) (by rw [max_eq_left (by linarith : b ≤ 1+b)]; linarith)
    0 h0 hgate hW0).1
  simp only [ResidualSystem.gate, form, hU2, hT2, zero_mul,
    relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    relu_of_nonneg hb.le, relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hz
  have hz' : b * (d.V 2 - (r-1)*d.W 2) = 0 := by
    linear_combination hz - (d.W 2 / 2) * hbeq
  have hh := (mul_eq_zero.mp hz').resolve_left hb.ne'
  dsimp only [r] at hh ⊢
  linarith

/-- Actual row-coefficient equations for the first projective branch. -/
def ResidualSystem.HasADirections (d : ResidualSystem (Fin 3)) (t k : ℝ) : Prop :=
  d.U 0 = -(1+t)*d.W 0 ∧ d.V 0 = 0 ∧ d.T 0 = d.W 0 ∧
  d.U 1 = -d.W 1 ∧ d.V 1 = -d.W 1 ∧ d.T 1 = k*d.W 1 ∧
  d.U 2 = -(1+t)*d.W 2 ∧ d.V 2 = 0 ∧ d.T 2 = (k+1)*d.W 2

/-- Actual row-coefficient equations for the second projective branch. -/
def ResidualSystem.HasBDirections (d : ResidualSystem (Fin 3)) (t r : ℝ) : Prop :=
  d.U 0 = -(1+t)*d.W 0 ∧ d.V 0 = r*d.W 0 ∧ d.T 0 = d.W 0 ∧
  d.U 1 = -d.W 1 ∧ d.V 1 = -d.W 1 ∧ d.T 1 = 0 ∧
  d.U 2 = -d.W 2 ∧ d.V 2 = (r-1)*d.W 2 ∧ d.T 2 = 0

/-- Every ordered three-gate identity has exactly one of the two projective
branch forms. All hypotheses before the conclusion are carrier facts already
derived for arbitrary residuals by `exists_ordered_three_gate`. -/
theorem ResidualSystem.ordered_projective_normal_form
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (h0 : 0 < d.out 0) (h1 : 0 < d.out 1) (h2 : d.out 2 < 0)
    (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0)
    (hU0 : d.U 0 = -(1+t)*d.W 0) (hT0 : d.T 0 = d.W 0)
    (hU1 : d.U 1 = -d.W 1) (hV1 : d.V 1 = -d.W 1) :
    (d.W 2 ≠ 0) ∧
    ((∃ k : ℝ, 1 ≤ t*k ∧ d.HasADirections t k) ∨
      (∃ r : ℝ, 1+t ≤ t*r ∧ d.HasBDirections t r)) := by
  rcases d.middle_facet_dichotomy t ht h h2 hU0 hT0 hU1 hV1 with hV0 | hT1
  · obtain ⟨hV2,hU2,hW2⟩ := d.negative_form_left_branch t ht h h0 h1 hW0 hU0 hV0
    have hbound := d.right_coefficient_bound t ht h h0 h1 hW1 hU1 hV2 hU2 hW2
    have hT2 := d.negative_T_left_branch t ht h h0 h1 hW1 hU1 hV1 hV2 hU2 hW2
    exact ⟨hW2,Or.inl ⟨d.T 1 / d.W 1,hbound,
      hU0,hV0,hT0,hU1,hV1,(div_mul_cancel _ hW1).symm,hU2,hV2,hT2⟩⟩
  · obtain ⟨hT2,hU2,hW2⟩ := d.negative_form_right_branch t ht h h0 h1 hW1 hU1 hT1
    have hbound := d.left_coefficient_bound t ht h h0 h1 hW0 hU0 hT2 hU2 hW2
    have hV2 := d.negative_V_right_branch t ht h h0 h1 hW0 hU0 hT0 hT2 hU2 hW2
    exact ⟨hW2,Or.inr ⟨d.V 0 / d.W 0,hbound,
      hU0,(div_mul_cancel _ hW0).symm,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩⟩

/-- Projective classification of every arbitrary three-gate all-input residual.
The equivalence merely reorders the original gates; no coefficient is changed. -/
theorem ResidualSystem.exists_projective_normal_form {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) :
    ∃ e : Fin 3 ≃ ι, (d.reindex e).Represents t ∧
      0 < (d.reindex e).out 0 ∧ 0 < (d.reindex e).out 1 ∧
      (d.reindex e).out 2 < 0 ∧
      (d.reindex e).W 0 ≠ 0 ∧ (d.reindex e).W 1 ≠ 0 ∧ (d.reindex e).W 2 ≠ 0 ∧
      ((∃ k : ℝ, 1 ≤ t*k ∧ (d.reindex e).HasADirections t k) ∨
        (∃ r : ℝ, 1+t ≤ t*r ∧ (d.reindex e).HasBDirections t r)) := by
  obtain ⟨e,he,h0,h1,h2,hW0,hW1,hU0,hT0,hU1,hV1⟩ :=
    d.exists_ordered_three_gate t ht h hcard
  obtain ⟨hW2,hbranches⟩ := (d.reindex e).ordered_projective_normal_form t ht he
    h0 h1 h2 hW0 hW1 hU0 hT0 hU1 hV1
  exact ⟨e,he,h0,h1,h2,hW0,hW1,hW2,hbranches⟩

end MaxCaterpillar.Fiber.Mixed65
