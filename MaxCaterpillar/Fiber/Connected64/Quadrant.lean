import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact coefficient moves for a linear target on a quadrant

These identities are ingredients of the three-gate baseline reduction. They do
not classify arbitrary three-gate representations and do not assert connectedness
of the full Max4 fiber. Each identity holds for every input in its stated domain.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Connected64

private theorem positive_part_sub_negative (u : ℝ) : max 0 u - max 0 (-u) = u := by
  simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self u

/-- A spare nonnegative gate joins a signed encoding of `R - N` to a split
encoding. The identity holds even outside the parameter interval `[0, 1]`. -/
theorem signed_split_identity (R N t : ℝ) (hN : 0 ≤ N) :
    max 0 (R - N + t * N) - max 0 (-(R - N + t * N)) - t * max 0 N = R - N := by
  rw [positive_part_sub_negative, max_eq_right hN]
  ring

/-- At the end of the signed-to-split move the negative signed gate is dormant
on the entire quadrant, including its boundary. -/
theorem signed_split_endpoint (R N : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) :
    max 0 (R - N + 1 * N) = R ∧
      max 0 (-(R - N + 1 * N)) = 0 ∧ max 0 N = N := by
  have h : R - N + 1 * N = R := by ring
  rw [h]
  exact ⟨max_eq_right hR, max_eq_left (neg_nonpos.mpr hR), max_eq_right hN⟩

/-- Remove an additional nonnegative term from a signed pair by changing the
signed pair's preactivation. No sign condition on its output weight is needed. -/
theorem signed_extra_contract_identity (B Q d t : ℝ) (hQ : 0 ≤ Q) (ht : t ≤ 1) :
    max 0 (B - d * ((1 - t) * Q)) - max 0 (-(B - d * ((1 - t) * Q))) +
      d * max 0 ((1 - t) * Q) = B := by
  rw [positive_part_sub_negative, max_eq_right (mul_nonneg (sub_nonneg.mpr ht) hQ)]
  ring

/-- Transfer one nonnegative preactivation into another without changing their
sum of ReLUs. This is a coefficient path, so it applies to any fixed feature map. -/
theorem nonnegative_gate_transfer (P Q t : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max 0 (P + t * Q) + max 0 ((1 - t) * Q) = max 0 P + max 0 Q := by
  rw [max_eq_right (add_nonneg hP (mul_nonneg ht0 hQ)),
    max_eq_right (mul_nonneg (sub_nonneg.mpr ht1) hQ),
    max_eq_right hP, max_eq_right hQ]
  ring

/-- An output-weight transfer between duplicate features is exact for arbitrary
signs, including the parameter at which one coefficient vanishes. -/
theorem duplicate_gate_transfer (P a b t : ℝ) :
    (a + t * b) * max 0 P + ((1 - t) * b) * max 0 P =
      a * max 0 P + b * max 0 P := by
  ring

/-- Two nonnegative linear forms whose signed difference is the target have
the usual nonnegative slack parameterization. Boundary coefficients are allowed. -/
theorem nonnegative_pair_normal_form (pR pN qR qN : ℝ)
    (hpR : 0 ≤ pR) (hpN : 0 ≤ pN) (hqR : 0 ≤ qR) (hqN : 0 ≤ qN)
    (h : ∀ R N : ℝ, 0 ≤ R → 0 ≤ N →
      max 0 (pR * R + pN * N) - max 0 (qR * R + qN * N) = R - N) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ pR = 1 + a ∧ pN = b ∧
      qR = a ∧ qN = 1 + b := by
  have hR := h 1 0 (by norm_num) (by norm_num)
  have hN := h 0 1 (by norm_num) (by norm_num)
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_zero, zero_sub,
    max_eq_right hpR, max_eq_right hpN, max_eq_right hqR,
    max_eq_right hqN] at hR hN
  refine ⟨qR, pN, hqR, hpN, ?_, rfl, rfl, ?_⟩ <;> linarith

/-- Contract all nonnegative slack in a split encoding while retaining the
quadrant identity at every intermediate coefficient vector. -/
theorem split_slack_contract_identity (R N a b t : ℝ)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : t ≤ 1) :
    max 0 ((1 + (1 - t) * a) * R + ((1 - t) * b) * N) -
      max 0 (((1 - t) * a) * R + (1 + (1 - t) * b) * N) = R - N := by
  have ha' : 0 ≤ (1 - t) * a := mul_nonneg (sub_nonneg.mpr ht) ha
  have hb' : 0 ≤ (1 - t) * b := mul_nonneg (sub_nonneg.mpr ht) hb
  have hP : 0 ≤ (1 + (1 - t) * a) * R + ((1 - t) * b) * N :=
    add_nonneg (mul_nonneg (add_nonneg (by norm_num) ha') hR) (mul_nonneg hb' hN)
  have hQ : 0 ≤ ((1 - t) * a) * R + (1 + (1 - t) * b) * N :=
    add_nonneg (mul_nonneg ha' hR) (mul_nonneg (add_nonneg (by norm_num) hb') hN)
  rw [max_eq_right hP, max_eq_right hQ]
  ring

end MaxCaterpillar.Fiber.Connected64
