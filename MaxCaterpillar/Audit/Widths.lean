import MaxCaterpillar.Frontier

/-! # Nonvacuity (and vacuity) of the hypotheses of the width theorems

* `second_width_half_succ` assumes exactly one first-layer row with positive and exactly one
  with negative coordinate sum. The `(4, 3)` network for `max₃` (`maxThreeNet`) and a
  `(6, 3)` network for `max₄` (`maxFourNetOne`, a variant of `maxFourNet`, whose rows
  `x₁, -x₁, x₃, -x₃` violate the hypothesis) satisfy it.
* `second_width_joint` assumes `6h₁ + 11N < 3N² + 18`. Together with
  `first_width_quadratic` this pins `6h₁ + 11N` to `[3N² + 12, 3N² + 17]`; for `N = 3, 4`
  no network computing `max_N` satisfies it (`max3_widths_iff`, `max4_widths_iff`). Whether
  any network satisfies it for some `N ≥ 5` is not known.
* `free_neurons` assumes an identity; every zero-bias network computing `max_N` (e.g. the
  Caterpillar Net) provides one.
-/

open BigOperators

namespace MaxCaterpillar
namespace Audit

open Frontier

/-! ## `second_width_half_succ`: witnesses -/

/-- The hypotheses of `second_width_half_succ` are satisfiable for `N = 3`: the `(4, 3)`
network `maxThreeNet` computes `max₃` and has exactly one first-layer row with positive and
exactly one with negative coordinate sum. -/
theorem second_width_half_succ_satisfiable_three :
    ∃ net : Network 3 4 3, (∀ x, net.eval x = Maximum 3 x) ∧
      (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1 ∧
      (Finset.univ.filter fun j => ∑ i, net.W₁ j i < 0).card = 1 := by
  refine ⟨maxThreeNet, maxThreeNet_eval, ?_, ?_⟩
  · rw [Finset.card_eq_one]
    refine ⟨2, ?_⟩
    ext j
    fin_cases j <;> simp [maxThreeNet, Fin.sum_univ_succ, Fin.ext_iff] <;> norm_num <;> first | rfl | decide
  · rw [Finset.card_eq_one]
    refine ⟨3, ?_⟩
    ext j
    fin_cases j <;> simp [maxThreeNet, Fin.sum_univ_succ, Fin.ext_iff] <;> norm_num <;> first | rfl | decide

/-- A network of widths `(6, 3)` for `max₄` with first layer
`x₀ - x₁, x₂ - x₃, x₁ - x₃, x₃ - x₁, x₃, -x₃` (zero biases):
with `m₂₃ = σ(x₂ - x₃) + σ(x₃) - σ(-x₃) = max(x₂, x₃)` and
`m₀₁ - m₂₃ = σ(x₀ - x₁) + σ(x₁ - x₃) - σ(x₃ - x₁) - σ(x₂ - x₃)`,
`F = σ(m₂₃) - σ(-m₂₃) + σ(m₀₁ - m₂₃)`. -/
noncomputable def maxFourNetOne : Network 4 6 3 where
  W₁ := ![![1, -1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 0, 1], ![0, 0, 0, 1],
    ![0, 0, 0, -1]]
  b₁ := 0
  W₂ := ![![0, 1, 0, 0, 1, -1], ![0, -1, 0, 0, -1, 1], ![1, -1, 1, -1, 0, 0]]
  b₂ := 0
  w₃ := ![1, -1, 1]
  b₃ := 0

theorem maxFourNetOne_eval (x : Point 4) : maxFourNetOne.eval x = Maximum 4 x := by
  simp only [Network.eval, maxFourNetOne, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
  simp only [one_mul, zero_mul, neg_mul, add_zero, zero_add, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  rw [Maximum_four, show (Fin.succ 2 : Fin 4) = 3 from rfl]
  set m23 := relu (x 2 + -x 3) + (relu (x 3) + -relu (-x 3)) with hm23
  have hA : m23 = max (x 2) (x 3) := by
    have := relu_sub_add (x 3) (x 2)
    rw [sub_eq_add_neg, max_comm] at this
    linarith [relu_sub_relu_neg (x 3)]
  have hB : relu (x 0 + -x 1) + x 1 = max (x 0) (x 1) := by
    have := relu_sub_add (x 1) (x 0)
    rw [sub_eq_add_neg, max_comm] at this
    linarith
  have h13 : relu (x 1 + -x 3) - relu (-x 1 + x 3) = x 1 - x 3 := by
    have := relu_sub_relu_neg (x 1 + -x 3)
    rw [show -(x 1 + -x 3) = -x 1 + x 3 by ring] at this
    linarith
  have e2 : relu (-relu (x 2 + -x 3) + (-relu (x 3) + relu (-x 3))) = relu (-m23) := by
    rw [hm23]; ring_nf
  have e3 : relu (relu (x 0 + -x 1) + (-relu (x 2 + -x 3) + (relu (x 1 + -x 3) +
      -relu (-x 1 + x 3)))) = relu (max (x 0) (x 1) - m23) := by
    congr 1
    rw [← hB, hm23]
    linarith [h13, relu_sub_relu_neg (x 3)]
  rw [e2, e3, hA]
  linarith [relu_sub_relu_neg (max (x 2) (x 3)), relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1)),
    max_comm (max (x 0) (x 1)) (max (x 2) (x 3))]

/-- The hypotheses of `second_width_half_succ` are satisfiable for `N = 4` at the minimal
widths `(6, 3)`: `maxFourNetOne` computes `max₄`, its only row with positive coordinate sum
is `x₃` and its only row with negative coordinate sum is `-x₃`. -/
theorem second_width_half_succ_satisfiable_four :
    ∃ net : Network 4 6 3, (∀ x, net.eval x = Maximum 4 x) ∧
      (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1 ∧
      (Finset.univ.filter fun j => ∑ i, net.W₁ j i < 0).card = 1 := by
  refine ⟨maxFourNetOne, maxFourNetOne_eval, ?_, ?_⟩
  · rw [Finset.card_eq_one]
    refine ⟨4, ?_⟩
    ext j
    fin_cases j <;> simp [maxFourNetOne, Fin.sum_univ_succ, Fin.ext_iff] <;> norm_num <;> first | rfl | decide
  · rw [Finset.card_eq_one]
    refine ⟨5, ?_⟩
    ext j
    fin_cases j <;> simp [maxFourNetOne, Fin.sum_univ_succ, Fin.ext_iff] <;> norm_num <;> first | rfl | decide

/-! ## `second_width_joint`: the hypothesis fails for `N = 3, 4` -/

/-- No network computing `max₃` satisfies the hypothesis of `second_width_joint`. -/
theorem second_width_joint_hyp_false_three {h₁ h₂ : ℕ} (net : Network 3 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 3 x) : ¬ 6 * h₁ + 11 * 3 < 3 * 3 * 3 + 18 := by
  have h4 : 4 ≤ h₁ := (max3_widths_iff.1 ⟨net, h⟩).1
  intro hh
  norm_num at hh
  omega

/-- No network computing `max₄` satisfies the hypothesis of `second_width_joint`. -/
theorem second_width_joint_hyp_false_four {h₁ h₂ : ℕ} (net : Network 4 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) : ¬ 6 * h₁ + 11 * 4 < 3 * 4 * 4 + 18 := by
  have h6 : 6 ≤ h₁ := (max4_widths_iff.1 ⟨net, h⟩).1
  intro hh
  norm_num at hh
  omega

/-! ## `free_neurons`: the identity is satisfiable -/

/-- The hypothesis of `free_neurons` is satisfiable for every positive `N`: the Caterpillar
Net (zero biases) is such an identity with `c = 0`, `a = 0`, `C = 0`. -/
theorem free_neurons_satisfiable (N : ℕ) [NeZero N] :
    ∃ (m K : ℕ) (c : Point N) (a : Fin m → ℝ) (B : Fin m → Point N) (d : Fin K → ℝ)
      (C : Fin K → Point N) (W : Fin K → Fin m → ℝ),
      ∀ x, Maximum N x = lin c x + ∑ j, a j * relu (lin (B j) x) +
        ∑ k, d k * relu (lin (C k) x + ∑ j, W k j * relu (lin (B j) x)) := by
  obtain ⟨net, h, -, hz⟩ := caterpillar_net N
  obtain ⟨hb₁, hb₂, hb₃⟩ := hz
  refine ⟨_, _, 0, 0, net.W₁, net.w₃, 0, net.W₂, fun x => ?_⟩
  rw [← h x]
  simp only [Network.eval, lin, hb₁, hb₂, hb₃, Pi.zero_apply, add_zero, zero_mul,
    Finset.sum_const_zero, zero_add]

end Audit
end MaxCaterpillar
