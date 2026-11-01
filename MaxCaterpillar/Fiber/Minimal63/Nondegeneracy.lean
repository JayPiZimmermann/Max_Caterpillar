import MaxCaterpillar.Frontier.Main
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact deletion and nondegeneracy at minimal widths

Deletion is performed on the original six parameter arrays. The lower-bound
corollaries concern equality on every real input, with arbitrary biases.
These results are prerequisites for fiber classification, not component counts.
-/

set_option autoImplicit false

namespace MaxCaterpillar

open BigOperators

namespace Network

variable {N h₁ h₂ : ℕ}

/-- Delete one neuron from the second hidden layer, retaining the other arrays. -/
def deleteSecond (net : Network N h₁ (h₂ + 1)) (k : Fin (h₂ + 1)) :
    Network N h₁ h₂ where
  W₁ := net.W₁
  b₁ := net.b₁
  W₂ := fun j => net.W₂ (k.succAbove j)
  b₂ := fun j => net.b₂ (k.succAbove j)
  w₃ := fun j => net.w₃ (k.succAbove j)
  b₃ := net.b₃

/-- A neuron with zero output weight may be deleted exactly. -/
theorem deleteSecond_eval_of_output_zero (net : Network N h₁ (h₂ + 1))
    (k : Fin (h₂ + 1)) (hk : net.w₃ k = 0) (x : Point N) :
    (net.deleteSecond k).eval x = net.eval x := by
  unfold eval
  rw [Fin.sum_univ_succAbove
    (fun j => net.w₃ j * relu
      ((∑ l, net.W₂ j l * relu ((∑ i, net.W₁ l i * x i) + net.b₁ l)) + net.b₂ j)) k]
  simp only [hk, zero_mul, zero_add]
  rfl

/-- Delete one neuron from the first hidden layer. -/
def deleteFirst (net : Network N (h₁ + 1) h₂) (j : Fin (h₁ + 1)) :
    Network N h₁ h₂ where
  W₁ := fun l => net.W₁ (j.succAbove l)
  b₁ := fun l => net.b₁ (j.succAbove l)
  W₂ := fun k l => net.W₂ k (j.succAbove l)
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

/-- Deletion preserves evaluation when the removed feature contributes zero to
every second-hidden-layer preactivation. -/
theorem deleteFirst_eval_of_contribution_zero (net : Network N (h₁ + 1) h₂)
    (j : Fin (h₁ + 1))
    (hj : ∀ (k : Fin h₂) (x : Point N),
      net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j) = 0)
    (x : Point N) : (net.deleteFirst j).eval x = net.eval x := by
  unfold eval
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change net.w₃ k * relu
      ((∑ l, net.W₂ k (j.succAbove l) *
        relu ((∑ i, net.W₁ (j.succAbove l) i * x i) + net.b₁ (j.succAbove l))) + net.b₂ k) = _
  rw [Fin.sum_univ_succAbove
    (fun l => net.W₂ k l * relu ((∑ i, net.W₁ l i * x i) + net.b₁ l)) j,
    hj k x, zero_add]

/-- A first-hidden-layer neuron with zero outgoing column may be deleted exactly. -/
theorem deleteFirst_eval_of_column_zero (net : Network N (h₁ + 1) h₂)
    (j : Fin (h₁ + 1)) (hj : ∀ k, net.W₂ k j = 0) (x : Point N) :
    (net.deleteFirst j).eval x = net.eval x := by
  apply deleteFirst_eval_of_contribution_zero net j
  intro k y
  rw [hj k, zero_mul]

/-- A first-hidden-layer neuron with zero incoming affine form may be deleted. -/
theorem deleteFirst_eval_of_affine_zero (net : Network N (h₁ + 1) h₂)
    (j : Fin (h₁ + 1)) (hj : ∀ i, net.W₁ j i = 0) (hb : net.b₁ j = 0)
    (x : Point N) : (net.deleteFirst j).eval x = net.eval x := by
  apply deleteFirst_eval_of_contribution_zero net j
  intro k y
  simp [hj, hb, relu]

/-- Delete a constant first-hidden-layer feature, absorbing its contribution in
the second-hidden-layer biases. -/
noncomputable def deleteConstantFirst (net : Network N (h₁ + 1) h₂)
    (j : Fin (h₁ + 1)) : Network N h₁ h₂ where
  W₁ := fun l => net.W₁ (j.succAbove l)
  b₁ := fun l => net.b₁ (j.succAbove l)
  W₂ := fun k l => net.W₂ k (j.succAbove l)
  b₂ := fun k => net.b₂ k + net.W₂ k j * relu (net.b₁ j)
  w₃ := net.w₃
  b₃ := net.b₃

/-- Zero incoming weights make a first-hidden-layer feature constant, even with
a nonzero bias; it can still be removed without changing the network function. -/
theorem deleteConstantFirst_eval (net : Network N (h₁ + 1) h₂)
    (j : Fin (h₁ + 1)) (hj : ∀ i, net.W₁ j i = 0) (x : Point N) :
    (net.deleteConstantFirst j).eval x = net.eval x := by
  unfold eval
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change net.w₃ k * relu
      ((∑ l, net.W₂ k (j.succAbove l) *
        relu ((∑ i, net.W₁ (j.succAbove l) i * x i) + net.b₁ (j.succAbove l))) +
        (net.b₂ k + net.W₂ k j * relu (net.b₁ j))) = _
  rw [Fin.sum_univ_succAbove
    (fun l => net.W₂ k l * relu ((∑ i, net.W₁ l i * x i) + net.b₁ l)) j]
  simp only [hj, zero_mul, Finset.sum_const_zero, zero_add]
  congr 2
  ring

/-- At the minimum second hidden width, every output weight is nonzero. -/
theorem output_ne_zero_of_max_three [NeZero N] (hN : 3 ≤ N)
    (net : Network N h₁ 3) (h : ∀ x, net.eval x = Maximum N x) (k : Fin 3) :
    net.w₃ k ≠ 0 := by
  intro hk
  have hlower := Frontier.second_width_ge_three hN (net.deleteSecond k)
    (fun x => (net.deleteSecond_eval_of_output_zero k hk x).trans (h x))
  norm_num at hlower

/-- At first hidden width six, every Max4 first row has a nonzero weight. -/
theorem first_row_ne_zero_of_max4_six (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (j : Fin 6) :
    ∃ i, net.W₁ j i ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hlower := Frontier.first_width_ge_six_max4 (net.deleteConstantFirst j)
    (fun x => (net.deleteConstantFirst_eval j hn x).trans (h x))
  norm_num at hlower

/-- At first hidden width six, no Max4 first neuron has a zero outgoing column. -/
theorem first_column_ne_zero_of_max4_six (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (j : Fin 6) :
    ∃ k, net.W₂ k j ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hlower := Frontier.first_width_ge_six_max4 (net.deleteFirst j)
    (fun x => (net.deleteFirst_eval_of_column_zero j hn x).trans (h x))
  norm_num at hlower

/-- Every exact maximum network has a positive output weight: otherwise its
output is bounded above by its output bias. -/
theorem exists_pos_output_of_max [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : ∃ k, 0 < net.w₃ k := by
  by_contra hn
  push_neg at hn
  let x : Point N := Frontier.diag (net.b₃ + 1)
  have hs : (∑ k, net.w₃ k * relu
      ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k)) ≤ 0 :=
    Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonpos_of_nonneg (hn k) (Frontier.relu_nonneg _)
  have he := h x
  rw [show Maximum N x = net.b₃ + 1 from Frontier.Maximum_diag _] at he
  unfold eval at he
  linarith

/-- Every exact maximum network has a negative output weight: otherwise its
output is bounded below by its output bias. -/
theorem exists_neg_output_of_max [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : ∃ k, net.w₃ k < 0 := by
  by_contra hn
  push_neg at hn
  let x : Point N := Frontier.diag (net.b₃ - 1)
  have hs : 0 ≤ (∑ k, net.w₃ k * relu
      ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k)) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (hn k) (Frontier.relu_nonneg _)
  have he := h x
  rw [show Maximum N x = net.b₃ - 1 from Frontier.Maximum_diag _] at he
  unfold eval at he
  linarith

/-- Change the output affine map along an affine relation among second hidden
activations. -/
noncomputable def shiftReadout (net : Network N h₁ h₂)
    (g : Fin h₂ → ℝ) (c t : ℝ) : Network N h₁ h₂ :=
  { net with w₃ := fun k => net.w₃ k - t * g k, b₃ := net.b₃ + t * c }

/-- An affine relation among second hidden activations gives an exact readout
recoding, including the compensating change in output bias. -/
theorem shiftReadout_eval (net : Network N h₁ h₂) (g : Fin h₂ → ℝ) (c t : ℝ)
    (hg : ∀ x : Point N,
      (∑ k, g k * relu
        ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k)) = c)
    (x : Point N) : (net.shiftReadout g c t).eval x = net.eval x := by
  unfold eval shiftReadout
  dsimp only
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hg x]
  ring

/-- At minimum second width three, no nontrivial linear combination of the
second activation functions can be constant. This includes arbitrary biases. -/
theorem second_activations_no_affine_relation_of_max_three [NeZero N]
    (hN : 3 ≤ N) (net : Network N h₁ 3) (h : ∀ x, net.eval x = Maximum N x)
    (g : Fin 3 → ℝ) (c : ℝ)
    (hg : ∀ x : Point N,
      (∑ k, g k * relu
        ((∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k)) = c) :
    (∀ k, g k = 0) ∧ c = 0 := by
  have hz : ∀ k, g k = 0 := by
    intro k
    by_contra hk
    let recoded := net.shiftReadout g c (net.w₃ k / g k)
    have hr : ∀ x, recoded.eval x = Maximum N x :=
      fun x => (net.shiftReadout_eval g c (net.w₃ k / g k) hg x).trans (h x)
    have hn := recoded.output_ne_zero_of_max_three hN hr k
    apply hn
    change net.w₃ k - net.w₃ k / g k * g k = 0
    rw [div_mul_cancel _ hk, sub_self]
  refine ⟨hz, ?_⟩
  have hc := hg 0
  simpa only [hz, zero_mul, Finset.sum_const_zero] using hc.symm

/-- Change the second affine map along an affine relation among first hidden
activations, with one arbitrary transfer coefficient per second neuron. -/
noncomputable def shiftFirstAffineRelation (net : Network N h₁ h₂)
    (g : Fin h₁ → ℝ) (c : ℝ) (t : Fin h₂ → ℝ) : Network N h₁ h₂ :=
  { net with
    W₂ := fun k j => net.W₂ k j - t k * g j
    b₂ := fun k => net.b₂ k + t k * c }

/-- The compensating bias shift makes every second preactivation unchanged. -/
theorem shiftFirstAffineRelation_eval (net : Network N h₁ h₂)
    (g : Fin h₁ → ℝ) (c : ℝ) (t : Fin h₂ → ℝ)
    (hg : ∀ x : Point N,
      (∑ j, g j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) = c)
    (x : Point N) : (net.shiftFirstAffineRelation g c t).eval x = net.eval x := by
  have hp (k : Fin h₂) :
      (∑ j, (net.W₂ k j - t k * g j) *
        relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + (net.b₂ k + t k * c) =
      (∑ j, net.W₂ k j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) + net.b₂ k := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [hg x]
    ring
  unfold eval shiftFirstAffineRelation
  dsimp only
  simp only [hp]

/-- At first hidden width six, no nontrivial linear combination of the first
activation functions of an exact Max4 network can be constant. This holds at
every second hidden width and with arbitrary biases. -/
theorem first_activations_no_affine_relation_of_max4_six
    (net : Network 4 6 h₂) (h : ∀ x, net.eval x = Maximum 4 x)
    (g : Fin 6 → ℝ) (c : ℝ)
    (hg : ∀ x : Point 4,
      (∑ j, g j * relu ((∑ i, net.W₁ j i * x i) + net.b₁ j)) = c) :
    (∀ j, g j = 0) ∧ c = 0 := by
  have hz : ∀ j, g j = 0 := by
    intro j
    by_contra hj
    let recoded := net.shiftFirstAffineRelation g c (fun k => net.W₂ k j / g j)
    have hr : ∀ x, recoded.eval x = Maximum 4 x :=
      fun x => (net.shiftFirstAffineRelation_eval g c (fun k => net.W₂ k j / g j)
        hg x).trans (h x)
    obtain ⟨k, hk⟩ := recoded.first_column_ne_zero_of_max4_six hr j
    apply hk
    change net.W₂ k j - net.W₂ k j / g j * g j = 0
    rw [div_mul_cancel _ hj, sub_self]
  refine ⟨hz, ?_⟩
  have hc := hg 0
  simpa only [hz, zero_mul, Finset.sum_const_zero] using hc.symm

end Network
end MaxCaterpillar
