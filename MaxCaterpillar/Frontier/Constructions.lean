import MaxCaterpillar.Frontier.Basic
import MaxCaterpillar.Compilation

/-! # The networks of widths `(4, 3)` for `max₃` and `(6, 3)` for `max₄`, and padding

Both networks nest maxima of pairs, `max(a, b) = b + σ(a - b)` with `b = σ(b) - σ(-b)`:
* `N = 3`: first layer `x₀ - x₂, x₁ - x₂, x₂, -x₂`;
  `F = σ(σ(x₂) + σ(x₀ - x₂)) - σ(σ(-x₂)) + σ(σ(x₁ - x₂) - σ(x₀ - x₂))`.
* `N = 4`: first layer `x₀ - x₁, x₂ - x₃, x₁, -x₁, x₃, -x₃`; with
  `m₀₁ = σ(x₁) - σ(-x₁) + σ(x₀ - x₁)` and `m₂₃ = σ(x₃) - σ(-x₃) + σ(x₂ - x₃)`,
  `F = σ(m₂₃) - σ(-m₂₃) + σ(m₀₁ - m₂₃)`.
(Data as in `research/sN/frontier4/net_N3_4_3.json` and `net_N4_6_3.json`.)

`Network.padFirst` appends first-layer neurons with zero weights; together with
`Network.exists_widen` (second layer) every larger pair of widths is realized.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

/-! ## Padding -/

/-- Append `m` first-layer neurons with zero incoming and outgoing weights. -/
def _root_.MaxCaterpillar.Network.padFirst (m : ℕ) (net : Network N h₁ h₂) :
    Network N (h₁ + m) h₂ :=
  ⟨Fin.append net.W₁ (fun _ _ => 0), Fin.append net.b₁ (fun _ => 0),
    fun k => Fin.append (net.W₂ k) (fun _ => 0), net.b₂, net.w₃, net.b₃⟩

theorem _root_.MaxCaterpillar.Network.padFirst_eval (m : ℕ) (net : Network N h₁ h₂)
    (x : Point N) : (net.padFirst m).eval x = net.eval x := by
  unfold Network.eval Network.padFirst
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero]

/-- A network computing `f` gives networks computing `f` at all larger widths. -/
theorem exists_network_of_le {f : Point N → ℝ} {a b : ℕ} (net : Network N a b)
    (hf : ∀ x, net.eval x = f x) (ha : a ≤ h₁) (hb : b ≤ h₂) :
    ∃ net' : Network N h₁ h₂, ∀ x, net'.eval x = f x := by
  have he : a + (h₁ - a) = h₁ := Nat.add_sub_cancel' ha
  obtain ⟨net', h', -, -⟩ := (he ▸ net.padFirst (h₁ - a) : Network N h₁ b).exists_widen hb
    (fun x => by rw [Network.cast_first_eval, Network.padFirst_eval, hf])
  exact ⟨net', h'⟩

/-! ## Helper identities -/

lemma Maximum_three (x : Point 3) : Maximum 3 x = max (max (x 0) (x 1)) (x 2) := by
  refine le_antisymm ((Maximum_le_iff _ _).2 fun i => ?_)
    (max_le (max_le (le_Maximum x 0) (le_Maximum x 1)) (le_Maximum x 2))
  fin_cases i
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_right _ _

lemma Maximum_four (x : Point 4) :
    Maximum 4 x = max (max (x 0) (x 1)) (max (x 2) (x 3)) := by
  refine le_antisymm ((Maximum_le_iff _ _).2 fun i => ?_)
    (max_le (max_le (le_Maximum x 0) (le_Maximum x 1))
      (max_le (le_Maximum x 2) (le_Maximum x 3)))
  fin_cases i
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_right _ _)

lemma relu_sub_add (a b : ℝ) : relu (b - a) + a = max a b := by
  unfold relu
  rcases le_total a b with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]; ring
  · rw [max_eq_left (by linarith), max_eq_left h]; ring

lemma relu_relu (u : ℝ) : relu (relu u) = relu u := relu_of_nonneg (relu_nonneg u)

/-! ## The network of widths `(4, 3)` for `N = 3` -/

/-- The network of widths `(4, 3)` computing `max₃` (zero biases). -/
noncomputable def maxThreeNet : Network 3 4 3 where
  W₁ := ![![1, 0, -1], ![0, 1, -1], ![0, 0, 1], ![0, 0, -1]]
  b₁ := 0
  W₂ := ![![1, 0, 1, 0], ![0, 0, 0, 1], ![-1, 1, 0, 0]]
  b₂ := 0
  w₃ := ![1, -1, 1]
  b₃ := 0

theorem maxThreeNet_eval (x : Point 3) : maxThreeNet.eval x = Maximum 3 x := by
  simp only [Network.eval, maxThreeNet, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
  simp only [one_mul, zero_mul, neg_mul, add_zero, zero_add, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  rw [Maximum_three]
  have e1 : relu (relu (x 0 + -x 2) + relu (x 2)) = relu (x 0 + -x 2) + relu (x 2) :=
    relu_of_nonneg (add_nonneg (relu_nonneg _) (relu_nonneg _))
  have e2 := relu_sub_relu_neg (x 2)
  have e3 := relu_sub_add (relu (x 0 + -x 2)) (relu (x 1 + -x 2))
  have e4 : max (relu (x 0 + -x 2)) (relu (x 1 + -x 2)) + x 2 =
      max (max (x 0) (x 1)) (x 2) := by
    unfold relu
    simp only [max_def]
    split_ifs <;> linarith
  have e5 : relu (-relu (x 0 + -x 2) + relu (x 1 + -x 2)) =
      relu (relu (x 1 + -x 2) - relu (x 0 + -x 2)) := by ring_nf
  rw [relu_relu]
  linarith [e1, e2, e3, e4, e5]

/-! ## The network of widths `(6, 3)` for `N = 4` -/

/-- The network of widths `(6, 3)` computing `max₄` (zero biases). -/
noncomputable def maxFourNet : Network 4 6 3 where
  W₁ := ![![1, -1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, 0], ![0, -1, 0, 0], ![0, 0, 0, 1],
    ![0, 0, 0, -1]]
  b₁ := 0
  W₂ := ![![0, 1, 0, 0, 1, -1], ![0, -1, 0, 0, -1, 1], ![1, -1, 1, -1, -1, 1]]
  b₂ := 0
  w₃ := ![1, -1, 1]
  b₃ := 0

theorem maxFourNet_eval (x : Point 4) : maxFourNet.eval x = Maximum 4 x := by
  simp only [Network.eval, maxFourNet, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply]
  simp only [one_mul, zero_mul, neg_mul, add_zero, zero_add, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  rw [Maximum_four, show (Fin.succ 2 : Fin 4) = 3 from rfl]
  have hA : relu (x 2 + -x 3) + (relu (x 3) + -relu (-x 3)) = max (x 2) (x 3) := by
    have := relu_sub_add (x 3) (x 2)
    rw [sub_eq_add_neg, max_comm] at this
    linarith [relu_sub_relu_neg (x 3)]
  have hB : relu (x 0 + -x 1) + (relu (x 1) + -relu (-x 1)) = max (x 0) (x 1) := by
    have := relu_sub_add (x 1) (x 0)
    rw [sub_eq_add_neg, max_comm] at this
    linarith [relu_sub_relu_neg (x 1)]
  have e2 : relu (-relu (x 2 + -x 3) + (-relu (x 3) + relu (-x 3))) =
      relu (-(relu (x 2 + -x 3) + (relu (x 3) + -relu (-x 3)))) := by ring_nf
  have e3 : relu (relu (x 0 + -x 1) + (-relu (x 2 + -x 3) + (relu (x 1) + (-relu (-x 1) +
      (-relu (x 3) + relu (-x 3)))))) = relu ((relu (x 0 + -x 1) + (relu (x 1) + -relu (-x 1))) -
      (relu (x 2 + -x 3) + (relu (x 3) + -relu (-x 3)))) := by ring_nf
  rw [e2, e3, hA, hB]
  linarith [relu_sub_relu_neg (max (x 2) (x 3)), relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1)),
    max_comm (max (x 0) (x 1)) (max (x 2) (x 3))]

lemma maxThreeNet_hasZeroBiases : maxThreeNet.HasZeroBiases := ⟨rfl, rfl, rfl⟩

lemma maxFourNet_hasZeroBiases : maxFourNet.HasZeroBiases := ⟨rfl, rfl, rfl⟩

end Frontier
end MaxCaterpillar
