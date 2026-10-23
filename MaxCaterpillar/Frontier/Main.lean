import MaxCaterpillar.Frontier.SecondWidth
import MaxCaterpillar.Frontier.FirstWidth
import MaxCaterpillar.Frontier.Constructions

/-! # Exact width frontiers of two-hidden-layer ReLU networks for `max₃` and `max₄`

All statements are about `MaxCaterpillar.Network` with arbitrary real weights and biases.

* `no_one_hidden_max`: for `N ≥ 3` the maximum is not a one-hidden-layer function
  (affine part plus a finite sum of `a σ(b·x + β)`), even with biases.
* `second_width_ge_three`: for `N ≥ 3` every network computing the maximum has `h₂ ≥ 3`.
* `first_width_ge_four_max3`, `first_width_ge_six_max4`: `h₁ ≥ 4` for `N = 3`, `h₁ ≥ 6`
  for `N = 4`.
* `max3_widths_iff`, `max4_widths_iff`: the widths `(h₁, h₂)` of networks computing the
  maximum are exactly `h₁ ≥ 4, h₂ ≥ 3` for `N = 3` and `h₁ ≥ 6, h₂ ≥ 3` for `N = 4`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- **Lemma 0′ (with biases).** For `N ≥ 3`, the maximum of `N` numbers is not a
one-hidden-layer function `x ↦ c·x + γ + Σⱼ aⱼ σ(Bⱼ·x + βⱼ)`. -/
theorem no_one_hidden_max [NeZero N] (hN : 3 ≤ N) (m : ℕ) (c : Point N) (γ : ℝ)
    (a : Fin m → ℝ) (B : Fin m → Point N) (β : Fin m → ℝ) :
    ¬ ∀ x : Point N, Maximum N x =
      (∑ i, c i * x i) + γ + ∑ j, a j * relu ((∑ i, B j i * x i) + β j) := by
  intro h
  have hloc : LocOddLin (fun x : Point N =>
      lin c x + γ + ∑ j, a j * relu (lin (B j) x + β j)) 0 :=
    ((locAff_lin c 0).locOddLin.add (locOddLin_const γ 0)).add
      (LocOddLin.sum _ fun j _ =>
        (((locAff_lin (B j) 0).add (locAff_const (β j) 0)).relu_locOddLin).const_mul (a j))
  exact not_locOddLin_max 0 Finset.univ
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hN) (fun _ _ => rfl)
    (fun i hi => absurd (Finset.mem_univ i) hi) (hloc.congr fun x => (h x).symm)

/-- **Lemma 0.** `max(x₀, x₁, x₂)` is not a one-hidden-layer function. -/
theorem no_one_hidden_max3 (m : ℕ) (c : Point 3) (γ : ℝ) (a : Fin m → ℝ)
    (B : Fin m → Point 3) (β : Fin m → ℝ) :
    ¬ ∀ x : Point 3, Maximum 3 x =
      (∑ i, c i * x i) + γ + ∑ j, a j * relu ((∑ i, B j i * x i) + β j) :=
  no_one_hidden_max le_rfl m c γ a B β

/-- **Theorem 1.** For `N ≥ 3`, every two-hidden-layer network computing `max_N` has at
least three neurons in its second hidden layer, whatever its first width. -/
theorem second_width_ge_three [NeZero N] (hN : 3 ≤ N) (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : 3 ≤ h₂ :=
  net.toZ.second_width_ge_three hN (net.toZ_eval_of_max h)

/-- Every two-hidden-layer network computing `max_N` has at least `N + 1` neurons in its
first hidden layer. -/
theorem first_width_ge_succ [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N + 1 ≤ h₁ :=
  net.toZ.first_width_ge_succ (net.toZ_eval_of_max h)

/-- **First width for `max₃`**: `h₁ ≥ 4`. -/
theorem first_width_ge_four_max3 (net : Network 3 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 3 x) : 4 ≤ h₁ :=
  net.toZ.first_width_ge_four_max3 (net.toZ_eval_of_max h)

/-- **Theorem 2 (first width for `max₄`)**: `h₁ ≥ 6`. -/
theorem first_width_ge_six_max4 (net : Network 4 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) : 6 ≤ h₁ :=
  net.toZ.first_width_ge_six_max4 (net.toZ_eval_of_max h)

/-- **Frontier for `max₃`**: a network of widths `(h₁, h₂)` computes the maximum of three
numbers if and only if `h₁ ≥ 4` and `h₂ ≥ 3`. -/
theorem max3_widths_iff :
    (∃ net : Network 3 h₁ h₂, ∀ x, net.eval x = Maximum 3 x) ↔ 4 ≤ h₁ ∧ 3 ≤ h₂ := by
  constructor
  · rintro ⟨net, h⟩
    exact ⟨first_width_ge_four_max3 net h, second_width_ge_three le_rfl net h⟩
  · rintro ⟨h1, h2⟩
    exact exists_network_of_le maxThreeNet maxThreeNet_eval h1 h2

/-- **Frontier for `max₄`**: a network of widths `(h₁, h₂)` computes the maximum of four
numbers if and only if `h₁ ≥ 6` and `h₂ ≥ 3`. -/
theorem max4_widths_iff :
    (∃ net : Network 4 h₁ h₂, ∀ x, net.eval x = Maximum 4 x) ↔ 6 ≤ h₁ ∧ 3 ≤ h₂ := by
  constructor
  · rintro ⟨net, h⟩
    exact ⟨first_width_ge_six_max4 net h, second_width_ge_three (by norm_num) net h⟩
  · rintro ⟨h1, h2⟩
    exact exists_network_of_le maxFourNet maxFourNet_eval h1 h2

end Frontier
end MaxCaterpillar
