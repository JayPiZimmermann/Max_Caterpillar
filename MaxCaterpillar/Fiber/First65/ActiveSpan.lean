import MaxCaterpillar.Frontier.Basic

/-! # Information-loss obstructions on first-layer cells

Suppose the maximum is a linear function plus an arbitrary decoder of finitely
many first ReLU features. A direction annihilating every first row whose
preactivation is nonnegative at a point leaves the hidden state fixed along
a small two-sided segment. Every maximizing coordinate must therefore have
the same directional variation as the explicit linear term.

The decoder is completely arbitrary; no continuity or network structure is
assumed for it. Boundary rows are included in the kernel assumption, so the
statements do not need generic points or strict gating patterns.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Frontier

open BigOperators Filter Topology

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- Annihilating all nonnegative first rows makes the first hidden state
locally constant along a two-sided line. Strictly negative rows stay inactive. -/
theorem eventually_first_features_eq_of_nonneg_kernel (A : ι → Point N)
    (q w : Point N)
    (hw : ∀ j, 0 ≤ lin (A j) q → lin (A j) w = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ j, relu (lin (A j) (q + ε • w)) = relu (lin (A j) q)) ∧
      (∀ j, relu (lin (A j) (q - ε • w)) = relu (lin (A j) q)) := by
  have hrow : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      relu (lin (A j) (q + ε • w)) = relu (lin (A j) q) ∧
      relu (lin (A j) (q - ε • w)) = relu (lin (A j) q) := by
    intro j
    by_cases hj : lin (A j) q < 0
    · filter_upwards [eventually_small (lin (A j) w) (neg_pos.mpr hj)] with ε hε
      have hbound := abs_lt.mp hε
      rw [lin_add_right, lin_sub_right, lin_smul_right]
      have hp : lin (A j) q + ε * lin (A j) w ≤ 0 := by linarith [hbound.2]
      have hm : lin (A j) q - ε * lin (A j) w ≤ 0 := by linarith [hbound.1]
      rw [relu_of_nonpos hp, relu_of_nonpos hm, relu_of_nonpos hj.le]
      exact ⟨rfl, rfl⟩
    · exact Filter.eventually_of_forall fun ε => by
        rw [lin_add_right, lin_sub_right, lin_smul_right, hw j (not_lt.mp hj),
          mul_zero, add_zero, sub_zero]
        exact ⟨rfl, rfl⟩
  filter_upwards [Filter.eventually_all.mpr hrow] with ε hε
  exact ⟨fun j => (hε j).1, fun j => (hε j).2⟩

/-- At any point, each maximizing coordinate agrees with the explicit linear
term on every direction annihilating all nonnegative first rows. -/
theorem active_kernel_top_coordinate [NeZero N] (A : ι → Point N)
    (ell : Point N) (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x : Point N, Maximum N x =
      lin ell x + Phi (fun j => relu (lin (A j) x)))
    (q w : Point N)
    (hw : ∀ j, 0 ≤ lin (A j) q → lin (A j) w = 0)
    (i : Fin N) (hi : q i = Maximum N q) :
    w i = lin ell w := by
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((∀ j, relu (lin (A j) (q + ε • w)) = relu (lin (A j) q)) ∧
       (∀ j, relu (lin (A j) (q - ε • w)) = relu (lin (A j) q))) ∧ 0 < ε :=
    (eventually_first_features_eq_of_nonneg_kernel A q w hw).and self_mem_nhdsWithin
  obtain ⟨ε, ⟨hp, hm⟩, hε⟩ := hall.exists
  have hpstate : (fun j => relu (lin (A j) (q + ε • w))) =
      (fun j => relu (lin (A j) q)) := funext hp
  have hmstate : (fun j => relu (lin (A j) (q - ε • w))) =
      (fun j => relu (lin (A j) q)) := funext hm
  have hplus : Maximum N (q + ε • w) = Maximum N q + ε * lin ell w := by
    rw [h (q + ε • w), h q, hpstate, lin_add_right, lin_smul_right]
    ring
  have hminus : Maximum N (q - ε • w) = Maximum N q - ε * lin ell w := by
    rw [h (q - ε • w), h q, hmstate, lin_sub_right, lin_smul_right]
    ring
  have hpbound := le_Maximum (q + ε • w) i
  have hmbound := le_Maximum (q - ε • w) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hplus, hminus, hi] at hpbound hmbound
  have he : ε * w i = ε * lin ell w := le_antisymm (by linarith) (by linarith)
  exact mul_left_cancel₀ hε.ne' he

/-- The normal of a target tie annihilates the common kernel of all
nonnegative first rows at that tie. This is the kernel form of the active-span
obstruction and includes first-activation boundaries. -/
theorem active_kernel_top_coordinates_eq [NeZero N] (A : ι → Point N)
    (ell : Point N) (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x : Point N, Maximum N x =
      lin ell x + Phi (fun j => relu (lin (A j) x)))
    (q w : Point N)
    (hw : ∀ j, 0 ≤ lin (A j) q → lin (A j) w = 0)
    (i k : Fin N) (hi : q i = Maximum N q) (hk : q k = Maximum N q) :
    w i = w k :=
  (active_kernel_top_coordinate A ell Phi h q w hw i hi).trans
    (active_kernel_top_coordinate A ell Phi h q w hw k hk).symm

/-- On a strict first-layer cell, it suffices to annihilate the active rows. -/
theorem strict_active_kernel_top_coordinate [NeZero N] (A : ι → Point N)
    (ell : Point N) (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x : Point N, Maximum N x =
      lin ell x + Phi (fun j => relu (lin (A j) x)))
    (q w : Point N) (hq : ∀ j, lin (A j) q ≠ 0)
    (hw : ∀ j, 0 < lin (A j) q → lin (A j) w = 0)
    (i : Fin N) (hi : q i = Maximum N q) :
    w i = lin ell w := by
  apply active_kernel_top_coordinate A ell Phi h q w _ i hi
  intro j hj
  exact hw j (lt_of_le_of_ne hj (Ne.symm (hq j)))

end Frontier
end MaxCaterpillar
