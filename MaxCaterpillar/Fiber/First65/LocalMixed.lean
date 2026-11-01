import MaxCaterpillar.Fiber.First65
import MaxCaterpillar.Fiber.First65.ActiveSpan
import MaxCaterpillar.Fiber.Mixed65.Construction

/-! # Finite-cell local rigidity of the mixed first hidden layer

The hypotheses in `LocalCertificate` are finitely many strict inequalities
on the actual first weight matrix. No classification is assumed. They hold
at every normalized mixed matrix and force every nearby exact network to
have the same mixed first-layer form, up to positive row scaling.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar

open BigOperators Frontier

namespace Network

variable {N h₁ h₂ : ℕ}

/-- Information lost by the homogeneous first hidden state cannot be
recovered by any suffix, even if the original network has biases. -/
theorem first_kernel_top_coordinate [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) (q w : Point N)
    (hw : ∀ j, 0 ≤ lin (net.W₁ j) q → lin (net.W₁ j) w = 0)
    (i : Fin N) (hi : q i = Maximum N q) : w i = 0 := by
  let Phi : (Fin h₁ → ℝ) → ℝ := fun a => ∑ k, net.w₃ k * relu (∑ j, net.W₂ k j * a j)
  have hf : ∀ x, Maximum N x = lin (0 : Point N) x +
      Phi (fun j => relu (lin (net.W₁ j) x)) := by
    intro x
    rw [lin_zero_left, zero_add]
    exact (net.toZ_eval_of_max h x).symm
  have he := active_kernel_top_coordinate net.W₁ 0 Phi hf q w hw i hi
  simpa only [lin_zero_left] using he

end Network

namespace Fiber.Mixed65

variable {h₂ : ℕ}

/-- Every row outside a specified finite set is strictly inactive. -/
def InactiveOutside (A : Fin 6 → Point 4) (x : Point 4) (J : Finset (Fin 6)) : Prop :=
  ∀ j, j ∉ J → lin (A j) x < 0

noncomputable def carrierPlusPoint (t : ℝ) : Point 4 := ![-1 - t, 1 - t, 1, 0]
noncomputable def carrierMinusPoint (t : ℝ) : Point 4 := ![-3 - t, -1 - t, -1, -2]
noncomputable def bPoint : Point 4 := ![1, 2, 1, 0]
noncomputable def cPoint (t : ℝ) : Point 4 := ![-1 - t, 1 - t, 1, 2]
noncomputable def qPoint (t : ℝ) : Point 4 := ![2 + 2*t, 1 + 2*t, 1, 0]
noncomputable def tPoint : Point 4 := ![2, 0, 1, 0]
noncomputable def bTiePlus : Point 4 := ![0, 1, 1, 0]
noncomputable def bTieMinus : Point 4 := ![-2, -1, -1, -2]
noncomputable def cTiePlus (t : ℝ) : Point 4 := ![-1 - t, 1 - t, 1, 1]
noncomputable def cTieMinus (t : ℝ) : Point 4 := ![-3 - t, -1 - t, -1, -1]

/-- A finite open condition around the normalized mixed first matrix. -/
structure LocalCertificate (t : ℝ) (A : Fin 6 → Point 4) : Prop where
  q_pos : 0 < A 0 0
  b_pos : 0 < A 1 1
  c_pos : 0 < A 2 3
  t_pos : 0 < A 3 0
  t_mid_pos : 0 < A 3 2
  carrier_pos : 0 < A 4 2
  carrier_neg : A 5 2 < 0
  carrierPlus : InactiveOutside A (carrierPlusPoint t) {4}
  carrierMinus : InactiveOutside A (carrierMinusPoint t) {5}
  bCell : InactiveOutside A bPoint {1, 4}
  cCell : InactiveOutside A (cPoint t) {2, 4}
  qCell : InactiveOutside A (qPoint t) {0, 1, 4}
  tCell : InactiveOutside A tPoint {0, 3, 4}
  bTiePlusCell : InactiveOutside A bTiePlus {1, 4}
  bTieMinusCell : InactiveOutside A bTieMinus {1, 5}
  cTiePlusCell : InactiveOutside A (cTiePlus t) {2, 4}
  cTieMinusCell : InactiveOutside A (cTieMinus t) {2, 5}

private theorem lin_of_support_singleton (A : Point 4) (i : Fin 4)
    (hA : ∀ j, j ≠ i → A j = 0) (w : Point 4) : lin A w = A i * w i := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hA j hji, zero_mul]
  · simp

/-- A sole potentially active first row must be supported on each winning
coordinate. This is a direct first-state information obstruction. -/
theorem row_support_of_single_active (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (x : Point 4) (p : Fin 6) (i : Fin 4)
    (hx : InactiveOutside net.W₁ x {p}) (hi : x i = Maximum 4 x) :
    ∀ j, j ≠ i → net.W₁ p j = 0 := by
  intro j hji
  let w : Point 4 := net.W₁ p j • unitVec i - net.W₁ p i • unitVec j
  have hp : lin (net.W₁ p) w = 0 := by
    simp only [w, lin_sub_right, lin_smul_right, lin_unitVec]
    ring
  have he := net.first_kernel_top_coordinate h x w (fun k hk => by
    have hkp : k = p := by
      by_contra hkp
      have hn := hx k (by simpa using hkp)
      linarith
    simpa only [hkp] using hp) i hi
  simpa [w, unitVec, Ne.symm hji] using he

/-- With one carrier supported on an anchor coordinate, another potentially
active row can only use that anchor and the winning coordinate. -/
theorem row_support_of_two_active (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (x : Point 4) (p a : Fin 6)
    (i z : Fin 4) (hiz : i ≠ z)
    (hx : InactiveOutside net.W₁ x {p,a}) (hi : x i = Maximum 4 x)
    (ha : ∀ j, j ≠ z → net.W₁ a j = 0) :
    ∀ j, j ≠ i → j ≠ z → net.W₁ p j = 0 := by
  intro j hji hjz
  let w : Point 4 := net.W₁ p j • unitVec i - net.W₁ p i • unitVec j
  have hp : lin (net.W₁ p) w = 0 := by
    simp only [w, lin_sub_right, lin_smul_right, lin_unitVec]
    ring
  have haw : lin (net.W₁ a) w = 0 := by
    rw [lin_of_support_singleton (net.W₁ a) z ha]
    simp [w, unitVec, hiz, Ne.symm hiz, hjz, Ne.symm hjz]
  have he := net.first_kernel_top_coordinate h x w (fun k hk => by
    have hka : k = p ∨ k = a := by
      by_contra hn
      have hl := hx k (by simpa using hn)
      linarith
    rcases hka with hkp | hka
    · simpa only [hkp] using hp
    · simpa only [hka] using haw) i hi
  simpa [w, unitVec, Ne.symm hji] using he

 /-- If only a carrier and one other row may be active, that other row
cannot be strictly inactive when a different coordinate wins. -/
theorem row_nonneg_of_two_active (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (x : Point 4) (p a : Fin 6)
    (i z : Fin 4) (hiz : i ≠ z)
    (hx : InactiveOutside net.W₁ x {p,a}) (hi : x i = Maximum 4 x)
    (ha : ∀ j, j ≠ z → net.W₁ a j = 0) :
    0 ≤ lin (net.W₁ p) x := by
  by_contra hn
  have hn' : lin (net.W₁ p) x < 0 := lt_of_not_ge hn
  have he := net.first_kernel_top_coordinate h x (unitVec i) (fun k hk => by
    have hka : k = p ∨ k = a := by
      by_contra hn
      have hl := hx k (by simpa using hn)
      linarith
    rcases hka with hkp | hka
    · subst k
      linarith
    · subst k
      rw [lin_unitVec]
      exact ha i hiz) i hi
  simpa [unitVec] using he

end Fiber.Mixed65
end MaxCaterpillar
