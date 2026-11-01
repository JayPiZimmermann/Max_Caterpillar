import MaxCaterpillar.Fiber.Bias
import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Mixed65.Construction
import Mathlib.Topology.Algebra.Order.Group

/-! # Physical coefficient bounds under mixed-row normalization

The actual divergence inequality remains an explicit hypothesis. This module
proves its transport from a zero-bias normalized first dictionary to arbitrary
biases and arbitrary positive first-row scales. In particular, no boundedness
of a chosen normal-form parameterization is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators

variable {h₂ : ℕ}

/-- The sum of absolute effective second-layer coefficients, independent of
positive second-neuron rescaling. -/
noncomputable def coefficientSize (net : Network 4 6 h₂) : ℝ :=
  ∑ k, ∑ j, |net.w₃ k * net.W₂ k j|

/-- Effective coefficients after normalizing the positive first-row scales. -/
noncomputable def scaledCoefficientSize (net : Network 4 6 h₂) (s : Fin 6 → ℝ) : ℝ :=
  ∑ k, ∑ j, |net.w₃ k * net.W₂ k j * s j|

/-- The substantive lower bound needed to exclude the canonical boundary.
It is a quantitative assertion about every normalized exact physical network,
not a topological separation assumption. -/
def NormalizedCoefficientBound : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ net : ExactFiber 4 6 5,
    net.val.HasZeroBiases → net.val.W₁ = firstRows t →
    1 ≤ t * coefficientSize net.val

theorem continuous_coefficientSize :
    Continuous (coefficientSize (h₂ := h₂)) := by
  unfold coefficientSize
  refine continuous_finset_sum _ fun k _ => ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply k).comp continuous_w₃).mul
    ((continuous_apply j).comp ((continuous_apply k).comp continuous_W₂))).abs

theorem continuous_scaledCoefficientSize {X : Type*} [TopologicalSpace X]
    {f : X → Network 4 6 h₂} {s : X → Fin 6 → ℝ}
    (hf : Continuous f) (hs : Continuous s) :
    Continuous (fun x => scaledCoefficientSize (f x) (s x)) := by
  unfold scaledCoefficientSize
  refine continuous_finset_sum _ fun k _ => ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((((continuous_apply k).comp (continuous_w₃.comp hf)).mul
    ((continuous_apply j).comp ((continuous_apply k).comp (continuous_W₂.comp hf)))).mul
      ((continuous_apply j).comp hs)).abs

/-- Normalize an actual first-hidden-layer matrix by a genuine positive scaling
symmetry, after taking the exact zero-bias recession network. -/
noncomputable def normalizeMixedRows (net : ExactFiber 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) : ExactFiber 4 6 5 :=
  scaleFirstFiber (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j)) (zeroBiasFiber net)

theorem normalizeMixedRows_hasZeroBiases (net : ExactFiber 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) :
    (normalizeMixedRows net s hs).val.HasZeroBiases := by
  change (scaleFirst net.val.zeroBias (fun j => (s j)⁻¹)).HasZeroBiases
  simp only [Network.HasZeroBiases, scaleFirst, Network.zeroBias,
    Pi.zero_apply, mul_zero, and_self]
  exact ⟨rfl, trivial⟩

theorem normalizeMixedRows_first (net : ExactFiber 4 6 5) {t : ℝ}
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (hrows : net.val.W₁ = fun j i => s j * firstRows t j i) :
    (normalizeMixedRows net s hs).val.W₁ = firstRows t := by
  funext j i
  change (s j)⁻¹ * net.val.W₁ j i = firstRows t j i
  rw [hrows, ← mul_assoc, inv_mul_cancel (ne_of_gt (hs j)), one_mul]

theorem normalizeMixedRows_coefficientSize (net : ExactFiber 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) :
    coefficientSize (normalizeMixedRows net s hs).val = scaledCoefficientSize net.val s := by
  simp only [coefficientSize, scaledCoefficientSize, normalizeMixedRows, scaleFirstFiber,
    zeroBiasFiber, scaleFirst, Network.zeroBias, div_inv_eq_mul, mul_assoc]

/-- The normalized divergence bound transfers to every positively scaled
physical mixed dictionary, including arbitrary biases. -/
theorem normalizedCoefficientBound_scaled (hbound : NormalizedCoefficientBound)
    (net : ExactFiber 4 6 5) {t : ℝ} (ht : 0 < t)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (hrows : net.val.W₁ = fun j i => s j * firstRows t j i) :
    1 ≤ t * scaledCoefficientSize net.val s := by
  have h := hbound t ht (normalizeMixedRows net s hs)
    (normalizeMixedRows_hasZeroBiases net s hs) (normalizeMixedRows_first net s hs hrows)
  rw [normalizeMixedRows_coefficientSize] at h
  exact h

/-- Clearing the mixed-row denominator gives an inequality in actual parameter
coordinates, suitable for taking finite network limits. -/
theorem normalizedCoefficientBound_cleared (hbound : NormalizedCoefficientBound)
    (net : ExactFiber 4 6 5) {t : ℝ} (ht : 0 < t)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (hrows : net.val.W₁ = fun j i => s j * firstRows t j i) :
    net.val.W₁ 3 2 ≤ net.val.W₁ 3 0 * scaledCoefficientSize net.val s := by
  have h := mul_le_mul_of_nonneg_left
    (normalizedCoefficientBound_scaled hbound net ht s hs hrows) (hs 3).le
  have ha : net.val.W₁ 3 0 = s 3 * t := by rw [hrows]; rfl
  have hb : net.val.W₁ 3 2 = s 3 := by rw [hrows]; change s 3 * 1 = s 3; ring
  rw [ha, hb]
  simpa only [mul_one, mul_assoc] using h

end MaxCaterpillar.Fiber.Mixed65
