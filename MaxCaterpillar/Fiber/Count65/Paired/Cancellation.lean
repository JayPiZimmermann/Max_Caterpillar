import MaxCaterpillar.Fiber.Paired65.RecessionAtoms
import Mathlib.Algebra.BigOperators.Ring

/-!
# Exact canceled groups and orientation changes

These identities keep all real coefficients and all offset values, including
zero offsets. They are the algebraic part of the paired four-recession
homotopies; no component count is asserted.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A canceled indicator group may move to any common offset, including zero,
without changing the represented hinge. -/
theorem canceled_group_relu_identity (j : ι → ℝ) (S : Finset ι)
    (hS : (∑ i in S, j i) = 0) (hj : (∑ i, j i) = 1) (z t : ℝ) :
    (∑ i, j i * relu (t - if i ∈ S then z else 0)) = relu t := by
  classical
  have he : (∑ i, j i * relu (t - if i ∈ S then z else 0)) =
      (∑ i in S, j i) * relu (t-z) +
        ((∑ i, j i)-(∑ i in S, j i)) * relu t := by
    have hfilter : (∑ i in S, j i) = ∑ i, if i ∈ S then j i else 0 := by
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
        (Finset.sum_filter (s := Finset.univ) (fun i => i ∈ S) j)
    rw [hfilter]
    simp only [Finset.sum_mul, sub_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  rw [he, hS, hj]
  ring

/-- Exact atom balance determines the sum of the weights as well. -/
theorem atomBalance_sum_weights (j f : ι → ℝ) (h : Paired65.AtomBalance j f) :
    (∑ i, j i) = 1 := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image f) (g := f)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) j
  rw [← hfib]
  change (∑ z in Finset.univ.image f, ∑ i in Paired65.offsetClass f z, j i) = 1
  have hclass : ∀ z : ℝ, (∑ i in Paired65.offsetClass f z, j i) =
      if z=0 then 1 else 0 := h
  simp_rw [hclass]
  obtain ⟨i, hi⟩ := Paired65.atomBalance_has_zero j f h
  have hzero : (0 : ℝ) ∈ Finset.univ.image f :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  simp only [Finset.sum_ite_eq', if_pos hzero]

/-- The common support of any nonzero indicator offset is a zero-sum group. -/
theorem indicator_support_zero_sum (j f : ι → ℝ) (S : Finset ι) (z : ℝ)
    (hz : z ≠ 0) (h : Paired65.AtomBalance j f)
    (hf : ∀ i, f i = if i ∈ S then z else 0) :
    (∑ i in S, j i) = 0 := by
  classical
  have he : Paired65.offsetClass f z = S := by
    ext i
    simp only [Paired65.mem_offsetClass, hf]
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, Ne.symm hz]
  have hs := h z
  simpa only [he, if_neg hz] using hs

/-- A Boolean orientation change only adds the expected linear term. -/
theorem oriented_relu (flip : Bool) (D f : ℝ) :
    relu (if flip then -(D-f) else D-f) =
      relu (D-f) - (if flip then 1 else 0) * (D-f) := by
  cases flip
  · simp
  · simp only [if_true, one_mul]
    have h := relu_sub_relu_neg (D-f)
    linarith only [h]

/-- The unique nonnegative carrier compensates every orientation change.
This is the exact scalar identity consumed by the coefficient homotopy. -/
theorem oriented_carrier_identity (j f : ι → ℝ) (flip : ι → Bool)
    (h : Paired65.AtomBalance j f) (B D : ℝ)
    (hcarrier : 0 ≤ B + (∑ i, j i * (if flip i then 1 else 0))*D -
      ∑ i, j i*(if flip i then 1 else 0)*f i) :
    relu (B + (∑ i, j i * (if flip i then 1 else 0))*D -
      ∑ i, j i*(if flip i then 1 else 0)*f i) +
      (∑ i, j i * relu (if flip i then -(D-f i) else D-f i)) =
        B + relu D := by
  rw [relu_of_nonneg hcarrier]
  simp_rw [oriented_relu, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Paired65.relu_identity_of_atomBalance j f h D]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

end MaxCaterpillar.Fiber.Count65.Paired
