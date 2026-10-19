import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Equal-weight compilation over finite fibers

These lemmas justify splitting one coefficient equally among all indices that
represent the same function.  They are independent of the caterpillar and
Gram-reconstruction definitions.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections.Canonical

noncomputable section

local instance fiberCompilerPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {ι α X : Type*} [Fintype ι]

/-- The indices whose represented value is exactly `g`. -/
def finiteFiber (φ : ι → α) (g : α) : Finset ι :=
  Finset.univ.filter fun i ↦ φ i = g

theorem finiteFiber_nonempty_of_mem_image (φ : ι → α) {g : α}
    (hg : g ∈ Finset.univ.image φ) : (finiteFiber φ g).Nonempty := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- On one nonempty fiber, equal shares of a scalar coefficient add back to
that coefficient.  The payload may be any scalar-valued function of the
represented value. -/
theorem sum_finiteFiber_average_mul (φ : ι → α) (g : α)
    (c v : α → ℝ) (hg : (finiteFiber φ g).Nonempty) :
    ∑ i in finiteFiber φ g,
        (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) * v (φ i) =
      c g * v g := by
  have hcard : ((finiteFiber φ g).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hg)
  calc
    ∑ i in finiteFiber φ g,
        (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) * v (φ i) =
        ∑ _i in finiteFiber φ g,
          (c g / ((finiteFiber φ g).card : ℝ)) * v g := by
      apply Finset.sum_congr rfl
      intro i hi
      have hφ : φ i = g := (Finset.mem_filter.mp hi).2
      rw [hφ]
    _ = c g * v g := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
      ac_rfl

/-- Function-valued form of `sum_finiteFiber_average_mul`. -/
theorem sum_finiteFiber_average_smul (φ : ι → X → ℝ) (g : X → ℝ)
    (c : (X → ℝ) → ℝ) (hg : (finiteFiber φ g).Nonempty) :
    ∑ i in finiteFiber φ g,
        (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) • φ i =
      c g • g := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_finiteFiber_average_mul φ g c (fun f ↦ f x) hg

/-- Summing the equal shares over every source index is the same as summing
one full coefficient over each represented value in the finite image. -/
theorem sum_finiteFiber_average_mul_eq_sum_image (φ : ι → α)
    (c v : α → ℝ) :
    ∑ i : ι, (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) * v (φ i) =
      ∑ g in Finset.univ.image φ, c g * v g := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image φ)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i ↦ (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) * v (φ i))]
  apply Finset.sum_congr rfl
  intro g hg
  exact sum_finiteFiber_average_mul φ g c v
    (finiteFiber_nonempty_of_mem_image φ hg)

/-- Function-valued global compiler identity. -/
theorem sum_finiteFiber_average_smul_eq_sum_image (φ : ι → X → ℝ)
    (c : (X → ℝ) → ℝ) :
    ∑ i : ι, (c (φ i) / ((finiteFiber φ (φ i)).card : ℝ)) • φ i =
      ∑ g in Finset.univ.image φ, c g • g := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_finiteFiber_average_mul_eq_sum_image φ c (fun f ↦ f x)

end

end MaxNN.Caterpillar.Corrections.Canonical
