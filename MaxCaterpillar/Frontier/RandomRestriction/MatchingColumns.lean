import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! # Weighted columns on genuinely disjoint endpoint slots are independent

The slot map is an actual injection of all two-ended edge slots into the
vertex labels. Each column is literally a nonzero real multiple of the two
coordinate indicators with opposite signs. Evaluating a finite linear relation
at that column's unique first endpoint isolates its coefficient.
-/
set_option autoImplicit false
open scoped BigOperators
namespace MaxCaterpillar.Frontier.RandomRestriction

variable {ι V : Type*}

/-- A generic coordinate-pivot criterion for a finite family of functions. -/
theorem linearIndependent_of_unique_pivots [Fintype ι]
    (columns : ι → V → ℝ) (pivot : ι → V)
    (hdiag : ∀ i, columns i (pivot i) ≠ 0)
    (hoff : ∀ i j, j ≠ i → columns j (pivot i) = 0) :
    LinearIndependent ℝ columns := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a hrel i
  have hh : (∑ j, a j * columns j (pivot i)) = 0 := by
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using
      congrFun hrel (pivot i)
  rw [Finset.sum_eq_single i] at hh
  · exact (mul_eq_zero.mp hh).resolve_right (hdiag i)
  · intro j _ hji
    rw [hoff i j hji,mul_zero]
  · simp

variable [DecidableEq V]

/-- An oriented coordinate root whose two endpoints come from genuine slots. -/
def matchingRoot (slot : (ι × Bool) ↪ V) (i : ι) : V → ℝ :=
  fun x => (if x = slot (i,false) then 1 else 0) -
    (if x = slot (i,true) then 1 else 0)

/-- The actual weighted disjoint root vector, with unrestricted real weight. -/
noncomputable def weightedMatchingColumn (slot : (ι × Bool) ↪ V) (c : ι → ℝ) (i : ι) : V → ℝ :=
  c i • matchingRoot slot i

@[simp] theorem weightedMatchingColumn_pivot (slot : (ι × Bool) ↪ V)
    (c : ι → ℝ) (i : ι) : weightedMatchingColumn slot c i (slot (i,false)) = c i := by
  simp [weightedMatchingColumn,matchingRoot,slot.injective.eq_iff]

theorem weightedMatchingColumn_off_pivot (slot : (ι × Bool) ↪ V)
    (c : ι → ℝ) (i j : ι) (hji : j ≠ i) :
    weightedMatchingColumn slot c j (slot (i,false)) = 0 := by
  simp [weightedMatchingColumn,matchingRoot,slot.injective.eq_iff,Ne.symm hji]

/-- Nonzero real weights on actual disjoint endpoint slots give linear
independence; no independent-columns assumption is used. -/
theorem weightedMatchingColumns_independent [Fintype ι]
    (slot : (ι × Bool) ↪ V) (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    LinearIndependent ℝ (weightedMatchingColumn slot c) := by
  apply linearIndependent_of_unique_pivots _ (fun i => slot (i,false))
  · intro i
    rw [weightedMatchingColumn_pivot]
    exact hc i
  · intro i j hji
    exact weightedMatchingColumn_off_pivot slot c i j hji

/-- An arbitrary chosen finite subset of nonzero weighted matching columns is
independent, even when any of the remaining original weights vanish. -/
theorem weightedMatchingColumns_on_independent
    (slot : (ι × Bool) ↪ V) (c : ι → ℝ) (s : Finset ι)
    (hc : ∀ i ∈ s, c i ≠ 0) :
    LinearIndependent ℝ (fun i : s => weightedMatchingColumn slot c i.val) := by
  classical
  apply linearIndependent_of_unique_pivots _ (fun i : s => slot (i.val,false))
  · intro i
    rw [weightedMatchingColumn_pivot]
    exact hc i.val i.property
  · intro i j hji
    apply weightedMatchingColumn_off_pivot
    exact fun he => hji (Subtype.ext he)

/-- Selecting exactly the nonzero coefficients gives the promised independent
family without any nonzero-weight hypothesis on the original coefficients. -/
theorem nonzero_weightedMatchingColumns_independent [Fintype ι]
    (slot : (ι × Bool) ↪ V) (c : ι → ℝ) :
    LinearIndependent ℝ
      (fun i : {i // c i ≠ 0} => weightedMatchingColumn slot c i.val) := by
  classical
  apply linearIndependent_of_unique_pivots _
    (fun i : {i // c i ≠ 0} => slot (i.val,false))
  · intro i
    rw [weightedMatchingColumn_pivot]
    exact i.property
  · intro i j hji
    apply weightedMatchingColumn_off_pivot
    exact fun he => hji (Subtype.ext he)

#print axioms linearIndependent_of_unique_pivots
#print axioms weightedMatchingColumns_independent
#print axioms weightedMatchingColumns_on_independent
#print axioms nonzero_weightedMatchingColumns_independent
end MaxCaterpillar.Frontier.RandomRestriction
