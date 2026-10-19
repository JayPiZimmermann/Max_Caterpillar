import MaxNN.Constructions.Paramid.Unit
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Support functions of lower-dimensional finite point sets

This file contains only the geometric class used by the caterpillar proof.
-/

namespace MaxNN

/-- Support functions of nonempty finite point sets in `ℝ^N` whose affine span
has dimension at most `k`. -/
def LowerDimSupport (N k : ℕ) : Set ((Fin N → ℝ) → ℝ) :=
  {f | ∃ (S : Finset (Fin N → ℝ)) (hS : S.Nonempty),
    FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin N → ℝ))) ≤ k ∧
    ∀ y, f y = S.sup' hS fun p => dot p y}

/-- A linear form is the support function of a singleton, hence belongs to
every lower-dimensional class. -/
theorem dot_mem_lowerDimSupport {N : ℕ} (p : Fin N → ℝ) (k : ℕ) :
    (fun y => dot p y) ∈ LowerDimSupport N k := by
  refine ⟨{p}, Finset.singleton_nonempty p, ?_, ?_⟩
  · rw [Finset.coe_singleton, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k
  · intro y
    rw [Finset.sup'_singleton]

end MaxNN
