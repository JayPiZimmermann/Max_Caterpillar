import MaxNN.Constructions.Paramid.Caterpillar.Formula.Assembly
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Recurrence
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Class

/-! # Correctness of the finite caterpillar formula for every arity

The formula is defined directly at each arity. Its correctness proof uses
induction, with the canonical coordinate recurrence as the induction step.
-/

namespace MaxNN.Caterpillar

open ParamidGeom Corrections

/-- The actual finite, factorial-weighted caterpillar sum represents the
simplex modulo functions supported in lower dimension, for every `r ≥ 1`. -/
theorem formula_sub_simplex_mem_LSpan (r : ℕ) (hr : 1 ≤ r) :
    formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r := by
  revert hr
  induction r with
  | zero => exact fun hr => False.elim (Nat.not_succ_le_zero 0 hr)
  | succ s ih =>
      intro hr
      by_cases hs : s = 0
      · subst s
        rw [formula_one_eq_simplex, sub_self]
        exact Submodule.zero_mem _
      · exact formula_sub_simplex_mem_LSpan_succ_of_recurrence (by omega)
          (ih (by omega))
          (germDiff_formula_coordinate_sub_valueFormula_mem_LSpan (by omega))

/-- No coordinate-recurrence or correction hypothesis remains. -/
theorem formulaClassIdentity (r : ℕ) (hr : 1 ≤ r) : FormulaClassIdentity r :=
  formula_sub_simplex_mem_LSpan r hr

end MaxNN.Caterpillar
