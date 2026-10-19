import MaxNN.Constructions.Paramid.Caterpillar.Formula.Completeness
import MaxNN.Constructions.Paramid.Geom.Coordinates

/-! # Lifting the lower-arity class identity to full vertex values -/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {r : ℕ}

theorem simplexValues_coordT (x : Fin (r + 1 + 1) → ℝ) :
    simplexValues ((CoordAux.coordT (r + 1)).mulVec x) = fun a => x a - x 0 := by
  funext a
  refine Fin.cases ?_ (fun i => ?_) a
  · rw [simplexValues_zero, sub_self]
  · rw [simplexValues_succ, CoordAux.coordT_mulVec]

theorem formula_coordT (x : Fin (r + 1 + 1) → ℝ) :
    formula r ((CoordAux.coordT (r + 1)).mulVec x) =
      valueFormula r x - totalWeight r * x 0 := by
  unfold formula
  rw [simplexValues_coordT]
  simp only [sub_eq_add_neg]
  rw [valueFormula_add_const]
  ring

/-- The raw candidate has its actual translation coefficient; the discrepancy
from coefficient one is kept as an explicit linear term. -/
theorem valueFormula_sub_MAX_eq (r : ℕ) :
    valueFormula r - MAX (r + 1 + 1) =
      (fun x => (formula r - hS (simplexVerts (r + 1)))
        ((CoordAux.coordT (r + 1)).mulVec x)) +
      (totalWeight r - 1) • dot (Pi.single (0 : Fin (r + 1 + 1)) 1) := by
  funext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    CompleteAux.dot_single_left, formula_coordT, CoordAux.MAX_succ_eq_add_hS_simplexVerts]
  ring

theorem valueFormula_sub_MAX_mem_LSpan
    (hclass : formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r) :
    valueFormula r - MAX (r + 1 + 1) ∈ LSpan (r + 1 + 1) r := by
  rw [valueFormula_sub_MAX_eq]
  exact Submodule.add_mem _
    (CompleteAux.comp_mulVec_mem_LSpan' (CoordAux.coordT (r + 1)) hclass)
    (Submodule.smul_mem _ _ (FlagAux.dot_mem_LSpan _ _))

end MaxNN.Caterpillar
