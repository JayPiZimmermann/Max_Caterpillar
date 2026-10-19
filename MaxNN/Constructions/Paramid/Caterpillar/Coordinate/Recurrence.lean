import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Nonempty
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Star
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.LinearCombination

/-! # The coordinate-facet recurrence -/

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

theorem germDiff_formula_coordinate_sub_valueFormula_mem_LSpan_of_star
    (hs : 1 ≤ s)
    (hstar : coordinateEndpointStarSum s ∈ LSpan (s + 2) s) :
    germDiff (coordinateOne s) (formula (s + 1)) - valueFormula s ∈
      LSpan (s + 2) s := by
  have hraw := coordinateRawSum_sub_activeSum_mem_LSpan hs
  have hactive : coordinateActiveSum s - coordinateStructuredSum s ∈
      LSpan (s + 2) s := by
    rw [coordinateActiveSum_eq_structured_add_star]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstar
  have hstructured := coordinateStructuredSum_sub_valueFormula_mem_LSpan hs
  rw [germDiff_formula_eq_coordinateRawSum]
  exact sub_mem_trans hraw (sub_mem_trans hactive hstructured)

/-- The actual all-arity coordinate facet recurrence for the caterpillar formula. -/
theorem germDiff_formula_coordinate_sub_valueFormula_mem_LSpan (hs : 1 ≤ s) :
    germDiff (coordinateOne s) (formula (s + 1)) - valueFormula s ∈
      LSpan (s + 2) s :=
  germDiff_formula_coordinate_sub_valueFormula_mem_LSpan_of_star hs
    (coordinateEndpointStarSum_mem_LSpan hs)

end MaxNN.Caterpillar
