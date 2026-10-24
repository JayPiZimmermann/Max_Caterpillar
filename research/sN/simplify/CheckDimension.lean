import MaxCaterpillar.Theorems
import MaxCaterpillar.Simplify.Dimension

open MaxCaterpillar

/-- Same statement as `caterpillarDim_ge`, proved by the new route. -/
theorem caterpillarDim_ge_simplified (r : ℕ) (hr : 1 ≤ r) : r.factorial ≤ caterpillarDim r := by
  rw [caterpillarDim_eq]
  exact Simplify.factorial_le_quotientDim r hr

example : type_of% @caterpillarDim_ge_simplified = type_of% @caterpillarDim_ge := rfl
#print axioms caterpillarDim_ge_simplified
#print axioms MaxCaterpillar.Simplify.factorial_le_quotientDim
