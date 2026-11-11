import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic

/-! # No extra input identification at the star endpoint

These finite statements concern the actual directed root graphs. Positive
neuron scaling preserves root orientation. Their application to arbitrary
physical sector charts still requires the separate first-layer classification.
-/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace MaxCaterpillar.Fiber.Count65.Star

/-- Directed root rows before the fourth invariant row becomes a root. -/
def interiorEdge (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 2)

/-- The endpoint adds the root from coordinate zero to the signed anchor. -/
def endpointEdge (i j : Fin 4) : Prop := interiorEdge i j ∨ (i = 0 ∧ j = 2)

instance (i j : Fin 4) : Decidable (interiorEdge i j) := inferInstanceAs
  (Decidable ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 2)))
instance (i j : Fin 4) : Decidable (endpointEdge i j) := inferInstanceAs
  (Decidable (interiorEdge i j ∨ (i = 0 ∧ j = 2)))

/-- The interior directed graph has no nontrivial input automorphism. -/
theorem interior_stabilizer_trivial : ∀ p : Equiv.Perm (Fin 4),
    (∀ i j, interiorEdge i j ↔ interiorEdge (p i) (p j)) → p = Equiv.refl _ := by
  decide

/-- The extra root at the endpoint does not introduce a new stabilizer. -/
theorem endpoint_stabilizer_trivial : ∀ p : Equiv.Perm (Fin 4),
    (∀ i j, endpointEdge i j ↔ endpointEdge (p i) (p j)) → p = Equiv.refl _ := by
  decide

end MaxCaterpillar.Fiber.Count65.Star
