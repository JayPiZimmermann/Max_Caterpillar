import MaxCaterpillar.Fiber.Disconnected65
import MaxCaterpillar.Frontier.Main

/-! Independent exact-type, nonvacuity, and axiom checks for the full disconnection
result. This file checks a lower bound of two, not an exact count of 65.
-/

set_option autoImplicit false

open MaxCaterpillar MaxCaterpillar.Fiber

example : Nontrivial (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_at_least_two_components

example : Nontrivial (ConnectedComponents (ExactFiber 4 6 5)) :=
  max4_6_5_raw_at_least_two_components

example : ¬ PreconnectedSpace (SymmetryQuotient 4 6 5) :=
  max4_6_5_quotient_not_preconnected

example : ¬ PreconnectedSpace (ExactFiber 4 6 5) :=
  max4_6_5_raw_not_preconnected

example : ¬ HasComponentCount 4 6 5 1 := max4_6_5_not_one_component

example : IsClopen Mixed65.sector := max4_6_5_mixed_sector_isClopen

example :
    (quotientMk Mixed65.mixedPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) ≠
      (quotientMk Mixed65.paddedMinimalPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_witness_components_ne

example (x : Fin 4 → ℝ) : Mixed65.mixedPoint.val.eval x = Maximum 4 x :=
  Mixed65.mixedPoint.property x

example (x : Fin 4 → ℝ) : Mixed65.paddedMinimalPoint.val.eval x = Maximum 4 x :=
  Mixed65.paddedMinimalPoint.property x

example (net : Network 4 6 5) :
    net ∈ ExactSet 4 6 5 ↔ ∀ x : Fin 4 → ℝ, net.eval x = Maximum 4 x := Iff.rfl

example (net net' : ExactFiber 4 6 5) :
    quotientMk net = quotientMk net' ↔ EqvGen SymmetryStep net net' :=
  quotientMk_eq_iff net net'

example (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = Mixed65.firstRows t)
    (hmax : ∀ x : Fin 4 → ℝ, net.eval x = Maximum 4 x) :
    1 ≤ t * Mixed65.coefficientSize net :=
  Mixed65.physical_coefficient_bound net t ht hW hmax

example (h₁ h₂ : ℕ) :
    (∃ net : Network 4 h₁ h₂, ∀ x : Fin 4 → ℝ, net.eval x = Maximum 4 x) ↔
      6 ≤ h₁ ∧ 3 ≤ h₂ := Frontier.max4_widths_iff

#check @max4_6_5_at_least_two_components
#check @max4_6_5_witness_components_ne
#check @Mixed65.sector_isOpen
#check @Mixed65.normalizedCoefficientBound
#check @Mixed65.physical_coefficient_bound
#check @Mixed65.physical_three_gate_extraction

#print axioms max4_6_5_mixed_sector_isClopen
#print axioms max4_6_5_at_least_two_components
#print axioms max4_6_5_raw_at_least_two_components
#print axioms max4_6_5_quotient_not_preconnected
#print axioms max4_6_5_raw_not_preconnected
#print axioms max4_6_5_not_one_component
#print axioms max4_6_5_witness_components_ne
#print axioms Mixed65.physical_coefficient_bound
#print axioms Mixed65.sector_isOpen
#print axioms Mixed65.mixedPoint
#print axioms Mixed65.paddedMinimalPoint
#print axioms Frontier.max4_widths_iff
