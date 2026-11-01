import MaxCaterpillar.Fiber.Disconnected65

open MaxCaterpillar.Fiber

-- These types have no hypotheses about normal forms, coefficient bounds,
-- topology, data, or the absence of biases.
example : Nontrivial (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_at_least_two_components
example : Nontrivial (ConnectedComponents (ExactFiber 4 6 5)) :=
  max4_6_5_raw_at_least_two_components
example : ¬ PreconnectedSpace (SymmetryQuotient 4 6 5) :=
  max4_6_5_quotient_not_preconnected
example : ¬ PreconnectedSpace (ExactFiber 4 6 5) :=
  max4_6_5_raw_not_preconnected
example : ¬ HasComponentCount 4 6 5 1 := max4_6_5_not_one_component
example :
    (quotientMk Mixed65.mixedPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) ≠
    (quotientMk Mixed65.paddedMinimalPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  max4_6_5_witness_components_ne

#print axioms max4_6_5_mixed_sector_isClopen
#print axioms max4_6_5_at_least_two_components
#print axioms max4_6_5_raw_at_least_two_components
#print axioms max4_6_5_quotient_not_preconnected
#print axioms max4_6_5_raw_not_preconnected
#print axioms max4_6_5_not_one_component
#print axioms max4_6_5_witness_components_ne
