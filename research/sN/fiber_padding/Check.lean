import research.sN.fiber_padding.Max465
import research.sN.fiber_padding.strong.Main

/-! Receipt: exact statements of the (6,5) reducibility results and their axioms. -/

open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Padding

/-- A component of the (6,5) quotient is reducible iff it is the paired component. -/
example (C : ConnectedComponents (SymmetryQuotient 4 6 5)) :
    IsReducibleComponent C ↔ C = pairedComponent :=
  isReducibleComponent_iff_eq_pairedComponent C

/-- The same with every definition unfolded. -/
example :
    ∃ C₀ : ConnectedComponents (SymmetryQuotient 4 6 5),
      ∀ C : ConnectedComponents (SymmetryQuotient 4 6 5),
        (∃ net : Network 4 6 5, ∃ hnet : ∀ x, net.eval x = Maximum 4 x,
          ((∃ j, (∀ k, net.W₂ k j = 0) ∨ ((∀ i, net.W₁ j i = 0) ∧ net.b₁ j = 0)) ∨
            ∃ k, net.w₃ k = 0 ∨ ((∀ j, net.W₂ k j = 0) ∧ net.b₂ k = 0)) ∧
          ((quotientMk ⟨net, hnet⟩ : SymmetryQuotient 4 6 5) :
            ConnectedComponents (SymmetryQuotient 4 6 5)) = C) ↔ C = C₀ :=
  max4_6_5_exactly_one_reducible_component

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // IsReducibleComponent C} = 1 :=
  max4_6_5_reducible_component_count

example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) // ¬ IsReducibleComponent C}
      = 64 :=
  max4_6_5_irreducible_component_count

/-- With the stronger notion: no network in the 64 other components is an expansion
(zero padding, duplication with split outgoing weights, and compositions) of an exact
network of a strictly smaller architecture. -/
example :
    Nat.card {C : ConnectedComponents (SymmetryQuotient 4 6 5) //
      ∀ net : ExactFiber 4 6 5,
        ((quotientMk net : SymmetryQuotient 4 6 5) :
          ConnectedComponents (SymmetryQuotient 4 6 5)) = C →
        ¬ Strong.IsExpandedSolution net.val} = 64 :=
  Strong.Main.max4_6_5_exactly_64_components_without_expandedSolution

#print axioms isReducibleComponent_iff_eq_pairedComponent
#print axioms max4_6_5_exactly_one_reducible_component
#print axioms max4_6_5_reducible_component_count
#print axioms max4_6_5_irreducible_component_count
#print axioms Strong.Main.max4_6_5_exactly_64_components_without_expandedSolution
