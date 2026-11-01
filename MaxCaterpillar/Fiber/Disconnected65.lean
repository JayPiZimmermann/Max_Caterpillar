import MaxCaterpillar.Fiber.Mixed65.Open
import MaxCaterpillar.Fiber.Mixed65.Boundary
import MaxCaterpillar.Fiber.Mixed65.PhysicalBlowup
import MaxCaterpillar.Fiber.Mixed65.SeparationWitnesses

/-! # The full Max4 (6,5) fiber is disconnected, including after symmetries

All parameters are arbitrary real numbers, all biases are allowed, and exactness
means equality to Max4 on every real input. The quotient identifies positive
rescaling in both hidden layers, both hidden-neuron permutations, and input
permutations, with the quotient of the ordinary parameter topology.

The mixed first-layer sector is nonempty, proper, invariant, open by finite
first-layer rigidity, and closed by an unbounded-coefficient obstruction at its
only possible finite boundary. Its clopen image separates the quotient.

These are lower-bound results: no exact count of 65 components is asserted.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

/-- The mixed sector is clopen in the full exact biased parameter fiber. -/
theorem max4_6_5_mixed_sector_isClopen : IsClopen Mixed65.sector :=
  ⟨Mixed65.sector_isOpen,
    Mixed65.isClosed_sector_of_coefficient_bound Mixed65.normalizedCoefficientBound⟩

/-- The full (6,5) Max4 fiber has at least two connected components after
positive scaling, hidden-neuron permutations, and input permutations. -/
theorem max4_6_5_at_least_two_components :
    Nontrivial (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  symmetryQuotient_nontrivial_components_of_isClopen Mixed65.sector_invariant
    max4_6_5_mixed_sector_isClopen Mixed65.sector_nonempty Mixed65.sector_compl_nonempty

/-- The same lower bound holds before quotienting any symmetry. -/
theorem max4_6_5_raw_at_least_two_components :
    Nontrivial (ConnectedComponents (ExactFiber 4 6 5)) :=
  nontrivial_connectedComponents_of_isClopen max4_6_5_mixed_sector_isClopen
    Mixed65.sector_nonempty Mixed65.sector_compl_nonempty

/-- The exact symmetry quotient is not even preconnected. -/
theorem max4_6_5_quotient_not_preconnected :
    ¬ PreconnectedSpace (SymmetryQuotient 4 6 5) :=
  not_preconnectedSpace_of_nontrivial_components max4_6_5_at_least_two_components

/-- The ordinary full parameter fiber is not even preconnected. -/
theorem max4_6_5_raw_not_preconnected :
    ¬ PreconnectedSpace (ExactFiber 4 6 5) :=
  not_preconnectedSpace_of_nontrivial_components max4_6_5_raw_at_least_two_components

/-- In the exact-count terminology, a single quotient component is impossible. -/
theorem max4_6_5_not_one_component : ¬ HasComponentCount 4 6 5 1 :=
  not_hasComponentCount_one_of_nontrivial max4_6_5_at_least_two_components

/-- The explicit mixed network and the padded minimal construction belong to
different connected components even after all the stated symmetries. -/
theorem max4_6_5_witness_components_ne :
    (quotientMk Mixed65.mixedPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) ≠
      (quotientMk Mixed65.paddedMinimalPoint : ConnectedComponents (SymmetryQuotient 4 6 5)) := by
  let S := quotientMk '' Mixed65.sector
  have hs : IsClopen S := isClopen_image_of_saturated quotientMk_quotientMap
    (fun x y hxy => Mixed65.sector_invariant x y ((quotientMk_eq_iff x y).mp hxy))
    max4_6_5_mixed_sector_isClopen
  have hin : quotientMk Mixed65.mixedPoint ∈ S :=
    ⟨Mixed65.mixedPoint, Mixed65.mixedPoint_mem_sector, rfl⟩
  have hout : quotientMk Mixed65.paddedMinimalPoint ∉ S := by
    rintro ⟨x, hx, hxy⟩
    exact Mixed65.paddedMinimalPoint_not_mem_sector
      ((Mixed65.sector_invariant x Mixed65.paddedMinimalPoint
        ((quotientMk_eq_iff x Mixed65.paddedMinimalPoint).mp hxy)).mp hx)
  intro heq
  have hmem : quotientMk Mixed65.paddedMinimalPoint ∈
      connectedComponent (quotientMk Mixed65.mixedPoint) :=
    ConnectedComponents.coe_eq_coe'.mp heq.symm
  exact hout (hs.connectedComponent_subset hin hmem)

end MaxCaterpillar.Fiber
