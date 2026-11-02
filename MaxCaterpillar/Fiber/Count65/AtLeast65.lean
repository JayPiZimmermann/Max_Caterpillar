import MaxCaterpillar.Fiber.Count65.AtLeast65.ComponentsLower
import MaxCaterpillar.Fiber.Count65.AtLeast65.PairedWitness
import MaxCaterpillar.Fiber.Count65.Mixed.FullSectorComponents
import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.Attainment

/-! # At least 65 genuine symmetry-quotient components of the full Max4 fiber

The lower bound follows from an actual continuous surjective 65-valued label.
No connectedness or finiteness of any sector is assumed. In particular these
statements remain valid if further connected components exist.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65
open SectorQuotient

/-- Every proposed component label is attained by an actual zero-bias network,
projected through precisely the original allowed physical symmetries. -/
theorem globalLabel_surjective : Function.Surjective globalLabel := by
  apply globalLabel_surjective_of_attainment
  · intro l
    obtain ⟨z,hz,_⟩ := MixedFullSectorComponents.isPathConnected_mixedLabel_fiber l
    exact ⟨z,hz⟩
  · exact StarAttainment.starZeroBiasLabel_attained
  · exact ⟨AtLeast65.pairedWitness,AtLeast65.pairedWitness_mixedLabel,
      AtLeast65.pairedWitness_starLabel⟩

theorem globalLabelFin65_surjective : Function.Surjective globalLabelFin65 :=
  componentLabelEquivFin65.surjective.comp globalLabel_surjective

/-- The actual connected-component space maps onto all 65 labels. -/
theorem zeroBiasComponentProjection65_surjective : Function.Surjective zeroBiasComponentProjection65 :=
  zeroBiasComponentProjection65_surjective_of_label globalLabelFin65_surjective

theorem fullComponentProjection65_surjective : Function.Surjective fullComponentProjection65 :=
  fullComponentProjection65_surjective_of_label globalLabelFin65_surjective

/-- Sixty-five distinct zero-bias quotient connected components, without a
finiteness assumption. -/
noncomputable def zeroBiasComponentsEmbedding65 :
    Fin 65 ↪ ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5) :=
  zeroBiasComponentsEmbedding65_of_label globalLabelFin65_surjective

/-- Allowing arbitrary biases preserves this lower bound after quotienting. -/
noncomputable def fullComponentsEmbedding65 :
    Fin 65 ↪ ConnectedComponents (SymmetryQuotient 4 6 5) :=
  fullComponentsEmbedding65_of_label globalLabelFin65_surjective

theorem zeroBias_components_cardinal_lower :
    (65 : Cardinal) ≤ Cardinal.mk (ConnectedComponents (ZeroBiasSymmetryQuotient 4 6 5)) :=
  zeroBias_components_cardinal_lower_of_label globalLabelFin65_surjective

theorem full_components_cardinal_lower :
    (65 : Cardinal) ≤ Cardinal.mk (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  full_components_cardinal_lower_of_label globalLabelFin65_surjective

#print axioms globalLabel_surjective
#print axioms globalLabelFin65_surjective
#print axioms fullComponentsEmbedding65
#print axioms full_components_cardinal_lower
end MaxCaterpillar.Fiber.Count65

namespace MaxCaterpillar.Fiber

/-- The complete arbitrary-bias Max4 (6,5) fiber, modulo all stated positive
scalings and hidden/input permutations, has at least 65 connected components. -/
theorem max4_6_5_at_least_65_components :
    Nonempty (Fin 65 ↪ ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  ⟨Count65.fullComponentsEmbedding65⟩

theorem max4_6_5_component_cardinal_lower :
    (65 : Cardinal) ≤ Cardinal.mk (ConnectedComponents (SymmetryQuotient 4 6 5)) :=
  Count65.full_components_cardinal_lower

#print axioms max4_6_5_at_least_65_components
#print axioms max4_6_5_component_cardinal_lower
end MaxCaterpillar.Fiber
