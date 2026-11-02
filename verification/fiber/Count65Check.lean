import MaxCaterpillar.Fiber.Count65
set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Fiber

/-- The expected carrier is all actual real networks computing Max4 on every
real input. No zero-bias, genericity, normal-form or regularity restriction. -/
abbrev ActualMax4Fiber :=
  {net : Network 4 6 5 // ∀ x : Fin 4 → ℝ,net.eval x=Maximum 4 x}

/-- Exactly the original positive-scaling/hidden/input permutation generators;
no equality-of-functions or normal-form identification is added. -/
def ActualMax4Symmetries : Setoid ActualMax4Fiber where
  r := EqvGen (SymmetryStep : ActualMax4Fiber → ActualMax4Fiber → Prop)
  iseqv := EqvGen.is_equivalence _

example : Nonempty (ConnectedComponents (Quotient ActualMax4Symmetries) ≃ Fin 65) :=
  max4_6_5_has_65_components
example : Nat.card (ConnectedComponents (Quotient ActualMax4Symmetries))=65 :=
  max4_6_5_component_count_eq_65
example : HasComponentCount 4 6 5 65 := max4_6_5_has_65_components

example : IsPathConnected Count65.Paired.quotientSector :=
  Count65.Paired.isPathConnected_quotientSector
example : ∀ l : Count65.NonpairedLabel,
    IsPathConnected (Count65.SectorQuotient.mixedZeroBiasLabel ⁻¹' {some l}) :=
  Count65.MixedFullSectorComponents.isPathConnected_mixedLabel_fiber
example : ∀ l : Count65.NonpairedLabel,
    IsPathConnected (Count65.SectorQuotient.starZeroBiasLabel ⁻¹' {some l}) :=
  Count65.ActualStarLabels.isPathConnected_starLabel_fiber

#check @max4_6_5_has_65_components
#print axioms max4_6_5_has_65_components
#print axioms max4_6_5_component_count_eq_65
#print axioms Count65.zeroBiasComponentsEquiv65
#print axioms Count65.fullComponentsEquiv65
#print axioms Count65.Paired.isPathConnected_quotientSector
#print axioms Count65.MixedFullSectorComponents.mixed_actual_sector_has_32_components
#print axioms Count65.StarFullSectorComponents.star_actual_sector_has_32_components
#print axioms Count65.globalLabel_surjective
#print axioms zeroBiasQuotientConnectedComponentsEquiv
