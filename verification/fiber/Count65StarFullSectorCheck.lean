import MaxCaterpillar.Fiber.Count65.Star.FullSectorComponents
set_option autoImplicit false
open Set MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open StarFullSectorComponents

/-- The actual geometric star quotient image includes its r=1 endpoint,
all strictly positive physical row scales, and hidden/input permutations. -/
example : Nonempty (ConnectedComponents
    (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ''
      {x : ZeroBiasFiber 4 6 5 |
        ∃ r : ℝ,0<r ∧ r≤1 ∧ ∃ s : Fin 6 → ℝ,(∀ j,0<s j) ∧
          ∃ p : Equiv.Perm (Fin 6),∃ q : Equiv.Perm (Fin 4),
            ∀ j i,x.val.val.W₁ j i=s j*Star65.firstRows r (p j) (q i)}) ≃ Fin 32) :=
  star_actual_sector_has_32_components

example (l : NonpairedLabel) :
    IsPathConnected (SectorQuotient.starZeroBiasLabel ⁻¹' {some l}) :=
  ActualStarLabels.isPathConnected_starLabel_fiber l
example (l : NonpairedLabel) : ∃ z : ZeroBiasSymmetryQuotient 4 6 5,
    SectorQuotient.starZeroBiasLabel z=some l := by
  obtain ⟨z,hz,_⟩ := ActualStarLabels.isPathConnected_starLabel_fiber l
  exact ⟨z,hz⟩

#print axioms SomeFiberComponents.componentsEquiv
#print axioms ActualStarLabels.starLabel_fiber
#print axioms ActualStarLabels.isPathConnected_starLabel_fiber
#print axioms star_sector_has_32_components
#print axioms star_actual_sector_has_32_components
