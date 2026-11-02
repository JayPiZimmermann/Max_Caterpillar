import MaxCaterpillar.Fiber.Count65.Mixed.GeometricComponents
set_option autoImplicit false
open Set MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open MixedFullSectorComponents

/-- The expected domain is the literal image of actual zero-bias exact
networks under the allowed symmetry quotient; all positive first scales and
all hidden/input permutations appear in the first-matrix predicate. -/
example : Nonempty (ConnectedComponents
    (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ''
      {x : ZeroBiasFiber 4 6 5 |
        ∃ t : ℝ,0<t ∧ ∃ c : Fin 6 → ℝ,(∀ j,0<c j) ∧
          ∃ p : Equiv.Perm (Fin 6),∃ q : Equiv.Perm (Fin 4),
            ∀ j i,x.val.val.W₁ j i=c j*Mixed65.firstRows t (p j) (q i)}) ≃ Fin 32) :=
  mixed_actual_sector_has_32_components

example (l : NonpairedLabel) :
    IsPathConnected (SectorQuotient.mixedZeroBiasLabel ⁻¹' {some l}) :=
  isPathConnected_mixedLabel_fiber l

example (l : NonpairedLabel) : ∃ z : ZeroBiasSymmetryQuotient 4 6 5,
    SectorQuotient.mixedZeroBiasLabel z=some l := by
  obtain ⟨z,hz,_⟩ := isPathConnected_mixedLabel_fiber l
  exact ⟨z,hz⟩

#print axioms mixedLabel_fiber
#print axioms mixed_sector_has_32_components
#print axioms mixedSome_iff_mem_image
#print axioms mixed_actual_sector_has_32_components
