import MaxCaterpillar.Fiber.Count65.Star.ChartClassFibers
import MaxCaterpillar.Fiber.Count65.SomeFiberComponents

/-! # Exact32 in the actual geometric star sector of the physical quotient -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.StarFullSectorComponents
open Set SectorQuotient

abbrev StarQuotientSector := SomeFiberComponents.Sector starZeroBiasLabel

noncomputable def starComponentsEquiv : ConnectedComponents StarQuotientSector ≃ NonpairedLabel :=
  SomeFiberComponents.componentsEquiv starZeroBiasLabel continuous_starZeroBiasLabel
    ActualStarLabels.isPathConnected_starLabel_fiber

theorem star_sector_has_32_components :
    Nonempty (ConnectedComponents StarQuotientSector ≃ Fin 32) :=
  ⟨starComponentsEquiv.trans (Fintype.equivFinOfCardEq nonpairedLabel_card)⟩

/-- The genuine quotient image of all actual star first matrices, including
r=1 and every positive hidden scaling and hidden/input permutation. -/
def starQuotientImage : Set (ZeroBiasSymmetryQuotient 4 6 5) :=
  Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ''
    {x : ZeroBiasFiber 4 6 5 | StarFirstMatrixForm x.val.val}

lemma starSome_iff_mem_image (z : ZeroBiasSymmetryQuotient 4 6 5) :
    (∃ l,starZeroBiasLabel z=some l) ↔ z ∈ starQuotientImage := by
  induction z using Quotient.inductionOn with
  | h x =>
    constructor
    · rintro ⟨l,hl⟩
      have hx : includeZeroBias x ∈ starSet := by
        by_contra hn
        have he := (starZeroBiasLabel_none_iff x).mpr hn
        rw [hl] at he
        cases he
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      rw [← he]
      cases hv : starZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) y) with
      | none => exact ((starZeroBiasLabel_none_iff y).mp hv hy).elim
      | some l => exact ⟨l,rfl⟩

noncomputable def starGeometricHomeomorph : StarQuotientSector ≃ₜ starQuotientImage :=
  Homeomorph.setCongr (Set.ext starSome_iff_mem_image)

/-- The full actual star zero-bias quotient sector has exactly32 components.
No normal-form or continuous-classifier hypothesis is an input. -/
theorem star_actual_sector_has_32_components :
    Nonempty (ConnectedComponents starQuotientImage ≃ Fin 32) := by
  obtain ⟨e⟩ := star_sector_has_32_components
  exact ⟨(connectedComponentsEquivOfHomeomorph starGeometricHomeomorph).symm.trans e⟩

#print axioms star_sector_has_32_components
#print axioms star_actual_sector_has_32_components
end MaxCaterpillar.Fiber.Count65.StarFullSectorComponents
