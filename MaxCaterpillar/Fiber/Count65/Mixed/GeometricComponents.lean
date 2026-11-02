import MaxCaterpillar.Fiber.Count65.Mixed.FullSectorComponents

/-! # Exact component count for the actual geometric mixed quotient sector -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.MixedFullSectorComponents
open Set Mixed65 SectorQuotient

/-- The image of actual zero-bias networks with the mixed first-matrix form
under the quotient by precisely the permitted physical symmetries. -/
def mixedQuotientImage : Set (ZeroBiasSymmetryQuotient 4 6 5) :=
  Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ''
    {x : ZeroBiasFiber 4 6 5 | FirstMatrixForm x.val.val}

lemma mixedSome_iff_mem_image (z : ZeroBiasSymmetryQuotient 4 6 5) :
    (∃ l,mixedZeroBiasLabel z=some l) ↔ z ∈ mixedQuotientImage := by
  induction z using Quotient.inductionOn with
  | h x =>
    constructor
    · rintro ⟨l,hl⟩
      have hx : includeZeroBias x ∈ sector := by
        by_contra hn
        have he := (mixedZeroBiasLabel_none_iff x).mpr hn
        rw [hl] at he
        cases he
      exact ⟨x,(mem_sector_iff_firstMatrixForm _).mp hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      rw [← he]
      cases hv : mixedZeroBiasLabel (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) y) with
      | none =>
        exact ((mixedZeroBiasLabel_none_iff y).mp hv
          ((mem_sector_iff_firstMatrixForm _).mpr hy)).elim
      | some l => exact ⟨l,rfl⟩

noncomputable def mixedGeometricHomeomorph : MixedQuotientSector ≃ₜ mixedQuotientImage :=
  Homeomorph.setCongr (Set.ext mixedSome_iff_mem_image)

/-- Exactly 32 connected components in the actual mixed part of the genuine
zero-bias physical symmetry quotient, with the geometric first-matrix
predicate rather than a classifier-built domain. -/
theorem mixed_actual_sector_has_32_components :
    Nonempty (ConnectedComponents mixedQuotientImage ≃ Fin 32) := by
  obtain ⟨e⟩ := mixed_sector_has_32_components
  exact ⟨(connectedComponentsEquivOfHomeomorph mixedGeometricHomeomorph).symm.trans e⟩

#print axioms mixedSome_iff_mem_image
#print axioms mixed_actual_sector_has_32_components
end MaxCaterpillar.Fiber.Count65.MixedFullSectorComponents
