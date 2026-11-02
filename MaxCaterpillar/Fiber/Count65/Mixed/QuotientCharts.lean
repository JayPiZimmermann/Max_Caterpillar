import MaxCaterpillar.Fiber.Count65.SectorComponents
import MaxCaterpillar.Fiber.Count65.Mixed.ActualChartCoverage
import MaxCaterpillar.Fiber.BiasQuotient

/-! # Actual mixed charts in the genuine zero-bias symmetry quotient -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.MixedQuotientCharts
open Set Mixed65 ActualMixedLabels MixedSectorComponents

noncomputable def chartAZeroBias (bits : Fin 3 → Bool) (p : ResidualHeadChartA bits) :
    ZeroBiasFiber 4 6 5 :=
  ⟨⟨chartNetA bits p,chartNetA_exact bits p⟩,residualLift_hasZeroBiases _ _ _ _ _⟩
noncomputable def chartBZeroBias (bits : Fin 3 → Bool) (p : ResidualHeadChartB bits) :
    ZeroBiasFiber 4 6 5 :=
  ⟨⟨chartNetB bits p,chartNetB_exact bits p⟩,residualLift_hasZeroBiases _ _ _ _ _⟩

lemma continuous_chartAZeroBias (bits : Fin 3 → Bool) : Continuous (chartAZeroBias bits) :=
  ((continuous_chartNetA bits).subtype_mk _).subtype_mk _
lemma continuous_chartBZeroBias (bits : Fin 3 → Bool) : Continuous (chartBZeroBias bits) :=
  ((continuous_chartNetB bits).subtype_mk _).subtype_mk _

noncomputable def chartAQuotient (bits : Fin 3 → Bool) (p : ResidualHeadChartA bits) :
    ZeroBiasSymmetryQuotient 4 6 5 := Quotient.mk _ (chartAZeroBias bits p)
noncomputable def chartBQuotient (bits : Fin 3 → Bool) (p : ResidualHeadChartB bits) :
    ZeroBiasSymmetryQuotient 4 6 5 := Quotient.mk _ (chartBZeroBias bits p)

lemma continuous_chartAQuotient (bits : Fin 3 → Bool) : Continuous (chartAQuotient bits) :=
  continuous_quotient_mk'.comp (continuous_chartAZeroBias bits)
lemma continuous_chartBQuotient (bits : Fin 3 → Bool) : Continuous (chartBQuotient bits) :=
  continuous_quotient_mk'.comp (continuous_chartBZeroBias bits)

theorem isPathConnected_quotientChartA (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartAQuotient bits '' headSectorA bits kind) :=
  (isPathConnected_headSectorA bits kind).image (continuous_chartAQuotient bits)
theorem isPathConnected_quotientChartB (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartBQuotient bits '' headSectorB bits kind) :=
  (isPathConnected_headSectorB bits kind).image (continuous_chartBQuotient bits)

def physicalZeroBias (p : Slice) (hz : p.val.2.HasZeroBiases) : ZeroBiasFiber 4 6 5 :=
  ⟨⟨p.val.2,p.property.2.2.1⟩,hz⟩

/-- Per-class exact coverage uses a genuine hidden-neuron permutation. -/
theorem classA_quotient_covered (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    ∃ q : ResidualHeadChartA (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=
        chartAQuotient (orientations l) q := by
  obtain ⟨q,ht,hh,hnet⟩ := physicalClass_chartA p l hl hz hb
  refine ⟨q,ht,hh,Quotient.sound ?_⟩
  change (symmetrySetoid 4 6 5).r (includeZeroBias (physicalZeroBias p hz))
    (includeZeroBias (chartAZeroBias (orientations l) q))
  have he : permuteHiddenFiber (Equiv.refl _) (rowOrder l)
      (includeZeroBias (physicalZeroBias p hz))=
      includeZeroBias (chartAZeroBias (orientations l) q) := Subtype.ext hnet
  rw [← he]
  exact EqvGen.rel _ _ (SymmetryStep.hidden _ (Equiv.refl _) (rowOrder l))

theorem classB_quotient_covered (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=true) :
    ∃ q : ResidualHeadChartB (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=
        chartBQuotient (orientations l) q := by
  obtain ⟨q,ht,hh,hnet⟩ := physicalClass_chartB p l hl hz hb
  refine ⟨q,ht,hh,Quotient.sound ?_⟩
  change (symmetrySetoid 4 6 5).r (includeZeroBias (physicalZeroBias p hz))
    (includeZeroBias (chartBZeroBias (orientations l) q))
  have he : permuteHiddenFiber (Equiv.refl _) (rowOrder l)
      (includeZeroBias (physicalZeroBias p hz))=
      includeZeroBias (chartBZeroBias (orientations l) q) := Subtype.ext hnet
  rw [← he]
  exact EqvGen.rel _ _ (SymmetryStep.hidden _ (Equiv.refl _) (rowOrder l))

/-- Every actual zero-bias canonical mixed network is covered in the genuine
quotient, with no branch, orientation, or normal-form assumption. -/
theorem zeroBias_quotient_coverage (p : Slice) (hz : p.val.2.HasZeroBiases) :
    ∃ bits : Fin 3 → Bool,
      (∃ q : ResidualHeadChartA bits,
        Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartAQuotient bits q) ∨
      (∃ q : ResidualHeadChartB bits,
        Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartBQuotient bits q) := by
  obtain ⟨l,hl⟩ := physicalClasses_exhaustive p
  refine ⟨orientations l,?_⟩
  cases hb : branch l
  · obtain ⟨q,_,_,he⟩ := classA_quotient_covered p l hl hz hb
    exact Or.inl ⟨q,he⟩
  · obtain ⟨q,_,_,he⟩ := classB_quotient_covered p l hl hz hb
    exact Or.inr ⟨q,he⟩

#print axioms isPathConnected_quotientChartA
#print axioms isPathConnected_quotientChartB
#print axioms classA_quotient_covered
#print axioms classB_quotient_covered
#print axioms zeroBias_quotient_coverage
end MaxCaterpillar.Fiber.Count65.MixedQuotientCharts
