import MaxCaterpillar.Fiber.Count65.Mixed.ActualChartClass
import MaxCaterpillar.Fiber.Count65.Mixed.QuotientCharts

/-! # Complete actual mixed physical classes are connected chart images -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.MixedClassFibers
open Set Mixed65 ActualMixedLabels MixedSectorComponents MixedQuotientCharts

def orderedZeroClass (branch : Bool) (bits : Fin 3 → Bool) (kind : Bool) : Set Slice :=
  {p | p.val.2.HasZeroBiases ∧ p ∈ physicalClass (Equiv.refl (Fin 5),branch,bits,kind)}

/-- This is equality of sets of all physical coefficients; the reverse
inclusion uses the exact derived normal form and literal network coverage. -/
theorem orderedZeroClassA_eq_image (bits : Fin 3 → Bool) (kind : Bool) :
    orderedZeroClass false bits kind=chartA bits '' headSectorA bits kind := by
  ext p
  constructor
  · rintro ⟨hz,hl⟩
    obtain ⟨q,hq,ht,hnet⟩ := physicalClass_chartA_in_headSector p
      (Equiv.refl (Fin 5),false,bits,kind) hl hz rfl
    refine ⟨q,hq,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ht
    · change chartNetA bits q=p.val.2
      change p.val.2=chartNetA bits q at hnet
      exact hnet.symm
  · rintro ⟨q,hq,rfl⟩
    exact ⟨residualLift_hasZeroBiases _ _ _ _ _,chartA_mem_physicalClass bits kind q hq⟩

theorem orderedZeroClassB_eq_image (bits : Fin 3 → Bool) (kind : Bool) :
    orderedZeroClass true bits kind=chartB bits '' headSectorB bits kind := by
  ext p
  constructor
  · rintro ⟨hz,hl⟩
    obtain ⟨q,hq,ht,hnet⟩ := physicalClass_chartB_in_headSector p
      (Equiv.refl (Fin 5),true,bits,kind) hl hz rfl
    refine ⟨q,hq,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ht
    · change chartNetB bits q=p.val.2
      change p.val.2=chartNetB bits q at hnet
      exact hnet.symm
  · rintro ⟨q,hq,rfl⟩
    exact ⟨residualLift_hasZeroBiases _ _ _ _ _,chartB_mem_physicalClass bits kind q hq⟩

/-- All actual zero-bias physical parameters in each ordered class, including
the complete parameter boundary and head freedom, form one path component. -/
theorem isPathConnected_orderedZeroClass (branch : Bool) (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (orderedZeroClass branch bits kind) := by
  cases branch
  · rw [orderedZeroClassA_eq_image]
    exact isPathConnected_actualChartA bits kind
  · rw [orderedZeroClassB_eq_image]
    exact isPathConnected_actualChartB bits kind

/-- The exact given physical class is covered by its matching connected
head-kind image in the genuine symmetry quotient. -/
theorem classA_quotient_covered_kind (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz) ∈
      chartAQuotient (orientations l) '' headSectorA (orientations l) (signed l) := by
  obtain ⟨q,_,hD,hQ⟩ := classA_quotient_covered p l hl hz hb
  exact ⟨q,headSectorA_of_actualData p l hl q hD,hQ.symm⟩

theorem classB_quotient_covered_kind (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=true) :
    Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz) ∈
      chartBQuotient (orientations l) '' headSectorB (orientations l) (signed l) := by
  obtain ⟨q,_,hD,hQ⟩ := classB_quotient_covered p l hl hz hb
  exact ⟨q,headSectorB_of_actualData p l hl q hD,hQ.symm⟩

/-- All 32 actual branch/orientation/head-kind values are attained. -/
theorem componentLabel_surjective : Function.Surjective componentLabel := by
  rintro ⟨b,bits,kind⟩
  cases b
  · obtain ⟨q,hq,_⟩ := isPathConnected_headSectorA bits kind
    exact ⟨chartA bits q,componentLabel_chartA bits kind q hq⟩
  · obtain ⟨q,hq,_⟩ := isPathConnected_headSectorB bits kind
    exact ⟨chartB bits q,componentLabel_chartB bits kind q hq⟩

#print axioms orderedZeroClassA_eq_image
#print axioms orderedZeroClassB_eq_image
#print axioms isPathConnected_orderedZeroClass
#print axioms classA_quotient_covered_kind
#print axioms classB_quotient_covered_kind
#print axioms componentLabel_surjective
end MaxCaterpillar.Fiber.Count65.MixedClassFibers
