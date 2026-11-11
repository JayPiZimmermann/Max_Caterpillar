import MaxCaterpillar.Fiber.Count65.Mixed.ChartClassFibers
set_option autoImplicit false
open Set MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open MixedClassFibers MixedSectorComponents MixedQuotientCharts ActualMixedLabels Mixed65

example (b : Bool) (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected {p : Slice | p.val.2.HasZeroBiases ∧
      p ∈ physicalClass (Equiv.refl (Fin 5),b,bits,kind)} :=
  isPathConnected_orderedZeroClass b bits kind

example : Function.Surjective (componentLabel : Slice → Bool × (Fin 3 → Bool) × Bool) :=
  componentLabel_surjective

example (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz) ∈
      chartAQuotient (orientations l) '' headSectorA (orientations l) (signed l) :=
  classA_quotient_covered_kind p l hl hz hb

example (b : Bool) (bits : Fin 3 → Bool) (kind : Bool) :
    ∃ p : Slice,p.val.2.HasZeroBiases ∧
      p ∈ physicalClass (Equiv.refl (Fin 5),b,bits,kind) := by
  obtain ⟨p,hp,_⟩ := isPathConnected_orderedZeroClass b bits kind
  exact ⟨p,hp⟩

#print axioms orderedZeroClassA_eq_image
#print axioms orderedZeroClassB_eq_image
#print axioms isPathConnected_orderedZeroClass
#print axioms classA_quotient_covered_kind
#print axioms classB_quotient_covered_kind
#print axioms componentLabel_surjective
