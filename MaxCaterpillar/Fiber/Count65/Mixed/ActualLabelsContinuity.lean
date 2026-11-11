import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsExhaustion
import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSeparation
import MaxCaterpillar.Fiber.Count65.FiniteClosedPartition

/-! # Actual continuous mixed physical labels

The full normalized physical first-row slice has an exhaustive, unique finite
closed partition. The label is therefore continuous in the ordinary topology
of all its actual coefficients, including arbitrary original biases.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function

instance labelTopologicalSpace : TopologicalSpace Label := ⊥
instance labelDiscreteTopology : DiscreteTopology Label := ⟨rfl⟩

theorem physicalClass_unique (p : Slice) (l m : Label)
    (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) : l=m :=
  physicalClass_unique_of_normalForm (normalForm p) hl hm

noncomputable def actualLabel : Slice → Label :=
  FiniteClosedPartition.classify physicalClass physicalClasses_exhaustive

lemma actualLabel_mem (p : Slice) : p ∈ physicalClass (actualLabel p) :=
  FiniteClosedPartition.classify_mem physicalClass physicalClasses_exhaustive p

lemma actualLabel_eq_iff (p : Slice) (l : Label) : actualLabel p=l ↔ p ∈ physicalClass l :=
  FiniteClosedPartition.classify_eq_iff physicalClass physicalClasses_exhaustive
    physicalClass_unique p l

theorem isClopen_physicalClass (l : Label) : IsClopen (physicalClass l) :=
  FiniteClosedPartition.isClopen_class physicalClass isClosed_physicalClass
    physicalClasses_exhaustive physicalClass_unique l

/-- Continuous labels are derived on the actual physical domain, without
assuming continuity of any normal-form choice. -/
theorem continuous_actualLabel : Continuous actualLabel :=
  FiniteClosedPartition.continuous_classify physicalClass isClosed_physicalClass
    physicalClasses_exhaustive physicalClass_unique

/-- The branch, three orientations and head kind, with finite physical row
names forgotten. Its 32 labels are not yet the full-network count. -/
noncomputable def componentLabel (p : Slice) : NonpairedLabel := (actualLabel p).2

theorem continuous_componentLabel : Continuous componentLabel :=
  (continuous_of_discreteTopology : Continuous (fun l : Label => l.2)).comp
    continuous_actualLabel

#print axioms physicalClass_unique
#print axioms continuous_actualLabel
#print axioms continuous_componentLabel
end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
