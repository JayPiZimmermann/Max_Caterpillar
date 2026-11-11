import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsNormalization

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open PhysicalExtraction

def rawExactFiber (p : RawSlice) : ExactFiber 4 6 5 := ⟨p.val.2,p.property.2.2⟩
noncomputable def normalizedExactFiber (p : RawSlice) : ExactFiber 4 6 5 :=
  ⟨(normalizePhysical p).val.2,(normalizePhysical p).property.2.2.1⟩

/-- The normalization is an actual permitted positive hidden-neuron scaling. -/
theorem normalizePhysical_symmetry (p : RawSlice) :
    (symmetrySetoid 4 6 5).r (rawExactFiber p) (normalizedExactFiber p) :=
  EqvGen.rel _ _ (SymmetryStep.second (rawExactFiber p) (fun k => |p.val.2.w₃ k|)
    (fun k => abs_pos.mpr (raw_outputs_nonzero p k)))

theorem normalizePhysical_sameQuotient (p : RawSlice) :
    quotientMk (normalizedExactFiber p)=quotientMk (rawExactFiber p) :=
  (Quotient.sound (normalizePhysical_symmetry p)).symm

#print axioms normalizePhysical_symmetry
#print axioms normalizePhysical_sameQuotient
end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
