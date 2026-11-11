import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairedClosed
import MaxCaterpillar.Fiber.Count65.SectorSeparation.StarClosed
import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairedInvariance
import MaxCaterpillar.Fiber.Count65.SectorSeparation.StarInvariance

/-! # The actual paired and star sectors are closed and symmetry invariant

Both conclusions concern the complete all-input exact physical fiber with
arbitrary biases. They impose only the displayed first-matrix property.
Neither conclusion assumes exhaustive classification of exact networks.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65

/-- Closedness of the full independent paired-code first-matrix sector. -/
theorem isClosed_pairedFirstMatrixForm :
    IsClosed {net : ExactFiber 4 6 5 | PairedFirstMatrixForm net.val} :=
  SectorSeparation.isClosed_pairedFirstMatrixForm

/-- Closedness of the full positive-path/star first-matrix sector. -/
theorem isClosed_starFirstMatrixForm :
    IsClosed {net : ExactFiber 4 6 5 | StarFirstMatrixForm net.val} :=
  SectorSeparation.StarClosed.isClosed_starFirstMatrixForm

/-- The actual paired sector respects every symmetry of the requested quotient. -/
theorem pairedFirstMatrixForm_symmetryInvariant :
    SymmetryInvariant {net : ExactFiber 4 6 5 | PairedFirstMatrixForm net.val} := by
  intro a b h
  exact SectorSeparation.pairedFirstMatrixForm_of_symmetry h

/-- The actual star sector respects every symmetry of the requested quotient. -/
theorem starFirstMatrixForm_symmetryInvariant :
    SymmetryInvariant {net : ExactFiber 4 6 5 | StarFirstMatrixForm net.val} := by
  intro a b h
  exact SectorSeparation.starFirstMatrixForm_of_symmetry h

#print axioms isClosed_pairedFirstMatrixForm
#print axioms isClosed_starFirstMatrixForm
#print axioms pairedFirstMatrixForm_symmetryInvariant
#print axioms starFirstMatrixForm_symmetryInvariant
end MaxCaterpillar.Fiber.Count65
