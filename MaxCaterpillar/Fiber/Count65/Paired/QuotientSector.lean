import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.BiasQuotient

/-! # The actual paired sector in the genuine zero-bias physical quotient -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Paired

/-- Every actual paired first matrix is allowed, including arbitrary independent
real code rows, all suffix coefficients, and every stated physical symmetry. -/
def quotientSector : Set (ZeroBiasSymmetryQuotient 4 6 5) :=
  Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) ''
    {x : ZeroBiasFiber 4 6 5 | PairedFirstMatrixForm x.val.val}

end MaxCaterpillar.Fiber.Count65.Paired
