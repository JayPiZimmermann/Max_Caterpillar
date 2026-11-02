import MaxCaterpillar.Fiber.Count65.Paired.Connected
set_option autoImplicit false
open Set MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open MaxCaterpillar.Fiber.Count65.Paired

example : IsPathConnected quotientSector := isPathConnected_quotientSector

example (z : ZeroBiasSymmetryQuotient 4 6 5) (hz : z ∈ quotientSector) :
    Joined z canonicalPairedEndpoint := quotientSector_joined_canonical z hz

example (x : ZeroBiasFiber 4 6 5) (U : Code) (hdet : codeDet U≠0)
    (hfirst : x.val.val.W₁=Paired.pairedRows U) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x) canonicalPairedEndpoint :=
  normalized_to_canonical x U hdet hfirst

/-- A genuine all-input network witnesses the geometric sector's nonemptiness. -/
example : canonicalPairedEndpoint ∈ quotientSector := canonicalPairedEndpoint_mem
example : (pairedMinimalNet identityCode).HasZeroBiases := pairedMinimalNet_zeroBias _
example : ∀ x,(pairedMinimalNet identityCode).eval x=Maximum 4 x :=
  pairedMinimalNet_eval identityCode (by rw [identityCode_det]; norm_num)

#print axioms normalized_to_canonical
#print axioms quotientSector_joined_canonical
#print axioms isPathConnected_quotientSector
#print axioms canonicalPairedEndpoint_mem
#print axioms network_atom_card_cases
