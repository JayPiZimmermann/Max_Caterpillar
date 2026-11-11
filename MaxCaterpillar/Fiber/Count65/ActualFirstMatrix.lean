import MaxCaterpillar.Fiber.Count65.FourRootClassification
import MaxCaterpillar.Fiber.Count65.FrameTransport.ActualClassification
import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.PairedForm

/-! # Every actual width-(6,5) Max4 network has one of three first-matrix forms

The hypothesis is the original all-input network equation. No zero-bias,
carrier, root-frame, coefficient-alphabet, or sector-membership hypothesis is
assumed. Positive first-row scales and both finite permutations are retained
inside the three concrete matrix predicates.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier

/-- Complete first-hidden-layer exhaustion for the full physical exact fiber.
This does not yet classify the second hidden layer or count components. -/
theorem max4_first_matrix_trichotomy (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x) :
    PairedFirstMatrixForm net ∨ Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  rcases max4_six_invariant_row_count net hnet with htwo | hfour
  · exact Or.inl (TwoInvariantPairing.pairedFirstMatrixForm_of_two_invariant net hnet htwo)
  · have hcard : (invariantRows net).card = 4 := hfour
    rcases FrameTransport.network_four_invariant_frame_reduction net hnet hcard with
      hmixed | hstar | hroot
    · exact Or.inr (Or.inl hmixed)
    · exact Or.inr (Or.inr hstar)
    · rcases four_root_first_matrix_cases net hnet hcard hroot with hpaired | hstar
      · exact Or.inl hpaired
      · exact Or.inr (Or.inr hstar)

#print axioms max4_first_matrix_trichotomy
end MaxCaterpillar.Fiber.Count65
