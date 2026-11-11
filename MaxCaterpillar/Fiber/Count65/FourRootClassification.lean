import MaxCaterpillar.Fiber.Count65.FourRootCompletion
import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.PairedWallForm

/-! # The actual four-root branch of the first-matrix classification

The only branch assumption is the support size of the actual invariant rows.
The finite root graph, input labeling, both remaining carrier rows, and the
complete first-matrix normal form are all derived.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier

/-- Four actual invariant coordinate-difference rows belong to the paired
sector or to the star endpoint. All biases and all suffix weights are free. -/
theorem four_root_first_matrix_cases (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4)
    (hroot : ∀ j, (∑ i, net.W₁ j i) = 0 →
      (nonzeroCoordinates (net.W₁ j)).card = 2) :
    PairedFirstMatrixForm net ∨ StarFirstMatrixForm net := by
  obtain ⟨q,hpaired | hstar⟩ := network_four_root_directions net hnet hcard hroot
  · exact Or.inl (pairedFirstMatrixForm_of_four_invariant_paired_frame
      net hnet hcard q hpaired)
  · exact Or.inr (star_first_matrix_of_root_frame net hnet hcard q hstar)

#print axioms four_root_first_matrix_cases
end MaxCaterpillar.Fiber.Count65
