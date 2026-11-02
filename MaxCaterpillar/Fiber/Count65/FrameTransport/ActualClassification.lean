import MaxCaterpillar.Fiber.Count65.FrameTransport.ActualFrames
import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.Two
import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.Three
import MaxCaterpillar.Fiber.Count65.FrameTransport.ForkNetworkExclusion
import MaxCaterpillar.Fiber.Count65.FrameTransport.ThreeNetworkClassification

/-! # The complete actual two-root and three-root strata

The headline uses only the original network equation and the cardinality of
its actual invariant first rows. Graph labels, real scales, nonroot rows,
coordinate carriers, and complete first-matrix forms are proved in sequence.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

/-- An exact physical width-(6,5) network cannot have exactly two
coordinate-root rows among its four actual invariant rows. -/
theorem network_two_root_count_impossible (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (e : Fin 4 ≃ invariantRows net)
    (hc : (rootIndices (enumeratedRows net e)).card=2) : False := by
  let nf := normalizedActualFrame net hnet e
  obtain ⟨k,q,s,t,_hsum,_htsum,hs,ht,p,c,hcpos,hrows⟩ :=
    two_root_frame_transport nf (enumerated_rows_not_pos_proportional net hnet e) hc
  obtain ⟨e',hW⟩ := reorder_invariant_frame net e (twoRootRows k s t) p c q.symm hrows
  exact network_two_root_frame_excluded net hnet e' k s t hs ht
    (fun j => c (p.symm j)) q.symm (fun j => hcpos (p.symm j)) hW

/-- Three actual invariant coordinate roots force one of the two complete
path first-matrix families. Original biases and suffix weights are arbitrary. -/
theorem network_three_root_count_forms (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (e : Fin 4 ≃ invariantRows net)
    (hc : (rootIndices (enumeratedRows net e)).card=3) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  let nf := normalizedActualFrame net hnet e
  obtain ⟨k,q,t,hsum,ht,p,c,hcpos,hrows⟩ :=
    three_root_frame_transport nf (enumerated_rows_not_pos_proportional net hnet e) hc
  obtain ⟨e',hW⟩ := reorder_invariant_frame net e (threeRootRows k t) p c q.symm hrows
  exact three_root_matrix_form_of_frame net hnet e' (fun j => c (p.symm j)) q.symm
    (fun j => hcpos (p.symm j)) k t hsum ht hW

/-- Unconditional reduction of the four-invariant stratum. The remaining
all-root branch is supplied to the separate four-root finite classifier. -/
theorem network_four_invariant_frame_reduction (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (hcard : (invariantRows net).card=4) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net ∨
      (∀ j,(∑ i,net.W₁ j i)=0 → (nonzeroCoordinates (net.W₁ j)).card=2) := by
  obtain ⟨e,_nf,hcases⟩ := actual_normalized_feature_frame net hnet hcard
  rcases hcases with htwo | hthree | hfour
  · exact False.elim (network_two_root_count_impossible net hnet e htwo)
  · rcases network_three_root_count_forms net hnet e hthree with hm | hs
    · exact Or.inl hm
    · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (all_invariant_roots_of_card_four net e hfour))

#print axioms network_two_root_count_impossible
#print axioms network_three_root_count_forms
#print axioms network_four_invariant_frame_reduction
end MaxCaterpillar.Fiber.Count65.FrameTransport
