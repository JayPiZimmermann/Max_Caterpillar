import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.SwitchingRows
import MaxCaterpillar.Fiber.Count65.Paired.FeatureInjectivity

/-! # A derived global unit atom becomes an actual unit comparison gate -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
open Frontier Absorption

lemma target_unitAtomRow (net : Network 4 6 5) (U : Fin 2 → Fin 2 → ℝ)
    (hdet : codeDet U≠0) (i : NetworkAtoms net)
    (hoff : ∀ a b,networkAtomOffset net U a b i=0) :
    unitAtomRow net i=comparisonRow U := by
  apply paired_feature_injective U (inverseCode U) (inverseCode_rightInverse U hdet)
  intro x
  rw [preact_pairedRows_zero,preact_pairedRows_zero,unitAtomRow_natural_offset net U hdet i x,
    hoff (x 1) (x 3),sub_zero]

/-- The global target atom furnished by exactness is normalized through an
actual physical path; no unit slope or literal row is assumed in the source. -/
theorem global_unit_atom_witness (net : Network 4 6 5) (U : Fin 2 → Fin 2 → ℝ)
    (hdet : codeDet U≠0) (hW : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) (i : NetworkAtoms net)
    (hj : networkAtomJump net i=1) (hoff : ∀ a b,networkAtomOffset net U a b i=0) :
    ∃ n : ExactFiber 4 6 5,n.val.W₁=pairedRows U ∧ n.val.HasZeroBiases ∧
      n.val.w₃ i.val=1 ∧
      n.val.W₂ i.val=(if networkAtomFlip net i then -comparisonRow U else comparisonRow U) ∧
      JoinedIn (ExactSet 4 6 5) net n.val := by
  have hp := normalizedAtomNetwork_joinedIn_exact net hnet
  let n : ExactFiber 4 6 5 := ⟨normalizedAtomNetwork net,hp.target_mem⟩
  refine ⟨n,hW,?_,?_,?_,hp⟩
  · exact PairNormalization.normalizeAtoms_zeroBiases net 0 (networkAtomSlots net) hb
  · exact (normalizedAtomNetwork_output net i).trans hj
  · change (normalizedAtomNetwork net).W₂ i.val=_
    rw [normalizedAtomNetwork_row_oriented,target_unitAtomRow net U hdet i hoff]

#print axioms global_unit_atom_witness
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
