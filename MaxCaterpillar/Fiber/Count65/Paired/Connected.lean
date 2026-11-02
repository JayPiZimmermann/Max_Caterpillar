import MaxCaterpillar.Fiber.Count65.Paired.QuotientSector
import MaxCaterpillar.Fiber.Count65.Paired.FirstNormalization
import MaxCaterpillar.Fiber.Count65.Paired.QuotientPaths
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpoint
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.ActualAttachment
import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
import MaxCaterpillar.Fiber.Count65.GlobalLabelFibers

/-! # Actual paired completions lie in one genuine quotient path component

The first-matrix orbit is normalized by actual allowed symmetries. The finite
comparison support bound and its attachment branches then exhaust every
ordinary real completion; no attachment or connectedness hypothesis is added.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open Set Function

lemma pairedRows_firstMatrixForm (net : Network 4 6 5) (U : Code)
    (hdet : codeDet U≠0) (hfirst : net.W₁=pairedRows U) : PairedFirstMatrixForm net := by
  refine ⟨U 0 0,U 0 1,U 1 0,U 1 1,hdet,(fun _ => 1),
    (fun _ => zero_lt_one),Equiv.refl _,Equiv.refl _,?_⟩
  intro j i
  rw [hfirst]
  change pairedRows U j i=1*MaxCaterpillar.Fiber.Count65.pairedRows
    (U 0 0) (U 0 1) (U 1 0) (U 1 1) j i
  rw [one_mul]
  rfl

lemma pairedMinimal_mem_quotientSector (U : Code) (hdet : codeDet U≠0) :
    pairedMinimalZeroQuotient U hdet ∈ quotientSector := by
  refine ⟨pairedMinimalZeroPoint U hdet,?_,rfl⟩
  exact pairedRows_firstMatrixForm _ U hdet rfl

lemma canonicalPairedEndpoint_mem : canonicalPairedEndpoint ∈ quotientSector :=
  pairedMinimal_mem_quotientSector identityCode (by rw [identityCode_det]; norm_num)

lemma quotientSector_nonempty : quotientSector.Nonempty :=
  ⟨canonicalPairedEndpoint,canonicalPairedEndpoint_mem⟩

/-- The actual five-neuron network supplies precisely the three cardinality
ranges used by the concrete attachment proofs. -/
theorem network_atom_card_cases (net : Network 4 6 5) (U : Code)
    (hfirst : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x) :
    (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card ≤ 2 ∨
    (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card=3 ∨
    (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card=4 := by
  let n := (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card
  have hn : n ≤ 4 := network_activeAtoms_card net (by decide : 5≤5) U hfirst hb hnet
  by_cases hlow : n ≤ 2
  · exact Or.inl hlow
  by_cases hthree : n=3
  · exact Or.inr (Or.inl hthree)
  apply Or.inr
  apply Or.inr
  apply Nat.le_antisymm hn
  have hgt : 2<n := lt_of_not_ge hlow
  have h3 : 3≤n := Nat.succ_le_iff.mpr hgt
  have hgt3 : 3<n := lt_of_le_of_ne h3 (Ne.symm hthree)
  exact Nat.succ_le_iff.mpr hgt3

/-- All ordinary zero-bias completions over an arbitrary invertible paired
code attach to the same fixed endpoint. The support split is derived from
actual exact evaluation, and every branch is an unconditional physical path. -/
theorem normalized_to_canonical (x : ZeroBiasFiber 4 6 5) (U : Code)
    (hdet : codeDet U≠0) (hfirst : x.val.val.W₁=pairedRows U) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) x) canonicalPairedEndpoint := by
  rcases network_atom_card_cases x.val.val U hfirst x.property x.val.property with
    hlow | hthree | hfour
  · have hfull := LowAtomsAttachment.low_atoms_quotient_joined x.val U hdet hfirst x.property hlow
    exact (joined_zeroQuotient_of_joined_full x (pairedMinimalZeroPoint U hdet) hfull).trans
      (pairedMinimal_to_canonical U hdet)
  · exact three_atom_zeroQuotient_joined x.val.val U hdet hfirst x.property x.val.property hthree
  · exact FourAttachment.network_four_atoms_to_canonical x.val.val U hfirst hdet
      x.property x.val.property hfour

/-- Every representative of the complete actual paired first-matrix orbit
joins the fixed canonical point in the genuine zero-bias symmetry quotient. -/
theorem quotientSector_joined_canonical (z : ZeroBiasSymmetryQuotient 4 6 5)
    (hz : z ∈ quotientSector) : Joined z canonicalPairedEndpoint := by
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨U,hdet,y,hy,hQ⟩ := paired_normalized_representative x hx
  rw [hQ]
  exact normalized_to_canonical y U hdet hy

/-- The full actual paired sector has one path component after exactly the
allowed positive hidden rescalings and hidden/input permutations. -/
theorem isPathConnected_quotientSector : IsPathConnected quotientSector := by
  refine ⟨canonicalPairedEndpoint,canonicalPairedEndpoint_mem,?_⟩
  intro y hy
  exact joinedIn_paired_quotientSector canonicalPairedEndpoint_mem
    (quotientSector_joined_canonical y hy).symm

#check @normalized_to_canonical
#check @isPathConnected_quotientSector
#print axioms normalized_to_canonical
#print axioms quotientSector_joined_canonical
#print axioms isPathConnected_quotientSector
#print axioms canonicalPairedEndpoint_mem
#print axioms network_atom_card_cases

end MaxCaterpillar.Fiber.Count65.Paired
