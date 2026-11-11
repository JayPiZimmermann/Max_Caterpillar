import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.AllTarget
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.Ordering
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.UnitAttachment
import MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment.RawExceptional
import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpoint

/-! # Every actual three-atom paired completion attaches to the minimal endpoint

The exhaustive alternatives come from the physical exact-network identity.
The first alternative merges actual matching rows; the others normalize a
unit target atom or deform the derived switching profile. No attachment or
baseline classification is assumed in the headline.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open ThreeAttachment

/-- Every exact zero-bias physical paired network with exactly three active
atoms joins the actual padded minimal network in the genuine full quotient. -/
theorem three_atom_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : a.val.W₁=pairedRows U) (hb : a.val.HasZeroBiases)
    (hc : (activeAtoms a.val.w₃ (fun k => a.val.W₂ k 0) (fun k => a.val.W₂ k 1)).card=3) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  rcases network_three_atom_cases a.val U hW hb a.property hc with hz | hunit | hswitch
  · obtain ⟨n,hnW,hnb,hnexact,hncard,hnpath⟩ :=
      allTarget_reduces_activeAtoms a.val U hdet hW hb a.property hc hz
    let b : ExactFiber 4 6 5 := ⟨n,hnexact⟩
    exact (joinedIn_exact_quotient a b hnpath).trans
      (LowAtomsAttachment.low_atoms_quotient_joined b U hdet hnW hnb hncard)
  · obtain ⟨i,hj,hoff⟩ := hunit
    exact global_unit_atom_quotient_joined a U hdet hW hb i hj hoff
  · obtain ⟨e,hj,hoff⟩ := hswitch
    rcases switching_order_cases a.val U e hj hoff with ⟨f,hjf,hoffF,hflipF⟩ | ⟨hsame,hne⟩
    · exact ordinary_switching_quotient_joined a U hdet hW hb f hjf hoffF hflipF
    · exact exceptional_switching_quotient_joined a U hdet hW hb e hj hoff hsame hne

/-- The raw three-atom result in exactly the zero-bias symmetry quotient used
for the final component count, with one fixed canonical paired endpoint. -/
theorem three_atom_zeroQuotient_joined (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U≠0)
    (hW : net.W₁=pairedRows U) (hb : net.HasZeroBiases)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hc : (activeAtoms net.w₃ (fun k => net.W₂ k 0) (fun k => net.W₂ k 1)).card=3) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨⟨net,hnet⟩,hb⟩ : ZeroBiasFiber 4 6 5)) canonicalPairedEndpoint := by
  have hj := three_atom_quotient_joined (⟨net,hnet⟩ : ExactFiber 4 6 5) U hdet hW hb hc
  have hz := joined_zeroQuotient_of_joined_full
    (⟨⟨net,hnet⟩,hb⟩ : ZeroBiasFiber 4 6 5) (pairedMinimalZeroPoint U hdet) hj
  exact hz.trans (pairedMinimal_to_canonical U hdet)

#print axioms three_atom_quotient_joined
#print axioms three_atom_zeroQuotient_joined
end MaxCaterpillar.Fiber.Count65.Paired
