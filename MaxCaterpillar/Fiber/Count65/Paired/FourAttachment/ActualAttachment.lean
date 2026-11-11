import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.FamilyQuotient
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpoint

/-! # Arbitrary four-effective-atom paired completions attach to padded minima

This theorem starts with ordinary six-array networks and all-input exactness.
All reductions are actual continuous parameter paths or genuine hidden
permutations in the stated symmetry quotient.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators

/-- Every actual paired `(4,6,5)` completion with four effective atoms joins
the actual padded minimal completion in the genuine symmetry quotient. -/
theorem network_four_atoms_quotient_attaches (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun i => net.W₂ i 0) (fun i => net.W₂ i 1)).card=4) :
    Joined (quotientMk (⟨net,hnet⟩ : ExactFiber 4 6 5))
      (quotientMk (pairedMinimalPoint U hcode)) := by
  obtain ⟨c,e,q,hq₀,hq,hnormal,hfamily,hg⟩ :=
    network_four_oriented_representation net U hU hcode hb hnet hfour
  have hn := hnormal.target_mem
  have hr := hfamily.source_mem
  have hf := extractedFourFamily_exact net U hU hcode hb hnet e hg
  have hp₁ := quotient_joined_of_joinedIn hnet hn hnormal
  have hp₂ := quotient_joined_of_joinedIn hr hf hfamily
  have he : quotientMk (⟨normalizeFourCarrier net c,hn⟩ : ExactFiber 4 6 5)=
      quotientMk (⟨fourReindexedNetwork net c q,hr⟩ : ExactFiber 4 6 5) :=
    quotientMk_eq_of_step (SymmetryStep.hidden (⟨normalizeFourCarrier net c,hn⟩ : ExactFiber 4 6 5)
      (Equiv.refl _) q)
  rw [he] at hp₁
  exact hp₁.trans (hp₂.trans (extracted_four_family_quotient_attaches net U hU hcode hb hnet e hg))

/-- The same attachment in the genuine zero-bias quotient used for the
component count. It is obtained by continuous bias retraction of the exhibited
full-quotient path, with both displayed endpoints fixed by the retraction. -/
theorem network_four_atoms_zeroQuotient_attaches (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun i => net.W₂ i 0) (fun i => net.W₂ i 1)).card=4) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨(⟨net,hnet⟩ : ExactFiber 4 6 5),hb⟩ : ZeroBiasFiber 4 6 5))
      (pairedMinimalZeroQuotient U hcode) := by
  have respect : ∀ a b : ExactFiber 4 6 5,(symmetrySetoid 4 6 5).r a b →
      (zeroBiasSymmetrySetoid 4 6 5).r (zeroBiasRetraction a) (zeroBiasRetraction b) := by
    intro a b h
    change (symmetrySetoid 4 6 5).r (zeroBiasFiber a) (zeroBiasFiber b)
    exact zeroBiasFiber_symmetry h
  let erase : SymmetryQuotient 4 6 5 → ZeroBiasSymmetryQuotient 4 6 5 :=
    Quotient.map' zeroBiasRetraction respect
  have hc : Continuous erase := continuous_zeroBiasRetraction.quotient_map' respect
  have hs : erase (quotientMk (⟨net,hnet⟩ : ExactFiber 4 6 5))=
      Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
        (⟨(⟨net,hnet⟩ : ExactFiber 4 6 5),hb⟩ : ZeroBiasFiber 4 6 5) :=
    congrArg (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5))
      (zeroBiasRetraction_include (⟨(⟨net,hnet⟩ : ExactFiber 4 6 5),hb⟩ : ZeroBiasFiber 4 6 5))
  have ht : erase (quotientMk (pairedMinimalPoint U hcode))=pairedMinimalZeroQuotient U hcode :=
    congrArg (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5))
      (zeroBiasRetraction_include (pairedMinimalZeroPoint U hcode))
  have hp := (network_four_atoms_quotient_attaches net U hU hcode hb hnet hfour).somePath.map hc
  rw [hs,ht] at hp
  exact ⟨hp⟩

/-- In particular every actual four-atom paired completion lies in the single
canonical paired path component of the genuine zero-bias symmetry quotient. -/
theorem network_four_atoms_to_canonical (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (hfour : (activeAtoms net.w₃ (fun i => net.W₂ i 0) (fun i => net.W₂ i 1)).card=4) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (⟨(⟨net,hnet⟩ : ExactFiber 4 6 5),hb⟩ : ZeroBiasFiber 4 6 5)) canonicalPairedEndpoint :=
  (network_four_atoms_zeroQuotient_attaches net U hU hcode hb hnet hfour).trans
    (pairedMinimal_to_canonical U hcode)

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
