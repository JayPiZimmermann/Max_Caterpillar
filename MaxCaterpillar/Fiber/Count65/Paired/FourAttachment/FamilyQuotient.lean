import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.FamilyAttachment
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Compression.Quotient

/-! # Every extracted four-atom family attaches in the genuine quotient -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption

private theorem through_commonSupport (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (H : Fin 6 → ℝ) (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4))
    (hS : (∑ i in S,j i)=0) (hj : (∑ i,j i)=1)
    (source : Network 4 6 5)
    (hp : JoinedIn (ExactSet 4 6 5) source
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (fun i => if i∈S then H else 0) j flip)) :
    Joined (quotientMk (⟨source,hp.source_mem⟩ : ExactFiber 4 6 5))
      (quotientMk (pairedMinimalPoint U hU)) := by
  have hc := hp.target_mem
  have hg := orientedCompletion_carrier_nonneg_of_exact (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    (fun i => if i∈S then H else 0) j flip (commonSupport_atomBalance _ _ H j S hS hj) hc
    (paired_max_decomposition U hU)
  exact (quotient_joined_of_joinedIn hp.source_mem hc hp).trans
    (paired_commonSupport_quotient_joined U hU H j flip S hS hj hg hc)

/-- The exhaustive actual signed-code support alternatives all attach to the
same padded minimal endpoint. One-coordinate support changes are contracted
inside physical parameter space before compression. -/
theorem extracted_four_family_quotient_attaches (net : Network 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hU : net.W₁=pairedRows U) (hcode : codeDet U≠0)
    (hb : net.HasZeroBiases) (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ NetworkAtoms net)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow (fun i => networkAtomJump net (e i)) (fourAtomFlip net e)
        (baselineRow U) (comparisonRow U) (fun i => codeOffsetRow net U (e i))) 0 x) :
    Joined (quotientMk (extractedFourFamilyPoint net U hU hcode hb hnet e hg))
      (quotientMk (pairedMinimalPoint U hcode)) := by
  let j := fun i : Fin 4 => networkAtomJump net (e i)
  let flip := fourAtomFlip net e
  have hj : (∑ i,j i)=1 := network_atom_jumps_sum net U hU hb hnet e
  have hneg := paired_negative_diagonal U hcode
  have hnonzero := carrierRow_offsets_not_all_zero (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    (fun i => codeOffsetRow net U (e i)) j flip hg (fun _ => -1) hneg.1 hneg.2
  rcases network_codeOffsetRow_cases net U hU hcode hb hnet e hnonzero with
    ⟨S,T,c,d,hS,hT,hF⟩ | ⟨S,T,c,d,hS,hT,hF⟩ | ⟨S,H,hS,hF⟩
  · have hgp : ∀ x,0≤preact (pairedRows U) 0
        (carrierRow j flip (baselineRow U) (comparisonRow U)
          (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c d)) 0 x := by
      simpa only [hF] using hg
    have hp := paired_right_halflineCompletion_contract U hcode S T c d j flip hS hT hj hgp
    rcases hp with hp|hp
    · rw [halflineOffsets_left_zero] at hp
      have hq := through_commonSupport U hcode (d • negativeRightCodeRow) j flip T hT hj _ hp
      have he : extractedFourFamilyPoint net U hU hcode hb hnet e hg=
          (⟨_,hp.source_mem⟩ : ExactFiber 4 6 5) := by
        apply Subtype.ext
        dsimp only [extractedFourFamilyPoint,extractedFourFamily]
        rw [hF]
      rw [he]
      exact hq
    · rw [halflineOffsets_right_zero] at hp
      have hq := through_commonSupport U hcode (c • positiveRightCodeRow) j flip S hS hj _ hp
      have he : extractedFourFamilyPoint net U hU hcode hb hnet e hg=
          (⟨_,hp.source_mem⟩ : ExactFiber 4 6 5) := by
        apply Subtype.ext
        dsimp only [extractedFourFamilyPoint,extractedFourFamily]
        rw [hF]
      rw [he]
      exact hq
  · have hgp : ∀ x,0≤preact (pairedRows U) 0
        (carrierRow j flip (baselineRow U) (comparisonRow U)
          (halflineOffsets positiveCodeRow negativeCodeRow S T c d)) 0 x := by
      simpa only [hF] using hg
    have hp := paired_halflineCompletion_contract U hcode S T c d j flip hS hT hj hgp
    rcases hp with hp|hp
    · rw [halflineOffsets_left_zero] at hp
      have hq := through_commonSupport U hcode (d • negativeCodeRow) j flip T hT hj _ hp
      have he : extractedFourFamilyPoint net U hU hcode hb hnet e hg=
          (⟨_,hp.source_mem⟩ : ExactFiber 4 6 5) := by
        apply Subtype.ext
        dsimp only [extractedFourFamilyPoint,extractedFourFamily]
        rw [hF]
      rw [he]
      exact hq
    · rw [halflineOffsets_right_zero] at hp
      have hq := through_commonSupport U hcode (c • positiveCodeRow) j flip S hS hj _ hp
      have he : extractedFourFamilyPoint net U hU hcode hb hnet e hg=
          (⟨_,hp.source_mem⟩ : ExactFiber 4 6 5) := by
        apply Subtype.ext
        dsimp only [extractedFourFamilyPoint,extractedFourFamily]
        rw [hF]
      rw [he]
      exact hq
  · have hg' : ∀ x,0≤preact (pairedRows U) 0
        (carrierRow j flip (baselineRow U) (comparisonRow U) (fun i => if i∈S then H else 0)) 0 x := by
      simpa only [funext hF] using hg
    have hsource := extractedFourFamily_exact net U hU hcode hb hnet e hg
    have hc : ∀ x,(orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (fun i => if i∈S then H else 0) j flip).eval x=Maximum 4 x := by
      simpa only [extractedFourFamily,funext hF] using hsource
    have hp := paired_commonSupport_quotient_joined U hcode H j flip S hS hj hg' hc
    have he : extractedFourFamilyPoint net U hU hcode hb hnet e hg=
        (⟨_,hc⟩ : ExactFiber 4 6 5) := by
      apply Subtype.ext
      dsimp only [extractedFourFamilyPoint,extractedFourFamily]
      rw [funext hF]
    rw [he]
    exact hp

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
