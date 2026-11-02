import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointPositive
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointReflection
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointScaledBridge

/-! # One genuine quotient path component for every invertible paired code endpoint

Positive determinant codes are connected by actual network paths. Reversing
one signed code pair flips the determinant and is a genuine first-hidden-neuron
permutation, so both determinant signs meet in the stated symmetry quotient.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

lemma pairedMinimalZeroQuotient_reverseCode (U : Code) (hU : codeDet U≠0) :
    pairedMinimalZeroQuotient (reverseCode U)
      (by rw [codeDet_reverseCode];exact neg_ne_zero.mpr hU)=
      pairedMinimalZeroQuotient U hU := by
  have hr : codeDet (reverseCode U) ≠ 0 := by
    rw [codeDet_reverseCode]
    exact neg_ne_zero.mpr hU
  apply Quotient.sound
  change (symmetrySetoid 4 6 5).r
    (pairedMinimalPoint (reverseCode U) hr) (pairedMinimalPoint U hU)
  have he : pairedMinimalPoint (reverseCode U) hr=
      permuteHiddenFiber (Equiv.swap (4 : Fin 6) 5) (Equiv.refl _)
        (pairedMinimalPoint U hU) := Subtype.ext (pairedMinimalNet_reverseCode U)
  rw [he]
  exact EqvGen.symm _ _ (EqvGen.rel _ _
    (SymmetryStep.hidden (pairedMinimalPoint U hU) (Equiv.swap (4 : Fin 6) 5) (Equiv.refl _)))

/-- Every actual signed padded paired endpoint, with an arbitrary invertible
real anchor code, joins the single identity-code endpoint in the genuine
zero-bias hidden/input symmetry quotient. -/
theorem pairedMinimal_to_canonical (U : Code) (hU : codeDet U≠0) :
    Joined (pairedMinimalZeroQuotient U hU) canonicalPairedEndpoint := by
  rcases lt_or_gt_of_ne hU with hn | hp
  · have hr : 0 < codeDet (reverseCode U) := by
      rw [codeDet_reverseCode]
      exact neg_pos.mpr hn
    have hj := positive_pairedMinimal_to_canonical (reverseCode U) hr
    rw [pairedMinimalZeroQuotient_reverseCode U hU] at hj
    exact hj
  · exact positive_pairedMinimal_to_canonical U hp

/-- The two real determinant signs introduce no additional paired endpoint
component after the actual allowed hidden permutations. -/
theorem pairedMinimal_zeroQuotient_joined (U V : Code)
    (hU : codeDet U≠0) (hV : codeDet V≠0) :
    Joined (pairedMinimalZeroQuotient U hU) (pairedMinimalZeroQuotient V hV) :=
  (pairedMinimal_to_canonical U hU).trans (pairedMinimal_to_canonical V hV).symm

/-- The same result in the full genuine symmetry quotient with biases allowed.
The endpoints are actual zero-bias networks inside that full fiber. -/
theorem pairedMinimal_quotient_joined (U V : Code)
    (hU : codeDet U≠0) (hV : codeDet V≠0) :
    Joined (quotientMk (pairedMinimalPoint U hU)) (quotientMk (pairedMinimalPoint V hV)) := by
  have respect : ∀ a b : ZeroBiasFiber 4 6 5,
      (zeroBiasSymmetrySetoid 4 6 5).r a b →
        (symmetrySetoid 4 6 5).r (includeZeroBias a) (includeZeroBias b) := by
    intro a b h
    change (symmetrySetoid 4 6 5).r (includeZeroBias a) (includeZeroBias b) at h
    exact h
  let forget : ZeroBiasSymmetryQuotient 4 6 5 → SymmetryQuotient 4 6 5 :=
    Quotient.map' includeZeroBias respect
  have hc : Continuous forget := continuous_includeZeroBias.quotient_map' respect
  exact ⟨(pairedMinimal_zeroQuotient_joined U V hU hV).somePath.map hc⟩

/-- The full signed-baseline attachment endpoint, with arbitrary code,
nonzero baseline scale of either sign, silent output and dormant row, joins
the same single actual identity-code endpoint. -/
theorem scaledEndpoint_to_canonical (U : Code) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) :
    Joined (Quotient.mk (zeroBiasSymmetrySetoid 4 6 5)
      (scaledEndpointZeroPoint U hU d K hK Z)) canonicalPairedEndpoint :=
  (scaledEndpoint_zeroQuotient_joined U hU d K hK Z).trans
    (pairedMinimal_to_canonical U hU)

#print axioms pairedMinimal_to_canonical
#print axioms pairedMinimal_zeroQuotient_joined
#print axioms pairedMinimal_quotient_joined
#print axioms scaledEndpoint_to_canonical
end MaxCaterpillar.Fiber.Count65.Paired
