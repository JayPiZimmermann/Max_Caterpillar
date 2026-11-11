import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.Compression
import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.PairedHalfline
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointScaledBridge

/-! The physical common-support compression attaches to the actual paired
minimal point in the genuine symmetry quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption

lemma paired_chord_one_scaled (U : Code) (g H : Fin 6 → ℝ) (K s : ℝ) :
    carrierPairChord (pairedRows U) 0 g H (comparisonRow U) (baselineRow U)
      0 0 0 0 0 1 K s 1=
        scaledEndpointNet U 1 K (-comparisonRow U) := by
  simp [carrierPairChord,carrierPairNet,scaledEndpointNet]

lemma scaledEndpoint_zero_eval (U : Code) (d : ℝ) (Z : Fin 6 → ℝ) (x : Point 4) :
    (scaledEndpointNet U d 0 Z).eval x=relu (endpointForm U (comparisonRow U) x) := by
  simp only [Network.eval,scaledEndpointNet,Pi.zero_apply,add_zero]
  change (∑ k : Fin 5,(![d,0,-0,1,0] : Fin 5 → ℝ) k*
    relu (endpointForm U ((![0,(0:ℝ)⁻¹ • baselineRow U,-((0:ℝ)⁻¹ • baselineRow U),comparisonRow U,Z] :
      Fin 5 → Fin 6 → ℝ) k) x))= _
  simp [Fin.sum_univ_succ,endpointForm_zero,relu]

/-- Actual common-support parameters reach the paired minimal point through
physical paths and permitted hidden permutations only. -/
theorem paired_commonSupport_quotient_joined (U : Code) (hcode : codeDet U≠0)
    (H : Fin 6 → ℝ) (j : Fin 4 → ℝ) (flip : Fin 4 → Bool) (S : Finset (Fin 4))
    (hS : (∑ i in S,j i)=0) (hj : (∑ i,j i)=1)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow j flip (baselineRow U) (comparisonRow U) (fun i => if i∈S then H else 0)) 0 x)
    (hexact : ∀ x,(orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
      (fun i => if i∈S then H else 0) j flip).eval x=Maximum 4 x) :
    Joined (quotientMk (⟨orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
      (fun i => if i∈S then H else 0) j flip,hexact⟩ : ExactFiber 4 6 5))
      (quotientMk (pairedMinimalPoint U hcode)) := by
  have hD : preact (pairedRows U) 0 (comparisonRow U) 0 (fun _ => -1)=0 := by
    rw [paired_preact_eq_endpointForm,comparisonRow_form U hcode]
    norm_num
  have hB : preact (pairedRows U) 0 (baselineRow U) 0 (fun _ => -1)<0 := by
    rw [paired_preact_eq_endpointForm,baselineRow_form U hcode]
    norm_num
  obtain ⟨e,hp⟩ := commonSupport_attaches (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    H j flip S hS hj hg hexact (paired_max_decomposition U hcode) (fun _ => -1) hD hB
  let K := groupTotal j (commonSupportGroup S flip) 0
  let s := groupTotal j (commonSupportGroup S flip) 3
  let q := liftLocalPerm e.symm
  have hscaled : ∀ x,(scaledEndpointNet U 1 K (-comparisonRow U)).eval x=Maximum 4 x := by
    intro x
    have hh := hp.target_mem x
    rw [permuteHidden_eval,paired_chord_one_scaled] at hh
    exact hh
  have hK : K≠0 := by
    intro hzero
    have hh := hscaled (fun _ => -1)
    rw [hzero,scaledEndpoint_zero_eval,comparisonRow_form U hcode,Maximum_four] at hh
    norm_num [relu] at hh
  let point := scaledEndpointPoint U hcode 1 K hK (-comparisonRow U)
  have he : (⟨_,hp.target_mem⟩ : ExactFiber 4 6 5)=
      permuteHiddenFiber (Equiv.refl _) q point := by
    apply Subtype.ext
    exact congrArg (fun net => permuteHidden net (Equiv.refl _) q)
      (paired_chord_one_scaled U _ _ K s)
  have hpath : Joined
      (quotientMk (⟨orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (fun i => if i∈S then H else 0) j flip,hexact⟩ : ExactFiber 4 6 5))
      (quotientMk (⟨_,hp.target_mem⟩ : ExactFiber 4 6 5)) :=
    ⟨hp.joined_subtype.somePath.map quotientMk_continuous⟩
  rw [he] at hpath
  have hq : quotientMk (permuteHiddenFiber (Equiv.refl _) q point)=quotientMk point :=
    (quotientMk_eq_of_step (SymmetryStep.hidden point (Equiv.refl _) q)).symm
  rw [hq] at hpath
  exact hpath.trans (scaledEndpoint_quotient_joined U hcode 1 K hK (-comparisonRow U))

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
