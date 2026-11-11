import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.UnitSigned
import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
import MaxCaterpillar.Fiber.Count65.Paired.ComparisonResidual

/-! Actual unit comparison attachment with four arbitrary physical residual gates. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open BigOperators Absorption BaselineAttachment QuadrantGroups

/-- One global unit comparison, with arbitrary four remaining gates, lies in
the genuine symmetry-quotient path component of the paired minimal endpoint. -/
theorem unit_comparison_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (c : Fin 5) (flip : Bool) (hwc : a.val.w₃ c = 1)
    (hpc : ∀ x, endpointForm U (a.val.W₂ c) x =
      if flip then -endpointForm U (comparisonRow U) x else endpointForm U (comparisonRow U) x) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  let S : Finset (Fin 5) := Finset.univ \ {c}
  have hS : 3 ≤ S.card := by norm_num [S,Finset.sdiff_singleton_eq_erase]
  have hcS : c ∉ S := by simp [S]
  have hfit := comparison_cluster_baseline_fit a.val U hdet hU hb a.property
    ({c} : Finset (Fin 5)) (fun _ => flip)
    (fun i hi x => by simpa only [Finset.mem_singleton.mp hi] using hpc x)
    (by simpa only [Finset.sum_singleton] using hwc)
  simp only [Finset.sum_singleton,hwc,one_mul] at hfit
  have hpreact (i : Fin 5) (x : Point 4) :
      preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x = endpointForm U (a.val.W₂ i) x := by
    rw [hU,hb.1,hb.2.1]
    exact preact_pairedRows_zero U (a.val.W₂ i) x
  have hlocal : ∀ x, (∑ i in S, a.val.w₃ i*relu
      (preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x)) =
      BaselineWeighted.weightedTarget (orientationIndicator flip) x := by
    intro x
    simp_rw [hpreact]
    exact hfit x
  obtain ⟨p,n,hp,hn,hpn,hjoin⟩ := weighted_baseline_attachment a.val U hU hdet hb
    (orientationIndicator flip) S hS hlocal a.property
  let b : ExactFiber 4 6 5 := ⟨signedNet a.val S p n
    (weightedRow U (orientationIndicator flip)) 0,hjoin.target_mem⟩
  have hpc' : p ≠ c := by simpa [S] using hp
  have hnc' : n ≠ c := by simpa [S] using hn
  have hcp : c ≠ p := Ne.symm hpc'
  have hcn : c ≠ n := Ne.symm hnc'
  have hbb : b.val.HasZeroBiases := by
    refine ⟨hb.1,?_,hb.2.2⟩
    funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hiS : i∈S <;>
      simp [b,signedNet,signedChordBiases,hip,hin,hiS,hb.2.1]
  have hcrow : b.val.W₂ c = a.val.W₂ c := by
    simp [b,signedNet,signedChordRows,hcp,hcn,hcS]
  have hbw : b.val.w₃ c = 1 := by
    simp [b,signedNet,readout,hcp,hcn,hcS,hwc]
  have hpw : b.val.w₃ p = 1 := by simp [b,signedNet,readout]
  have hnw : b.val.w₃ n = -1 := by simp [b,signedNet,readout,Ne.symm hpn]
  have hwo : ∀ i, i≠c → i≠p → i≠n → b.val.w₃ i=0 := by
    intro i hic hip hin
    have hiS : i∈S := by simp [S,hic]
    simp [b,signedNet,readout,hip,hin,hiS,hic]
  have hprow : b.val.W₂ p = weightedRow U (orientationIndicator flip) := by
    simp [b,signedNet,signedChordRows]
  have hnrow : b.val.W₂ n = -weightedRow U (orientationIndicator flip) := by
    simp [b,signedNet,signedChordRows,Ne.symm hpn]
  have hunit := unit_signed_quotient_joined b U hdet hU hbb c p n hcp hcn hpn flip
    hbw hpw hnw hwo (fun x => by rw [hcrow]; exact hpc x) hprow hnrow
  exact (quotient_joined_of_joinedIn a b hjoin).trans hunit

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
