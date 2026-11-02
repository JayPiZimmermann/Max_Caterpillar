import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.FourRoles
import MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment.Unit

/-! Actual opposite target comparisons with three arbitrary residual gates. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
open BigOperators Absorption BaselineAttachment QuadrantGroups

theorem two_comparisons_quotient_joined (a : ExactFiber 4 6 5)
    (U : Fin 2 → Fin 2 → ℝ) (hdet : codeDet U ≠ 0)
    (hU : a.val.W₁ = pairedRows U) (hb : a.val.HasZeroBiases)
    (cp cn : Fin 5) (hcpn : cp ≠ cn) (hsum : a.val.w₃ cp+a.val.w₃ cn=1)
    (hcpr : ∀ x, endpointForm U (a.val.W₂ cp) x = endpointForm U (comparisonRow U) x)
    (hcnr : ∀ x, endpointForm U (a.val.W₂ cn) x = -endpointForm U (comparisonRow U) x) :
    Joined (quotientMk a) (quotientMk (pairedMinimalPoint U hdet)) := by
  classical
  let C : Finset (Fin 5) := {cp,cn}
  let S : Finset (Fin 5) := Finset.univ \ C
  have hS : 3 ≤ S.card := by
    dsimp only [S]
    rw [Finset.card_sdiff (Finset.subset_univ C)]
    norm_num [C,hcpn]
  have hcpS : cp ∉ S := by simp [S,C]
  have hcnS : cn ∉ S := by simp [S,C]
  have hnatural : ∀ i ∈ C, ∀ x, endpointForm U (a.val.W₂ i) x =
      if decide (i=cn) then -endpointForm U (comparisonRow U) x else
        endpointForm U (comparisonRow U) x := by
    intro i hi x
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      simpa [hcpn] using hcpr x
    · have hh := Finset.mem_singleton.mp hi
      subst i
      simpa using hcnr x
  have hweight : (∑ i in C,a.val.w₃ i)=1 := by simpa [C,hcpn] using hsum
  have hfit := comparison_cluster_baseline_fit a.val U hdet hU hb a.property C
    (fun i => decide (i=cn)) hnatural hweight
  have hs : (∑ i in C,a.val.w₃ i*orientationIndicator (decide (i=cn)))=a.val.w₃ cn := by
    simp [C,hcpn,orientationIndicator]
  rw [hs] at hfit
  have hpreact (i : Fin 5) (x : Point 4) :
      preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x = endpointForm U (a.val.W₂ i) x := by
    rw [hU,hb.1,hb.2.1]
    exact preact_pairedRows_zero U (a.val.W₂ i) x
  have hlocal : ∀ x,(∑ i in S,a.val.w₃ i*relu
      (preact a.val.W₁ a.val.b₁ (a.val.W₂ i) (a.val.b₂ i) x)) =
      BaselineWeighted.weightedTarget (a.val.w₃ cn) x := by
    intro x
    simp_rw [hpreact]
    exact hfit x
  obtain ⟨p,n,hp,hn,hpn,hjoin⟩ := weighted_baseline_attachment a.val U hU hdet hb
    (a.val.w₃ cn) S hS hlocal a.property
  have hpne : p ≠ cp ∧ p ≠ cn := by simpa [S,C,not_or] using hp
  have hnne : n ≠ cp ∧ n ≠ cn := by simpa [S,C,not_or] using hn
  let b : ExactFiber 4 6 5 := ⟨signedNet a.val S p n (weightedRow U (a.val.w₃ cn)) 0,
    hjoin.target_mem⟩
  have hbb : b.val.HasZeroBiases := by
    refine ⟨hb.1,?_,hb.2.2⟩
    funext i
    by_cases hip : i=p <;> by_cases hin : i=n <;> by_cases hiS : i∈S <;>
      simp [b,signedNet,signedChordBiases,hip,hin,hiS,hb.2.1]
  have hcprow : b.val.W₂ cp = a.val.W₂ cp := by
    simp [b,signedNet,signedChordRows,Ne.symm hpne.1,Ne.symm hnne.1,hcpS]
  have hcnrow : b.val.W₂ cn = a.val.W₂ cn := by
    simp [b,signedNet,signedChordRows,Ne.symm hpne.2,Ne.symm hnne.2,hcnS]
  have hcpw : b.val.w₃ cp = 1-a.val.w₃ cn := by
    simp only [b,signedNet,readout,if_neg (Ne.symm hpne.1),if_neg (Ne.symm hnne.1),if_neg hcpS]
    linarith only [hsum]
  have hcnw : b.val.w₃ cn = a.val.w₃ cn := by
    simp [b,signedNet,readout,Ne.symm hpne.2,Ne.symm hnne.2,hcnS]
  have hpw : b.val.w₃ p = 1 := by simp [b,signedNet,readout]
  have hnw : b.val.w₃ n = -1 := by simp [b,signedNet,readout,Ne.symm hpn]
  have hwo : ∀ i,i≠cp → i≠cn → i≠p → i≠n → b.val.w₃ i=0 := by
    intro i hicp hicn hip hin
    have hiS : i∈S := by simp [S,C,hicp,hicn]
    simp [b,signedNet,readout,hip,hin,hiS,hicp,hicn]
  have hprow : b.val.W₂ p = weightedRow U (a.val.w₃ cn) := by simp [b,signedNet,signedChordRows]
  have hnrow : b.val.W₂ n = -weightedRow U (a.val.w₃ cn) := by
    simp [b,signedNet,signedChordRows,Ne.symm hpn]
  have hfinal := two_comparisons_signed_quotient_joined b U hdet hU hbb cp cn p n
    hcpn (Ne.symm hpne.1) (Ne.symm hnne.1) (Ne.symm hpne.2) (Ne.symm hnne.2) hpn
    (a.val.w₃ cn) hcpw hcnw hpw hnw hwo
    (fun x => by rw [hcprow]; exact hcpr x) (fun x => by rw [hcnrow]; exact hcnr x) hprow hnrow
  exact (quotient_joined_of_joinedIn a b hjoin).trans hfinal

end MaxCaterpillar.Fiber.Count65.Paired.LowAtomsAttachment
