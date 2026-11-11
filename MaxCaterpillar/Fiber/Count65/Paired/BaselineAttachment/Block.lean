import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Quadrant
import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Prefix
import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Carrier
import MaxCaterpillar.Fiber.Count65.Paired.BaselineEndpointFold

/-! Actual attachment of arbitrary weighted paired baseline blocks. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators Absorption BaselineEndpointFold
variable {m r : ℕ}

theorem weighted_baseline_block_attachment (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (hm : 3≤m) (C : Fin m → Fin 6 → ℝ) (weights : Fin m → ℝ)
    (hfit : ∀ x,(BaselineFold.completion U C 0 weights 0).eval x=BaselineWeighted.weightedTarget s x)
    (rows : Fin r → Fin 6 → ℝ) (bias sw : Fin r → ℝ)
    (hsource : ∀ x,(appendSpectators (BaselineFold.completion U C 0 weights 0) rows bias sw).eval x=
      Maximum 4 x) :
    ∃ p n : Fin (m+r),p∈prefixSlots m r ∧ n∈prefixSlots m r ∧ p≠n ∧
      JoinedIn (ExactSet 4 6 (m+r))
        (appendSpectators (BaselineFold.completion U C 0 weights 0) rows bias sw)
        (signedNet (appendSpectators (BaselineFold.completion U C 0 weights 0) rows bias sw)
          (prefixSlots m r) p n (baselineRow U s) 0) := by
  classical
  obtain ⟨data,hfold⟩ := weighted_baseline_fold_data U hU s C weights hfit rows bias sw hsource
  let source := appendSpectators (BaselineFold.completion U C 0 weights 0) rows bias sw
  let B := appendSpectators data.block rows bias sw
  let S := prefixSlots m r
  let α : Fin (m+r) → ℝ := Fin.append data.a 0
  let β : Fin (m+r) → ℝ := Fin.append data.b 0
  have hrows : ∀ i∈S,∀ j,B.W₂ i j=α i*data.positiveRow j+β i*data.negativeRow j := by
    intro i hi j
    obtain ⟨k,rfl⟩ := prefixSlots_onto i hi
    simp only [B,α,β,appendSpectators,Fin.append_left]
    exact congrFun (data.rows k) j
  have hbias : ∀ i∈S,B.b₂ i=α i*0+β i*0 := by
    intro i hi
    obtain ⟨k,rfl⟩ := prefixSlots_onto i hi
    simp only [B,α,β,appendSpectators,Fin.append_left,data.secondBias,Pi.zero_apply,
      mul_zero,zero_add]
  have hQ (x : Point 4) : 0≤preact B.W₁ B.b₁ data.positiveRow 0 x := by
    change 0≤preact data.block.W₁ data.block.b₁ data.positiveRow 0 x
    rw [data.firstMatrix,data.firstBias]
    exact data.positive x
  have hR (x : Point 4) : 0≤preact B.W₁ B.b₁ data.negativeRow 0 x := by
    change 0≤preact data.block.W₁ data.block.b₁ data.negativeRow 0 x
    rw [data.firstMatrix,data.firstBias]
    exact data.negative x
  have hquadrant : ∀ u v : ℝ,0≤u → 0≤v →
      (∑ i in S,B.w₃ i*max 0 (α i*u+β i*v))=u-v := by
    intro u v hu hv
    change (∑ i in prefixSlots m r,B.w₃ i*max 0 (α i*u+β i*v))=u-v
    rw [sum_prefixSlots]
    simp only [B,α,β,appendSpectators,Fin.append_left,data.readout]
    exact data.quadrantFit u v hu hv
  have hcard : 3≤S.card := by simpa only [S,prefixSlots_card] using hm
  obtain ⟨p,n,hp,hn,hpn,hquadrantpath⟩ := quadrant_signed_attachment B S hcard
    data.positiveRow data.negativeRow 0 0 α β hrows hbias hQ hR hquadrant hfold.target_mem
  simp only [sub_self] at hquadrantpath
  have hcarrier : ∀ x,preact B.W₁ B.b₁ (baselineRow U s) 0 x=
      preact B.W₁ B.b₁ (fun j=>data.positiveRow j-data.negativeRow j) 0 x := by
    intro x
    change preact data.block.W₁ data.block.b₁ (baselineRow U s) 0 x=
      preact data.block.W₁ data.block.b₁ (fun j=>data.positiveRow j-data.negativeRow j) 0 x
    rw [data.firstMatrix,data.firstBias,baselineRow_preact U hU s x,data.difference x]
  have hchange := signedNet_change_carrier B S p n
    (fun j=>data.positiveRow j-data.negativeRow j) (baselineRow U s) 0 0 hcarrier hquadrantpath.target_mem
  have hagree : AgreeOutside source B S := appendSpectators_agree
    (BaselineFold.completion U C 0 weights 0) data.block rows bias sw
    data.firstMatrix data.firstBias data.outputBias
  have heq := signedNet_congr_source source B S p n (baselineRow U s) 0 hagree
  exact ⟨p,n,hp,hn,hpn,by simpa only [heq] using (hfold.trans hquadrantpath).trans hchange⟩

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
