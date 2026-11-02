import MaxCaterpillar.Fiber.Count65.ForkExclusion.CarrierForcing

/-! # A spurious fork crease forces a negative residual gate -/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier

noncomputable def wSlope (κ R S : ℝ) (d : Coeff) : ℝ :=
  (if 0 < R then d.r else 0) + (if 0 < S then κ*d.s else 0)

lemma forms_affine_near_w (α β κ u v w : ℝ) (hκ : 0 < κ)
    (hr : w-α*u-β*v ≠ 0) (hs : κ*w-α*u-β*v ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : Coeff, ∀ t : ℝ, |t| < δ →
      form α β κ d u v (w+t) =
        wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) d*t + form α β κ d u v w := by
  let R := w-α*u-β*v
  let S := κ*w-α*u-β*v
  let δ := min |R| (|S|/κ)
  have hδ : 0 < δ := lt_min (abs_pos.mpr hr) (div_pos (abs_pos.mpr hs) hκ)
  refine ⟨δ,hδ,?_⟩
  intro d t ht
  have htR : |t| < |R| := lt_of_lt_of_le ht (min_le_left _ _)
  have htS : |κ*t| < |S| := by
    rw [abs_mul,abs_of_pos hκ]
    have htd : |t| < |S|/κ := lt_of_lt_of_le ht (min_le_right _ _)
    have hh := (lt_div_iff hκ).mp htd
    nlinarith only [hh]
  have heR : (w+t)-α*u-β*v=R+t := by dsimp [R]; ring
  have heS : κ*(w+t)-α*u-β*v=S+κ*t := by dsimp [S]; ring
  change form α β κ d u v (w+t)=wSlope κ R S d*t+form α β κ d u v w
  unfold form wSlope
  rw [heR,heS]
  change _ = ((if 0<R then d.r else 0)+(if 0<S then κ*d.s else 0))*t+
    (d.a*relu u+d.b*relu v+d.r*relu R+d.s*relu S)
  by_cases hR : 0 < R
  · have hRt : 0 ≤ R+t := by
      rw [abs_of_pos hR] at htR
      linarith only [(abs_lt.mp htR).1]
    by_cases hS : 0 < S
    · have hSt : 0 ≤ S+κ*t := by
        rw [abs_of_pos hS] at htS
        linarith only [(abs_lt.mp htS).1]
      rw [if_pos hR,if_pos hS,relu_of_nonneg hRt,relu_of_nonneg hSt,
        relu_of_nonneg hR.le,relu_of_nonneg hS.le]
      ring
    · have hSneg : S < 0 := lt_of_le_of_ne (le_of_not_gt hS) hs
      have hSt : S+κ*t ≤ 0 := by
        rw [abs_of_neg hSneg] at htS
        linarith only [(abs_lt.mp htS).2]
      rw [if_pos hR,if_neg hS,relu_of_nonneg hRt,relu_of_nonpos hSt,
        relu_of_nonneg hR.le,relu_of_nonpos hSneg.le]
      ring
  · have hRneg : R < 0 := lt_of_le_of_ne (le_of_not_gt hR) hr
    have hRt : R+t ≤ 0 := by
      rw [abs_of_neg hRneg] at htR
      linarith only [(abs_lt.mp htR).2]
    by_cases hS : 0 < S
    · have hSt : 0 ≤ S+κ*t := by
        rw [abs_of_pos hS] at htS
        linarith only [(abs_lt.mp htS).1]
      rw [if_neg hR,if_pos hS,relu_of_nonpos hRt,relu_of_nonneg hSt,
        relu_of_nonpos hRneg.le,relu_of_nonneg hS.le]
      ring
    · have hSneg : S < 0 := lt_of_le_of_ne (le_of_not_gt hS) hs
      have hSt : S+κ*t ≤ 0 := by
        rw [abs_of_neg hSneg] at htS
        linarith only [(abs_lt.mp htS).2]
      rw [if_neg hR,if_neg hS,relu_of_nonpos hRt,relu_of_nonpos hSt,
        relu_of_nonpos hRneg.le,relu_of_nonpos hSneg.le]
      ring

lemma target_affine_near_w (u v w : ℝ) (hw : w ≠ max (max 0 u) v) :
    ∃ δ a b : ℝ, 0 < δ ∧ ∀ t : ℝ, |t|<δ → target u v (w+t)=a*t+b := by
  let M := max (max 0 u) v
  let δ := |w-M|/2
  have hδ : 0 < δ := div_pos (abs_pos.mpr (sub_ne_zero.mpr hw)) (by norm_num)
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · refine ⟨δ,0,M,hδ,?_⟩
    intro t ht
    have ht' := (abs_lt.mp ht).2
    have hwm : w+t ≤ M := by
      dsimp [δ] at ht'
      rw [abs_of_neg (sub_neg.mpr hlt)] at ht'
      linarith only [ht',hlt]
    change max (max 0 u) (max v (w+t)) = _
    rw [← max_assoc,max_eq_left hwm,zero_mul,zero_add]
  · refine ⟨δ,1,w,hδ,?_⟩
    intro t ht
    have ht' := (abs_lt.mp ht).1
    have hmw : M ≤ w+t := by
      dsimp [δ] at ht'
      rw [abs_of_pos (sub_pos.mpr hgt)] at ht'
      linarith only [ht',hgt]
    change max (max 0 u) (max v (w+t)) = _
    rw [← max_assoc,max_eq_right hmw,one_mul]
    ring

/-- A genuine positive crease away from a target wall must be canceled by
some negative-output gate. All other coefficients remain arbitrary. -/
theorem ResidualSystem.negative_of_spurious {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hκ : 0 < κ)
    (h : d.Represents α β κ) (u v w : ℝ)
    (hr : w-α*u-β*v ≠ 0) (hs : κ*w-α*u-β*v ≠ 0)
    (hw : w ≠ max (max 0 u) v) (i : ι) (hi : 0 < d.out i)
    (hz : form α β κ (d.gate i) u v w=0)
    (hd : wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) (d.gate i) ≠ 0) :
    ∃ j, d.out j < 0 := by
  obtain ⟨δF,hδF,hF⟩ := forms_affine_near_w α β κ u v w hκ hr hs
  obtain ⟨δT,a,b,hδT,hT⟩ := target_affine_near_w u v w hw
  let δ := min δF δT
  have hδ : 0 < δ := lt_min hδF hδT
  have hidentity : ∀ t : ℝ, |t|<δ →
      (∑ j, d.out j * relu
        (wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) (d.gate j)*t+
          form α β κ (d.gate j) u v w)) =
        (a-wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) d.base)*t+
          (b-form α β κ d.base u v w) := by
    intro t ht
    have htF : |t|<δF := lt_of_lt_of_le ht (min_le_left _ _)
    have htT : |t|<δT := lt_of_lt_of_le ht (min_le_right _ _)
    have hh := h u v (w+t)
    rw [hT t htT] at hh
    unfold ResidualSystem.eval at hh
    simp_rw [hF _ t htF] at hh
    linarith only [hh]
  obtain ⟨j,hj,_,_⟩ := exists_negative_active_zero_gate
    (fun j => wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) (d.gate j))
    (fun j => form α β κ (d.gate j) u v w) d.out
    (a-wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) d.base)
    (b-form α β κ d.base u v w) δ hδ hidentity i hi hz hd
  exact ⟨j,hj⟩

end MaxCaterpillar.Fiber.Count65.ForkExclusion
