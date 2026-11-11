import MaxCaterpillar.Fiber.Count65.ForkExclusion.BelowOne

/-! # Spurious creases below one away from the symmetric endpoint -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier Filter Topology

lemma form_lowU_all_active {α β κ u v w : ℝ} {d : Coeff}
    (hαβ : α+β=1) (h : InnerLowU β d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : 0 ≤ w-α*u-β*v) (hs : 0 ≤ κ*w-α*u-β*v) :
    form α β κ d u v w=d.r*(w-u)+d.s*(κ*w-α*u-β*v) := by
  unfold form
  rw [relu_of_nonneg hu,relu_of_nonneg hv,relu_of_nonneg hr,relu_of_nonneg hs]
  linear_combination u*h.1+v*h.2.1-u*d.r*hαβ

/-- The same strict-cell cancellation test in the `v` direction. -/
theorem ResidualSystem.negative_at_v_spurious {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ v : ℝ} (hβ : 0 < β)
    (h : d.Represents α β κ) (hv : v ∈ Set.Ioo (0:ℝ) 2)
    (hr : 0 < 2-α*1-β*v) (hs : 0 < κ*2-α*1-β*v)
    (i : ι) (hi : 0 < d.out i) (hz : form α β κ (d.gate i) 1 v 2=0)
    (hd : (d.gate i).b-β*((d.gate i).r+(d.gate i).s) ≠ 0) :
    ∃ j, d.out j < 0 := by
  let δ := min v (min (2-v) (min ((2-α*1-β*v)/β) ((κ*2-α*1-β*v)/β)))
  have hδ : 0 < δ := lt_min hv.1 (lt_min (by linarith only [hv.2])
    (lt_min (div_pos hr hβ) (div_pos hs hβ)))
  have hδv : δ ≤ v := min_le_left _ _
  have hδ2 : δ ≤ 2-v := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδR : δ*β ≤ 2-α*1-β*v := (le_div_iff hβ).mp
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδS : δ*β ≤ κ*2-α*1-β*v := (le_div_iff hβ).mp
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hforms : ∀ e : Coeff, ∀ t : ℝ, |t|<δ →
      form α β κ e 1 (v+t) 2=(e.b-β*(e.r+e.s))*t+form α β κ e 1 v 2 := by
    intro e t ht
    obtain ⟨htlo,hthi⟩ := abs_lt.mp ht
    have hvt : 0 ≤ v+t := by linarith only [htlo,hδv]
    have hp : 0 < (δ-t)*β := mul_pos (by linarith only [hthi]) hβ
    have hr' : 0 ≤ 2-α*1-β*(v+t) := by nlinarith only [hp,hδR]
    have hs' : 0 ≤ κ*2-α*1-β*(v+t) := by nlinarith only [hp,hδS]
    unfold form
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),relu_of_nonneg hv.1.le,
      relu_of_nonneg hvt,relu_of_nonneg hr.le,relu_of_nonneg hr',
      relu_of_nonneg hs.le,relu_of_nonneg hs']
    ring
  have hid : ∀ t : ℝ, |t|<δ →
      (∑ j, d.out j*relu (((d.gate j).b-β*((d.gate j).r+(d.gate j).s))*t+
        form α β κ (d.gate j) 1 v 2)) =
        (-(d.base.b-β*(d.base.r+d.base.s)))*t+(2-form α β κ d.base 1 v 2) := by
    intro t ht
    have hvt : v+t ≤ 2 := by linarith only [(abs_lt.mp ht).2,hδ2]
    have hh := h 1 (v+t) 2
    change max (max 0 1) (max (v+t) 2)=_ at hh
    rw [max_eq_right (by norm_num : (0:ℝ) ≤ 1),max_eq_right hvt,
      max_eq_right (by norm_num : (1:ℝ) ≤ 2)] at hh
    unfold ResidualSystem.eval at hh
    simp_rw [hforms _ t ht] at hh
    linarith only [hh]
  obtain ⟨j,hj,_,_⟩ := exists_negative_active_zero_gate
    (fun j => (d.gate j).b-β*((d.gate j).r+(d.gate j).s))
    (fun j => form α β κ (d.gate j) 1 v 2) d.out
    (-(d.base.b-β*(d.base.r+d.base.s))) (2-form α β κ d.base 1 v 2)
    δ hδ hid i hi hz hd
  exact ⟨j,hj⟩

/-- A low inner carrier with nonzero all-active w slope has a spurious
w-transverse crease whenever kappa exceeds alpha. -/
theorem InnerLowU.spurious_low_w {α β κ : ℝ} {d : Coeff}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α+β=1)
    (hακ : α < κ) (hκ1 : κ < 1) (h : InnerLowU β d)
    (hW : d.r+κ*d.s ≠ 0) :
    ∃ u v w : ℝ, w-α*u-β*v ≠ 0 ∧ κ*w-α*u-β*v ≠ 0 ∧
      w ≠ max (max 0 u) v ∧ form α β κ d u v w=0 ∧
      wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) d ≠ 0 := by
  have hα1 : α < 1 := by linarith only [hβ,hαβ]
  by_cases hS : d.s=0
  · have hr : 0 < α-α*1-β*(-1) := by linarith only [hβ]
    have hs : 0 < κ*α-α*1-β*(-1) := by
      have hp := mul_pos hβ (sub_pos.mpr hκ1)
      have he : κ*α-α+β=(κ-α)+β*(1-κ) := by
        linear_combination κ*hαβ
      nlinarith only [hp,hακ,he]
    refine ⟨1,-1,α,hr.ne',hs.ne',?_,?_,?_⟩
    · norm_num
      exact hα1.ne
    · unfold form
      rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
        relu_of_nonpos (by norm_num : (-1:ℝ) ≤ 0),relu_of_nonneg hr.le,
        relu_of_nonneg hs.le,hS]
      have hh := h.1
      nlinarith only [hh]
    · unfold wSlope
      rw [if_pos hr,if_pos hs,hS,mul_zero,add_zero]
      exact h.2.2
  · let v0 := (κ-α)/β
    have hv0 : 0 < v0 := div_pos (sub_pos.mpr hακ) hβ
    have hv1 : v0 < 1 := (div_lt_iff hβ).mpr (by linarith only [hκ1,hαβ])
    have hm0 : α+β*v0=κ := by
      have he : β*v0=κ-α := mul_div_cancel' _ hβ.ne'
      linarith only [he]
    let Cv := -d.r*(d.r+κ*d.s)
    let Cw := -β*d.r*d.s
    let CR := Cw-β*Cv
    have hη : 0 < min v0 (1-v0) := lt_min hv0 (by linarith only [hv1])
    have hall := (eventually_small Cv hη).and
      ((eventually_small CR (by linarith only [hκ1] : 0 < 1-κ)).and
        (Ioo_mem_nhdsWithin_Ioi (show (0:ℝ) ∈ Set.Ico 0 1 from ⟨le_rfl,by norm_num⟩)))
    obtain ⟨t,htv,htr,ht0,_⟩ := hall.exists
    let v := v0+t*Cv
    let w := 1+t*Cw
    have hv : 0 < v := by
      have hb := lt_of_lt_of_le htv (min_le_left _ _)
      change 0 < v0+t*Cv
      linarith only [(abs_lt.mp hb).1]
    have hv' : v < 1 := by
      have hb := lt_of_lt_of_le htv (min_le_right _ _)
      change v0+t*Cv < 1
      linarith only [(abs_lt.mp hb).2]
    have heR : w-α*1-β*v=(1-κ)+t*CR := by
      dsimp [w,v,CR]
      linear_combination -hm0
    have heS : κ*w-α*1-β*v=β*d.r^2*t := by
      dsimp [w,v,Cv,Cw]
      linear_combination -hm0
    have hr : 0 < w-α*1-β*v := by
      rw [heR]
      linarith only [(abs_lt.mp htr).1]
    have hs : 0 < κ*w-α*1-β*v := by
      rw [heS]
      exact mul_pos (mul_pos hβ (sq_pos_of_ne_zero d.r h.2.2)) ht0
    have hCw : Cw ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hβ.ne') h.2.2) hS
    refine ⟨1,v,w,hr.ne',hs.ne',?_,?_,?_⟩
    · rw [max_eq_right (by norm_num : (0:ℝ) ≤ 1),max_eq_left hv'.le]
      intro he
      have hz : t*Cw=0 := by change 1+t*Cw=1 at he; linarith only [he]
      exact (mul_ne_zero ht0.ne' hCw) hz
    · rw [form_lowU_all_active hαβ h (by norm_num) hv.le hr.le hs.le,heS]
      dsimp [w,Cw]
      ring
    · unfold wSlope
      rw [if_pos hr,if_pos hs]
      exact hW

/-- In the exceptional zero-w-slope case, the transverse v crease is nonzero. -/
theorem ResidualSystem.negative_of_inner_lowU {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hακ : α < κ) (hκ1 : κ < 1)
    (h : d.Represents α β κ) (i : ι) (hi : 0 < d.out i)
    (hI : InnerLowU β (d.gate i)) : ∃ j, d.out j < 0 := by
  have hκ0 : 0 < κ := lt_trans hα hακ
  by_cases hW : (d.gate i).r+κ*(d.gate i).s=0
  · let v0 := (κ-α)/β
    have hv0 : 0 < v0 := div_pos (sub_pos.mpr hακ) hβ
    have hv1 : v0 < 1 := (div_lt_iff hβ).mpr (by linarith only [hκ1,hαβ])
    have hm0 : α+β*v0=κ := by
      have he : β*v0=κ-α := mul_div_cancel' _ hβ.ne'
      linarith only [he]
    have hr : 0 < 2-α*1-β*v0 := by linarith only [hm0,hκ1]
    have hs : 0 < κ*2-α*1-β*v0 := by linarith only [hm0,hκ0]
    have hz : form α β κ (d.gate i) 1 v0 2=0 := by
      rw [form_lowU_all_active hαβ hI (by norm_num) hv0.le hr.le hs.le]
      linear_combination hW-(d.gate i).s*hm0
    have hS : (d.gate i).s ≠ 0 := by
      intro he
      apply hI.2.2
      rw [he,mul_zero,add_zero] at hW
      exact hW
    have hd : (d.gate i).b-β*((d.gate i).r+(d.gate i).s) ≠ 0 := by
      have he : (d.gate i).b-β*((d.gate i).r+(d.gate i).s) = -β*(d.gate i).s := by
        linear_combination hI.2.1
      rw [he]
      exact mul_ne_zero (neg_ne_zero.mpr hβ.ne') hS
    exact d.negative_at_v_spurious hβ h ⟨hv0,by linarith only [hv1]⟩ hr hs i hi hz hd
  · obtain ⟨u,v,w,hr,hs,hw,hz,hd⟩ := hI.spurious_low_w hα hβ hαβ hακ hκ1 hW
    exact d.negative_of_spurious hκ0 h u v w hr hs hw i hi hz hd

theorem ResidualSystem.card_ge_four_low_of_alpha_lt {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hακ : α < κ) (hβκ : β ≤ κ) (hκ1 : κ < 1)
    (h : d.Represents α β κ) : 4 ≤ Fintype.card ι := by
  classical
  have hκ0 : 0 < κ := lt_trans hα hακ
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := d.three_positive_low_of_alpha_lt
    hα hβ hαβ hακ hβκ hκ1 h
  obtain ⟨l,hl,hI⟩ := d.exists_inner_lowU hβ hαβ hκ0 hακ.le hκ1 h
  obtain ⟨n,hn⟩ := d.negative_of_inner_lowU hα hβ hαβ hακ hκ1 h l hl hI
  have hin : i ≠ n := by intro he; subst n; linarith only [hi,hn]
  have hjn : j ≠ n := by intro he; subst n; linarith only [hj,hn]
  have hkn : k ≠ n := by intro he; subst n; linarith only [hk,hn]
  have hc : ({i,j,k,n} : Finset ι).card=4 := by simp [hij,hik,hjk,hin,hjn,hkn]
  have hle := Finset.card_le_of_subset (Finset.subset_univ ({i,j,k,n} : Finset ι))
  simpa only [hc,Finset.card_univ] using hle

theorem ResidualSystem.card_ge_four_low_of_beta_lt {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hακ : α ≤ κ) (hβκ : β < κ) (hκ1 : κ < 1)
    (h : d.Represents α β κ) : 4 ≤ Fintype.card ι :=
  d.swap.card_ge_four_low_of_alpha_lt hβ hα (by linarith only [hαβ]) hβκ hακ hκ1 h.swap

#print axioms ResidualSystem.card_ge_four_low_of_alpha_lt
#print axioms ResidualSystem.card_ge_four_low_of_beta_lt
end MaxCaterpillar.Fiber.Count65.ForkExclusion
