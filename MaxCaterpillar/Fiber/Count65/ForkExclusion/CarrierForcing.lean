import MaxCaterpillar.Fiber.Count65.ForkExclusion.Roles

/-! # Facet carriers forced by arbitrary real residual identities

This file extracts coefficient equations from all-input identities. The
finite affine-cover argument is applied to an entire open facet, rather than
assuming that a gate selected at one point carries that whole facet.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier

lemma form_shift_w (α β κ : ℝ) (d : Coeff) (u v w t : ℝ)
    (hr : 0 ≤ w-α*u-β*v) (hr' : 0 ≤ (w+t)-α*u-β*v)
    (hs : 0 ≤ κ*w-α*u-β*v) (hs' : 0 ≤ κ*(w+t)-α*u-β*v) :
    form α β κ d u v (w+t) = (d.r+κ*d.s)*t + form α β κ d u v w := by
  unfold form
  rw [relu_of_nonneg hr,relu_of_nonneg hr',relu_of_nonneg hs,relu_of_nonneg hs']
  ring

lemma target_u_shift (v t : ℝ) (hv : v ≤ 1) : target 1 v (1+t) = 1+relu t := by
  unfold target
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 1),← max_assoc,max_eq_left hv]
  rcases le_total 0 t with ht | ht
  · rw [relu_of_nonneg ht,max_eq_right (by linarith)]
  · rw [relu_of_nonpos ht,max_eq_left (by linarith),add_zero]

lemma u_facet_gaps_pos {α β κ v : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ : 1 < κ) (hv : v < 1) :
    0 < 1-α-β*v ∧ 0 < κ-α-β*v := by
  have hp := mul_pos hβ (sub_pos.mpr hv)
  constructor <;> nlinarith only [hp,hαβ,hκ]

/-- Every point of the positive `u=w` facet has a positive-output gate
with a nonzero transverse slope. -/
theorem ResidualSystem.local_u_active_RS {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hκ0 : 0 < κ)
    (h : d.Represents α β κ) (v : ℝ) (hv : v < 1)
    (hr : 0 < 1-α-β*v) (hs : 0 < κ-α-β*v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t|<δ →
      relu t=(d.base.r+κ*d.base.s)*t+(form α β κ d.base 1 v 1-1)+
        ∑ i, d.out i*relu (((d.gate i).r+κ*(d.gate i).s)*t+form α β κ (d.gate i) 1 v 1) := by
  let δ := min (1-α-β*v) ((κ-α-β*v)/κ)
  have hδ : 0 < δ := lt_min hr (div_pos hs hκ0)
  have hδR : δ ≤ 1-α-β*v := min_le_left _ _
  have hδS : δ*κ ≤ κ-α-β*v := (le_div_iff hκ0).mp (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have htlo := (abs_lt.mp ht).1
  have hr' : 0 ≤ (1+t)-α*1-β*v := by linarith only [htlo,hδR]
  have hprod : 0 < (t+δ)*κ := mul_pos (by linarith only [htlo]) hκ0
  have hs' : 0 ≤ κ*(1+t)-α*1-β*v := by nlinarith only [hprod,hδS]
  have hbase := form_shift_w α β κ d.base 1 v 1 t (by simpa using hr.le) hr'
    (by simpa using hs.le) hs'
  have hgate : ∀ i, form α β κ (d.gate i) 1 v (1+t) =
      ((d.gate i).r+κ*(d.gate i).s)*t + form α β κ (d.gate i) 1 v 1 :=
    fun i => form_shift_w α β κ (d.gate i) 1 v 1 t
      (by simpa using hr.le) hr' (by simpa using hs.le) hs'
  have hh := h 1 v (1+t)
  rw [target_u_shift v t hv.le] at hh
  unfold ResidualSystem.eval at hh
  simp_rw [hbase,hgate] at hh
  linarith only [hh]

theorem ResidualSystem.positive_on_u_active_RS {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hκ0 : 0 < κ)
    (h : d.Represents α β κ) (v : ℝ) (hv : v < 1)
    (hr : 0 < 1-α-β*v) (hs : 0 < κ-α-β*v) :
    ∃ i, 0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0 ∧
      form α β κ (d.gate i) 1 v 1 = 0 := by
  obtain ⟨δ,hδ,hid⟩ := d.local_u_active_RS hκ0 h v hv hr hs
  exact exists_positive_active_zero_gate
    (fun i => (d.gate i).r+κ*(d.gate i).s)
    (fun i => form α β κ (d.gate i) 1 v 1) d.out
    (d.base.r+κ*d.base.s) (form α β κ d.base 1 v 1-1) δ hδ hid

theorem ResidualSystem.positive_on_u_facet {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) (v : ℝ) (hv : v < 1) :
    ∃ i, 0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0 ∧
      form α β κ (d.gate i) 1 v 1 = 0 := by
  obtain ⟨hr,hs⟩ := u_facet_gaps_pos (v := v) hβ hαβ hκ hv
  exact d.positive_on_u_active_RS (by linarith only [hκ]) h v hv hr hs

theorem ResidualSystem.exists_outerU {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ OuterU κ (d.gate i) := by
  have hcover : ∀ v ∈ Set.Ioo (-1:ℝ) 0,
      ∃ i, (0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0) ∧
        ((d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s) +
          (-β*((d.gate i).r+(d.gate i).s))*v = 0 := by
    intro v hv
    obtain ⟨i,hi,hd,hz⟩ := d.positive_on_u_facet hβ hαβ hκ h v (by linarith [hv.2])
    obtain ⟨hr,hs⟩ := u_facet_gaps_pos (v := v) hβ hαβ hκ (by linarith [hv.2])
    refine ⟨i,⟨hi,hd⟩,?_⟩
    unfold form at hz
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),relu_of_nonpos hv.2.le,
      relu_of_nonneg (by simpa using hr.le),relu_of_nonneg (by simpa using hs.le)] at hz
    linear_combination hz + (d.gate i).r*hαβ
  obtain ⟨i,⟨hi,hd⟩,hA,hB⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => (d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s)
    (fun i => -β*((d.gate i).r+(d.gate i).s))
    (fun i => 0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0)
    (by norm_num : (-1:ℝ)<0) hcover
  have hrs : (d.gate i).r+(d.gate i).s=0 := by
    have hz : β*((d.gate i).r+(d.gate i).s)=0 := by linarith only [hB]
    exact (mul_eq_zero.mp hz).resolve_left hβ.ne'
  have has : (d.gate i).a+(κ-1)*(d.gate i).s=0 := by
    linear_combination hA - β*hrs + (d.gate i).s*hαβ
  refine ⟨i,hi,hrs,has,?_⟩
  intro ha
  apply hd
  linear_combination has + hrs - ha

theorem ResidualSystem.exists_innerU {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ InnerU α β κ (d.gate i) := by
  have hcover : ∀ v ∈ Set.Ioo (0:ℝ) 1,
      ∃ i, (0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0) ∧
        ((d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s) +
          ((d.gate i).b-β*((d.gate i).r+(d.gate i).s))*v = 0 := by
    intro v hv
    obtain ⟨i,hi,hd,hz⟩ := d.positive_on_u_facet hβ hαβ hκ h v hv.2
    obtain ⟨hr,hs⟩ := u_facet_gaps_pos (v := v) hβ hαβ hκ hv.2
    refine ⟨i,⟨hi,hd⟩,?_⟩
    unfold form at hz
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),relu_of_nonneg hv.1.le,
      relu_of_nonneg (by simpa using hr.le),relu_of_nonneg (by simpa using hs.le)] at hz
    linear_combination hz + (d.gate i).r*hαβ
  obtain ⟨i,⟨hi,hd⟩,hA,hB⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => (d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s)
    (fun i => (d.gate i).b-β*((d.gate i).r+(d.gate i).s))
    (fun i => 0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0)
    (by norm_num : (0:ℝ)<1) hcover
  exact ⟨i,hi,hB,hA,hd⟩

theorem ResidualSystem.exists_outerV {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ OuterV κ (d.gate i) := by
  obtain ⟨i,hi,hg⟩ := d.swap.exists_outerU hα (by linarith : β+α=1) hκ h.swap
  exact ⟨i,hi,hg⟩

theorem ResidualSystem.exists_innerV {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ InnerV α β κ (d.gate i) := by
  obtain ⟨i,hi,hg⟩ := d.swap.exists_innerU hα (by linarith : β+α=1) hκ h.swap
  exact ⟨i,hi,hg⟩

lemma form_shift_u_middle (α β κ : ℝ) (d : Coeff) (w t : ℝ)
    (hu : 0 ≤ 1+t) (hr : w-α*1-β*1 ≤ 0)
    (hr' : w-α*(1+t)-β*1 ≤ 0)
    (hs : 0 ≤ κ*w-α*1-β*1) (hs' : 0 ≤ κ*w-α*(1+t)-β*1) :
    form α β κ d (1+t) 1 w = (d.a-α*d.s)*t + form α β κ d 1 1 w := by
  unfold form
  rw [relu_of_nonneg hu,relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    relu_of_nonpos hr,relu_of_nonpos hr',relu_of_nonneg hs,relu_of_nonneg hs']
  ring

lemma target_middle_shift (w t : ℝ) (hw : w ≤ 1) : target (1+t) 1 w = 1+relu t := by
  unfold target
  rw [max_eq_left hw,max_assoc,
    max_eq_right (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right (1+t) 1)),
    max_comm (1+t) 1]
  rcases le_total 0 t with ht | ht
  · rw [relu_of_nonneg ht,max_eq_right (by linarith)]
  · rw [relu_of_nonpos ht,max_eq_left (by linarith),add_zero]

theorem ResidualSystem.positive_on_middle_facet {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) (w : ℝ)
    (hw : w ∈ Set.Ioo (1/κ) 1) :
    ∃ i, 0 < d.out i ∧ (d.gate i).a-α*(d.gate i).s ≠ 0 ∧
      form α β κ (d.gate i) 1 1 w = 0 := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hwκ : 1 < κ*w := by
    have hh := (div_lt_iff hκ0).mp hw.1
    simpa only [mul_comm] using hh
  let δ := min (1:ℝ) (min ((1-w)/α) ((κ*w-1)/α))
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (div_pos (by linarith only [hw.2]) hα)
      (div_pos (by linarith only [hwκ]) hα))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδR : δ*α ≤ 1-w := (le_div_iff hα).mp
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδS : δ*α ≤ κ*w-1 := (le_div_iff hα).mp
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hr : w-α*1-β*1 ≤ 0 := by linarith only [hαβ,hw.2]
  have hs : 0 ≤ κ*w-α*1-β*1 := by linarith only [hαβ,hwκ]
  apply exists_positive_active_zero_gate
    (fun i => (d.gate i).a-α*(d.gate i).s)
    (fun i => form α β κ (d.gate i) 1 1 w) d.out
    (d.base.a-α*d.base.s) (form α β κ d.base 1 1 w-1) δ hδ
  intro t ht
  obtain ⟨htlo,hthi⟩ := abs_lt.mp ht
  have hu : 0 ≤ 1+t := by linarith only [htlo,hδ1]
  have hpR : 0 < (t+δ)*α := mul_pos (by linarith only [htlo]) hα
  have hpS : 0 < (δ-t)*α := mul_pos (by linarith only [hthi]) hα
  have hr' : w-α*(1+t)-β*1 ≤ 0 := by nlinarith only [hpR,hδR,hαβ]
  have hs' : 0 ≤ κ*w-α*(1+t)-β*1 := by nlinarith only [hpS,hδS,hαβ]
  have hb := form_shift_u_middle α β κ d.base w t hu hr hr' hs hs'
  have hg : ∀ i, form α β κ (d.gate i) (1+t) 1 w =
      ((d.gate i).a-α*(d.gate i).s)*t+form α β κ (d.gate i) 1 1 w :=
    fun i => form_shift_u_middle α β κ (d.gate i) w t hu hr hr' hs hs'
  have hh := h (1+t) 1 w
  rw [target_middle_shift w t hw.2.le] at hh
  unfold ResidualSystem.eval at hh
  simp_rw [hb,hg] at hh
  linarith only [hh]

theorem ResidualSystem.exists_middle {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hαβ : α+β=1)
    (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ Middle (d.gate i) := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hab : (1:ℝ)/κ < 1 := (div_lt_iff hκ0).mpr (by linarith only [hκ])
  have hcover : ∀ w ∈ Set.Ioo (1/κ) 1,
      ∃ i, (0 < d.out i ∧ (d.gate i).a-α*(d.gate i).s ≠ 0) ∧
        ((d.gate i).a+(d.gate i).b-(d.gate i).s) + (κ*(d.gate i).s)*w=0 := by
    intro w hw
    obtain ⟨i,hi,hd,hz⟩ := d.positive_on_middle_facet hα hαβ hκ h w hw
    have hwκ : 1 < κ*w := by
      have hh := (div_lt_iff hκ0).mp hw.1
      simpa only [mul_comm] using hh
    refine ⟨i,⟨hi,hd⟩,?_⟩
    unfold form at hz
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos (by linarith only [hαβ,hw.2] : w-α*1-β*1 ≤ 0),
      relu_of_nonneg (by linarith only [hαβ,hwκ] : 0 ≤ κ*w-α*1-β*1)] at hz
    linear_combination hz + (d.gate i).s*hαβ
  obtain ⟨i,⟨hi,hd⟩,hA,hB⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => (d.gate i).a+(d.gate i).b-(d.gate i).s)
    (fun i => κ*(d.gate i).s)
    (fun i => 0 < d.out i ∧ (d.gate i).a-α*(d.gate i).s ≠ 0) hab hcover
  have hS : (d.gate i).s=0 := (mul_eq_zero.mp hB).resolve_left hκ0.ne'
  refine ⟨i,hi,hS,?_,?_⟩
  · linarith only [hA,hS]
  · simpa only [hS,mul_zero,sub_zero] using hd

/-- The five carrier equations follow from the original all-real-input identity. -/
theorem ResidualSystem.forced_roles_gt_one {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hκ : 1 < κ) (h : d.Represents α β κ) :
    ForcedRoles d α β κ :=
  ⟨d.exists_outerU hβ hαβ hκ h,d.exists_outerV hα hαβ hκ h,
    d.exists_innerU hβ hαβ hκ h,d.exists_innerV hα hαβ hκ h,
    d.exists_middle hα hαβ hκ h⟩

/-- In particular every exact inward-fork residual above one has at least
three different positive-output gates, without assuming any gate signs. -/
theorem ResidualSystem.three_positive_gt_one {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < d.out i ∧ 0 < d.out j ∧ 0 < d.out k :=
  three_positive_of_forced_roles d hαβ (d.forced_roles_gt_one hα hβ hαβ hκ h)

#print axioms ResidualSystem.forced_roles_gt_one
#print axioms ResidualSystem.three_positive_gt_one
end MaxCaterpillar.Fiber.Count65.ForkExclusion
