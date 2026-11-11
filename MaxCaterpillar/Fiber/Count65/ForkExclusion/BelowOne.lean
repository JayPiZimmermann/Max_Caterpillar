import MaxCaterpillar.Fiber.Count65.ForkExclusion.AboveOne

/-! # The inward fork below one, away from the symmetric endpoint -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier Filter Topology

def InnerLowU (β : ℝ) (d : Coeff) : Prop :=
  d.a+β*d.r=0 ∧ d.b-β*d.r=0 ∧ d.r ≠ 0

def InnerLowV (α : ℝ) (d : Coeff) : Prop :=
  d.a-α*d.r=0 ∧ d.b+α*d.r=0 ∧ d.r ≠ 0

lemma form_shift_w_R_only (α β κ : ℝ) (d : Coeff) (v t : ℝ)
    (hr : 0 ≤ 1-α*1-β*v) (hr' : 0 ≤ (1+t)-α*1-β*v)
    (hs : κ*1-α*1-β*v ≤ 0) (hs' : κ*(1+t)-α*1-β*v ≤ 0) :
    form α β κ d 1 v (1+t)=d.r*t+form α β κ d 1 v 1 := by
  unfold form
  rw [relu_of_nonneg hr,relu_of_nonneg hr',relu_of_nonpos hs,relu_of_nonpos hs']
  ring

theorem ResidualSystem.local_u_R_only {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hκ0 : 0 < κ)
    (h : d.Represents α β κ) (v : ℝ) (hv : v < 1)
    (hr : 0 < 1-α-β*v) (hs : κ-α-β*v < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t|<δ →
      relu t=d.base.r*t+(form α β κ d.base 1 v 1-1)+
        ∑ i, d.out i*relu ((d.gate i).r*t+form α β κ (d.gate i) 1 v 1) := by
  let δ := min (1-α-β*v) ((-(κ-α-β*v))/κ)
  have hδ : 0 < δ := lt_min hr (div_pos (neg_pos.mpr hs) hκ0)
  have hδR : δ ≤ 1-α-β*v := min_le_left _ _
  have hδS : δ*κ ≤ -(κ-α-β*v) := (le_div_iff hκ0).mp (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  obtain ⟨htlo,hthi⟩ := abs_lt.mp ht
  have hr' : 0 ≤ (1+t)-α*1-β*v := by linarith only [htlo,hδR]
  have hp : 0 < (δ-t)*κ := mul_pos (by linarith only [hthi]) hκ0
  have hs' : κ*(1+t)-α*1-β*v ≤ 0 := by nlinarith only [hp,hδS]
  have hb := form_shift_w_R_only α β κ d.base v t (by simpa using hr.le) hr'
    (by simpa using hs.le) hs'
  have hg : ∀ i, form α β κ (d.gate i) 1 v (1+t)=
      (d.gate i).r*t+form α β κ (d.gate i) 1 v 1 :=
    fun i => form_shift_w_R_only α β κ (d.gate i) v t
      (by simpa using hr.le) hr' (by simpa using hs.le) hs'
  have hh := h 1 v (1+t)
  rw [target_u_shift v t hv.le] at hh
  unfold ResidualSystem.eval at hh
  simp_rw [hb,hg] at hh
  linarith only [hh]

theorem ResidualSystem.positive_on_u_R_only {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hκ0 : 0 < κ)
    (h : d.Represents α β κ) (v : ℝ) (hv : v < 1)
    (hr : 0 < 1-α-β*v) (hs : κ-α-β*v < 0) :
    ∃ i, 0 < d.out i ∧ (d.gate i).r ≠ 0 ∧ form α β κ (d.gate i) 1 v 1=0 := by
  obtain ⟨δ,hδ,hid⟩ := d.local_u_R_only hκ0 h v hv hr hs
  exact exists_positive_active_zero_gate (fun i => (d.gate i).r)
    (fun i => form α β κ (d.gate i) 1 v 1) d.out d.base.r
    (form α β κ d.base 1 v 1-1) δ hδ hid

theorem ResidualSystem.exists_inner_lowU {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ0 : 0 < κ) (hακ : α ≤ κ) (hκ1 : κ < 1) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ InnerLowU β (d.gate i) := by
  have ha0 : 0 ≤ (κ-α)/β := div_nonneg (by linarith only [hακ]) hβ.le
  have ha1 : (κ-α)/β < 1 := (div_lt_iff hβ).mpr (by linarith only [hκ1,hαβ])
  have hcover : ∀ v ∈ Set.Ioo ((κ-α)/β) 1,
      ∃ i, (0 < d.out i ∧ (d.gate i).r ≠ 0) ∧
        ((d.gate i).a+β*(d.gate i).r)+((d.gate i).b-β*(d.gate i).r)*v=0 := by
    intro v hv
    have hv0 : 0 < v := lt_of_le_of_lt ha0 hv.1
    have hr : 0 < 1-α-β*v := by
      have hp := mul_pos hβ (sub_pos.mpr hv.2)
      nlinarith only [hp,hαβ]
    have hs : κ-α-β*v < 0 := by
      have hh := (div_lt_iff hβ).mp hv.1
      nlinarith only [hh]
    obtain ⟨i,hi,hd,hz⟩ := d.positive_on_u_R_only hκ0 h v hv.2 hr hs
    refine ⟨i,⟨hi,hd⟩,?_⟩
    unfold form at hz
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),relu_of_nonneg hv0.le,
      relu_of_nonneg (by simpa using hr.le),relu_of_nonpos (by simpa using hs.le)] at hz
    linear_combination hz+(d.gate i).r*hαβ
  obtain ⟨i,⟨hi,hd⟩,hA,hB⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => (d.gate i).a+β*(d.gate i).r)
    (fun i => (d.gate i).b-β*(d.gate i).r)
    (fun i => 0 < d.out i ∧ (d.gate i).r ≠ 0) ha1 hcover
  exact ⟨i,hi,hA,hB,hd⟩

theorem ResidualSystem.exists_inner_lowV {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hαβ : α+β=1)
    (hκ0 : 0 < κ) (hβκ : β ≤ κ) (hκ1 : κ < 1) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ InnerLowV α (d.gate i) := by
  obtain ⟨i,hi,hg⟩ := d.swap.exists_inner_lowU hα (by linarith only [hαβ]) hκ0 hβκ hκ1 h.swap
  exact ⟨i,hi,hg.2.1,hg.1,hg.2.2⟩

theorem ResidualSystem.exists_outerU_low {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hβ : 0 < β) (hαβ : α+β=1)
    (hκ0 : 0 < κ) (hακ : α ≤ κ) (h : d.Represents α β κ) :
    ∃ i, 0 < d.out i ∧ OuterU κ (d.gate i) := by
  have hcover : ∀ v ∈ Set.Ioo (-1:ℝ) 0,
      ∃ i, (0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0) ∧
        ((d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s) +
          (-β*((d.gate i).r+(d.gate i).s))*v=0 := by
    intro v hv
    have hr : 0 < 1-α-β*v := by
      have hp := mul_pos hβ (by linarith only [hv.2] : 0 < 1-v)
      nlinarith only [hp,hαβ]
    have hs : 0 < κ-α-β*v := by
      have hp := mul_neg_of_pos_of_neg hβ hv.2
      linarith only [hp,hακ]
    obtain ⟨i,hi,hd,hz⟩ := d.positive_on_u_active_RS hκ0 h v (by linarith only [hv.2]) hr hs
    refine ⟨i,⟨hi,hd⟩,?_⟩
    unfold form at hz
    rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),relu_of_nonpos hv.2.le,
      relu_of_nonneg (by simpa using hr.le),relu_of_nonneg (by simpa using hs.le)] at hz
    linear_combination hz+(d.gate i).r*hαβ
  obtain ⟨i,⟨hi,hd⟩,hA,hB⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => (d.gate i).a+β*(d.gate i).r+(κ-α)*(d.gate i).s)
    (fun i => -β*((d.gate i).r+(d.gate i).s))
    (fun i => 0 < d.out i ∧ (d.gate i).r+κ*(d.gate i).s ≠ 0)
    (by norm_num : (-1:ℝ)<0) hcover
  have hrs : (d.gate i).r+(d.gate i).s=0 := by
    have hz : β*((d.gate i).r+(d.gate i).s)=0 := by linarith only [hB]
    exact (mul_eq_zero.mp hz).resolve_left hβ.ne'
  have has : (d.gate i).a+(κ-1)*(d.gate i).s=0 := by
    linear_combination hA-β*hrs+(d.gate i).s*hαβ
  refine ⟨i,hi,hrs,has,?_⟩
  intro ha
  apply hd
  linear_combination has+hrs-ha

lemma InnerLowU.not_lowV {α β : ℝ} {d : Coeff} (hαβ : α+β=1)
    (hu : InnerLowU β d) : ¬ InnerLowV α d := by
  intro hv
  apply hu.2.2
  linear_combination hu.1-hv.1-d.r*hαβ

lemma OuterU.not_lowU_of_lt {α β κ : ℝ} {d : Coeff} (hαβ : α+β=1)
    (hακ : α < κ) (ho : OuterU κ d) : ¬ InnerLowU β d := by
  intro hi
  have hz : (κ-α)*d.r=0 := by
    linear_combination hi.1-ho.2.1+(κ-1)*ho.1-d.r*hαβ
  exact hi.2.2 ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hακ.ne'))

lemma OuterU.not_lowV_of_lt_one {α κ : ℝ} {d : Coeff} (hα : 0 < α)
    (hκ1 : κ < 1) (ho : OuterU κ d) : ¬ InnerLowV α d := by
  intro hi
  have hz : (κ-1-α)*d.r=0 := by
    linear_combination hi.1-ho.2.1+(κ-1)*ho.1
  exact hi.2.2 ((mul_eq_zero.mp hz).resolve_left (by linarith only [hκ1,hα] : κ-1-α ≠ 0))

/-- Away from the symmetric endpoint, three positive gates are necessary. -/
theorem ResidualSystem.three_positive_low_of_alpha_lt {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hακ : α < κ) (hβκ : β ≤ κ) (hκ1 : κ < 1)
    (h : d.Represents α β κ) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < d.out i ∧ 0 < d.out j ∧ 0 < d.out k := by
  have hκ0 : 0 < κ := lt_trans hα hακ
  obtain ⟨i,hi,hIu⟩ := d.exists_inner_lowU hβ hαβ hκ0 hακ.le hκ1 h
  obtain ⟨j,hj,hIv⟩ := d.exists_inner_lowV hα hαβ hκ0 hβκ hκ1 h
  obtain ⟨k,hk,hO⟩ := d.exists_outerU_low hβ hαβ hκ0 hακ.le h
  refine ⟨i,j,k,?_,?_,?_,hi,hj,hk⟩
  · intro he
    subst j
    exact hIu.not_lowV hαβ hIv
  · intro he
    subst k
    exact hO.not_lowU_of_lt hαβ hακ hIu
  · intro he
    subst k
    exact hO.not_lowV_of_lt_one hα hκ1 hIv

end MaxCaterpillar.Fiber.Count65.ForkExclusion
