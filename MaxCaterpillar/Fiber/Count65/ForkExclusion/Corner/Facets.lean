import MaxCaterpillar.Fiber.Count65.ForkExclusion.BelowOne
import MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner.Jump

/-! # Exact corner jump balances on inner and outer target facets -/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
open BigOperators MaxCaterpillar.Frontier

 theorem jump_innerU {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (h : d.Represents (1/2) (1/2) (1/2)) (v : ℝ) (hv0 : 0<v) (hv1 : v<1) :
    jumpMass (fun i => (d.gate i).r)
      (fun i => form (1/2) (1/2) (1/2) (d.gate i) 1 v 1) d.out=1 := by
  obtain ⟨δ,hδ,hid⟩ := d.local_u_R_only (by norm_num) h v hv1
    (by linarith only [hv1]) (by linarith only [hv0])
  exact jumpMass_eq_one _ _ _ d.base.r
    (form (1/2) (1/2) (1/2) d.base 1 v 1-1) δ hδ hid

 theorem jump_outerU {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (h : d.Represents (1/2) (1/2) (1/2)) (v : ℝ) (hv : v<0) :
    jumpMass (fun i => (d.gate i).r+(1/2)*(d.gate i).s)
      (fun i => form (1/2) (1/2) (1/2) (d.gate i) 1 v 1) d.out=1 := by
  obtain ⟨δ,hδ,hid⟩ := d.local_u_active_RS (by norm_num) h v (by linarith only [hv])
    (by linarith only [hv]) (by linarith only [hv])
  exact jumpMass_eq_one _ _ _ (d.base.r+(1/2)*d.base.s)
    (form (1/2) (1/2) (1/2) d.base 1 v 1-1) δ hδ hid

lemma InnerLowU.form_inner {d : Coeff} (h : InnerLowU (1/2) d)
    (v : ℝ) (hv0 : 0<v) (hv1 : v<1) : form (1/2) (1/2) (1/2) d 1 v 1=0 := by
  unfold form
  rw [relu_of_nonneg (by norm_num : (0:ℝ)≤1),relu_of_nonneg hv0.le,
    relu_of_nonneg (by linarith only [hv1] : (0:ℝ)≤1-(1/2)*1-(1/2)*v),
    relu_of_nonpos (by linarith only [hv0] : (1/2)*1-(1/2)*1-(1/2)*v≤(0:ℝ))]
  linear_combination h.1+v*h.2.1

lemma InnerLowV.form_inner_other {d : Coeff} (h : InnerLowV (1/2) d)
    (v : ℝ) (hv0 : 0<v) (hv1 : v<1) :
    form (1/2) (1/2) (1/2) d 1 v 1=d.r*(1-v) := by
  unfold form
  rw [relu_of_nonneg (by norm_num : (0:ℝ)≤1),relu_of_nonneg hv0.le,
    relu_of_nonneg (by linarith only [hv1] : (0:ℝ)≤1-(1/2)*1-(1/2)*v),
    relu_of_nonpos (by linarith only [hv0] : (1/2)*1-(1/2)*1-(1/2)*v≤(0:ℝ))]
  linear_combination h.1+v*h.2.1

lemma InnerLowU.form_outer {d : Coeff} (h : InnerLowU (1/2) d)
    (ho : OuterU (1/2) d) : form (1/2) (1/2) (1/2) d 1 (-1) 1=0 := by
  norm_num [form,relu]
  linear_combination h.1+(1/2)*ho.1

lemma InnerLowV.form_outer_other {d : Coeff} (h : InnerLowV (1/2) d)
    (ho : OuterV (1/2) d) : form (1/2) (1/2) (1/2) d 1 (-1) 1=d.r := by
  norm_num [form,relu]
  linear_combination h.1+(1/2)*ho.1

lemma sum_eq_three {ι : Type*} [Fintype ι] (hc : Fintype.card ι≤3)
    (i j k : ι) (hij : i≠j) (hik : i≠k) (hjk : j≠k) (f : ι→ℝ) :
    ∑ l, f l=f i+f j+f k := by
  classical
  have hs : ({i,j,k} : Finset ι).card=3 := by simp [hij,hik,hjk,add_assoc]
  have he : ({i,j,k} : Finset ι)=Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by simpa only [Finset.card_univ,hs] using hc)
  rw [← he]
  simp [hij,hik,hjk,add_assoc]

lemma OuterV.not_lowU {d : Coeff} (ho : OuterV (1/2) d) : ¬ InnerLowU (1/2) d := by
  intro hi
  have hO : OuterU (1/2) d.swap := ho
  have hI : InnerLowV (1/2) d.swap := ⟨hi.2.1,hi.1,hi.2.2⟩
  exact hO.not_lowV_of_lt_one (by norm_num) (by norm_num) hI

end MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
