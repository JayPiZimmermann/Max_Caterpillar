import MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner.Facets
import MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner.Certificate

/-! # Three signed residual gates cannot compute the symmetric inward fork -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner
open BigOperators MaxCaterpillar.Frontier

lemma forced_negative_innerU {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (h : d.Represents (1/2) (1/2) (1/2)) (i j k : ι)
    (hsum : ∀ f : ι→ℝ, ∑ l, f l=f i+f j+f k)
    (hI : InnerLowU (1/2) (d.gate i)) (hOi : OuterU (1/2) (d.gate i))
    (hJ : InnerLowV (1/2) (d.gate j)) (hOj : OuterV (1/2) (d.gate j))
    (hk : d.out k<0) : InnerLowU (1/2) (d.gate k) := by
  classical
  have hout := jump_outerU d h (-1) (by norm_num)
  unfold jumpMass at hout
  rw [hsum] at hout
  dsimp only at hout
  rw [InnerLowU.form_outer hI hOi,InnerLowV.form_outer_other hJ hOj,
    if_pos rfl,if_neg hJ.2.2,mul_zero,add_zero] at hout
  have hneg : d.out k*(if form (1/2) (1/2) (1/2) (d.gate k) 1 (-1) 1=0
      then |(d.gate k).r+(1/2)*(d.gate k).s| else 0) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hk.le (by split_ifs <;> [exact abs_nonneg _; norm_num])
  have hslope : (d.gate i).r+(1/2)*(d.gate i).s=(1/2)*(d.gate i).r := by
    linarith only [hOi.1]
  rw [hslope,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hout
  have hmass : 2 ≤ d.out i*|(d.gate i).r| := by nlinarith only [hout,hneg]
  have hinner : ∀ v : ℝ, 0<v → v<1 →
      d.out i*|(d.gate i).r| + d.out k*
        (if form (1/2) (1/2) (1/2) (d.gate k) 1 v 1=0 then |(d.gate k).r| else 0)=1 := by
    intro v hv0 hv1
    have hjform : form (1/2) (1/2) (1/2) (d.gate j) 1 v 1 ≠ 0 := by
      rw [InnerLowV.form_inner_other hJ v hv0 hv1]
      exact mul_ne_zero hJ.2.2 (sub_pos.mpr hv1).ne'
    have hh := jump_innerU d h v hv0 hv1
    unfold jumpMass at hh
    rw [hsum] at hh
    try dsimp only at hh
    rw [InnerLowU.form_inner hI v hv0 hv1,if_pos rfl,if_neg hjform,mul_zero,add_zero] at hh
    exact hh
  have hzero : ∀ v : ℝ, 0<v → v<1 →
      form (1/2) (1/2) (1/2) (d.gate k) 1 v 1=0 := by
    intro v hv0 hv1
    by_contra hz
    have hh := hinner v hv0 hv1
    rw [if_neg hz,mul_zero,add_zero] at hh
    linarith only [hh,hmass]
  have hz1 := hzero (1/4) (by norm_num) (by norm_num)
  have hz2 := hzero (3/4) (by norm_num) (by norm_num)
  norm_num [form,relu] at hz1 hz2
  refine ⟨?_,?_,?_⟩
  · linarith only [hz1,hz2]
  · linarith only [hz1,hz2]
  · intro hr
    have hh := hinner (1/2) (by norm_num) (by norm_num)
    simp only [hr,abs_zero,ite_self,mul_zero,add_zero] at hh
    linarith only [hh,hmass]

/-- The symmetric endpoint requires at least four arbitrary signed residual
ReLUs. The finite certificate supplies the necessary negative gate. -/
theorem card_ge_four_corner {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (h : d.Represents (1/2) (1/2) (1/2)) : 4 ≤ Fintype.card ι := by
  classical
  by_contra hc
  have hcard : Fintype.card ι≤3 := Nat.le_of_lt_succ (lt_of_not_ge hc)
  obtain ⟨i,hi,hI⟩ := d.exists_inner_lowU (by norm_num) (by norm_num)
    (by norm_num) (le_refl (1/2:ℝ)) (by norm_num) h
  obtain ⟨j,hj,hJ⟩ := d.exists_inner_lowV (by norm_num) (by norm_num)
    (by norm_num) (le_refl (1/2:ℝ)) (by norm_num) h
  obtain ⟨k,hk⟩ := d.exists_negative_corner h
  have hij : i≠j := by intro he; subst j; exact hI.not_lowV (by norm_num) hJ
  have hik : i≠k := by intro he; subst k; linarith only [hi,hk]
  have hjk : j≠k := by intro he; subst k; linarith only [hj,hk]
  have hsum : ∀ f : ι→ℝ, ∑ l, f l=f i+f j+f k := sum_eq_three hcard i j k hij hik hjk
  have hall : ∀ e : ι, e=i ∨ e=j ∨ e=k := by
    intro e
    have hh : (∑ l : ι, if l=e then (1:ℝ) else 0)=1 := by simp
    rw [hsum] at hh
    try dsimp only at hh
    by_cases hei : e=i
    · exact Or.inl hei
    by_cases hej : e=j
    · exact Or.inr (Or.inl hej)
    by_cases hek : e=k
    · exact Or.inr (Or.inr hek)
    simp only [if_neg (Ne.symm hei),if_neg (Ne.symm hej),if_neg (Ne.symm hek)] at hh
    norm_num at hh
  obtain ⟨e,he,hO⟩ := d.exists_outerU_low (by norm_num) (by norm_num)
    (by norm_num) (le_refl (1/2:ℝ)) h
  have hOi : OuterU (1/2) (d.gate i) := by
    rcases hall e with hei | hej | hek
    · simpa only [hei] using hO
    · subst e
      exact (hO.not_lowV_of_lt_one (by norm_num) (by norm_num) hJ).elim
    · subst e
      linarith only [he,hk]
  obtain ⟨e,he,hO⟩ := d.swap.exists_outerU_low (by norm_num) (by norm_num)
    (by norm_num) (le_refl (1/2:ℝ)) h.swap
  have hOv : OuterV (1/2) (d.gate e) := hO
  have hOj : OuterV (1/2) (d.gate j) := by
    rcases hall e with hei | hej | hek
    · subst e
      exact (OuterV.not_lowU hOv hI).elim
    · simpa only [hej] using hOv
    · subst e
      change 0<d.out k at he
      linarith only [he,hk]
  have hIk := forced_negative_innerU d h i j k hsum hI hOi hJ hOj hk
  have hsum' : ∀ f : ι→ℝ, ∑ l, f l=f j+f i+f k := by
    intro f
    rw [hsum]
    ring
  have hJ' : InnerLowU (1/2) (d.swap.gate j) := ⟨hJ.2.1,hJ.1,hJ.2.2⟩
  have hI' : InnerLowV (1/2) (d.swap.gate i) := ⟨hI.2.1,hI.1,hI.2.2⟩
  have hK' := forced_negative_innerU d.swap h.swap j i k hsum' hJ' hOj hI' hOi hk
  have hVk : InnerLowV (1/2) (d.gate k) := ⟨hK'.2.1,hK'.1,hK'.2.2⟩
  exact hIk.not_lowV (by norm_num) hVk

#print axioms card_ge_four_corner
end MaxCaterpillar.Fiber.Count65.ForkExclusion.Corner

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
 theorem ResidualSystem.card_ge_four_corner {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (h : d.Represents (1/2) (1/2) (1/2)) : 4≤Fintype.card ι :=
  Corner.card_ge_four_corner d h
end MaxCaterpillar.Fiber.Count65.ForkExclusion
