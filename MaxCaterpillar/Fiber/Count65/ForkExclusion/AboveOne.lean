import MaxCaterpillar.Fiber.Count65.ForkExclusion.Spurious

/-! # The inward fork above one needs at least four residual ReLUs

Both the positive and negative output signs are consequences of the exact
all-input identity. The witness of the spurious outer crease is explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators MaxCaterpillar.Frontier

lemma OuterU.s_ne_zero {κ : ℝ} {d : Coeff} (h : OuterU κ d) : d.s ≠ 0 := by
  intro hs
  apply h.2.2
  have hz := h.2.1
  rw [hs,mul_zero,add_zero] at hz
  exact hz

lemma OuterU.slope {κ : ℝ} {d : Coeff} (h : OuterU κ d) : d.r+κ*d.s = -d.a := by
  linear_combination h.1+h.2.1

lemma form_outerU_all_active {α β κ u v w : ℝ} {d : Coeff} (h : OuterU κ d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ w-α*u-β*v)
    (hs : 0 ≤ κ*w-α*u-β*v) :
    form α β κ d u v w = d.a*(u-w)+d.b*v := by
  unfold form
  rw [relu_of_nonneg hu,relu_of_nonneg hv,relu_of_nonneg hr,relu_of_nonneg hs]
  linear_combination (w-α*u-β*v)*h.1+w*h.2.1

/-- Every forced outer carrier has a genuine zero crease in a strict feature
cell where the target is smooth. This holds for every real free coefficient. -/
theorem OuterU.spurious_gt_one {α β κ : ℝ} {d : Coeff}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α+β=1) (hκ : 1 < κ)
    (h : OuterU κ d) :
    ∃ u v w : ℝ, w-α*u-β*v ≠ 0 ∧ κ*w-α*u-β*v ≠ 0 ∧
      w ≠ max (max 0 u) v ∧ form α β κ d u v w=0 ∧
      wSlope κ (w-α*u-β*v) (κ*w-α*u-β*v) d ≠ 0 := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hβ1 : β < 1 := by linarith only [hα,hαβ]
  have hα1 : α < 1 := by linarith only [hβ,hαβ]
  by_cases hb : d.b=0
  · let w := 1+β/κ
    have hdv : κ*(β/κ)=β := mul_div_cancel' β hκ0.ne'
    have hdiv : β/κ < β := (div_lt_iff hκ0).mpr (by nlinarith only [hβ,hκ])
    have hdiv1 : β/κ < 1 := lt_trans hdiv hβ1
    have hr : w-α*1-β*2 < 0 := by dsimp [w]; linarith only [hdiv,hαβ]
    have hs : 0 < κ*w-α*1-β*2 := by dsimp [w]; nlinarith only [hdv,hκ,hαβ]
    have hS : κ*w-α*1-β*2=κ-1 := by dsimp [w]; nlinarith only [hdv,hαβ]
    refine ⟨1,2,w,hr.ne,hs.ne',?_,?_,?_⟩
    · norm_num
      linarith only [hdiv1]
    · unfold form
      rw [relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 2),relu_of_nonpos hr.le,
        relu_of_nonneg hs.le,hb,hS]
      have he := h.2.1
      nlinarith only [he]
    · unfold wSlope
      rw [if_neg (not_lt.mpr hr.le),if_pos hs,zero_add]
      exact mul_ne_zero hκ0.ne' h.s_ne_zero
  · let ρ := d.b/d.a
    have hρ : ρ*d.a=d.b := div_mul_cancel _ h.2.2
    have hρ0 : ρ ≠ 0 := div_ne_zero hb h.2.2
    have hκα : 0 < κ-α := by linarith only [hκ,hα1]
    let T := 3+|ρ|+(|ρ|+1)/β+(κ*|ρ|+β+1)/(κ-α)
    have hp : 0 < (|ρ|+1)/β := div_pos (by linarith only [abs_nonneg ρ]) hβ
    have hq : 0 < (κ*|ρ|+β+1)/(κ-α) := div_pos
      (by nlinarith only [mul_nonneg hκ0.le (abs_nonneg ρ),hβ]) hκα
    have hT : 3+|ρ| ≤ T := by dsimp [T]; linarith only [hp,hq]
    have hTp : (|ρ|+1)/β ≤ T-1 := by dsimp [T]; linarith only [hq,abs_nonneg ρ]
    have hTq : (κ*|ρ|+β+1)/(κ-α) ≤ T := by dsimp [T]; linarith only [hp,abs_nonneg ρ]
    have hRbd : |ρ|+1 ≤ (T-1)*β := (div_le_iff hβ).mp hTp
    have hSbd : κ*|ρ|+β+1 ≤ T*(κ-α) := (div_le_iff hκα).mp hTq
    have hρlo : 0 ≤ |ρ|+ρ := by linarith only [neg_abs_le_self ρ]
    have hu : 0 < T := by linarith only [hT,abs_nonneg ρ]
    have hr : 0 < (T+ρ)-α*T-β*1 := by
      have hprod : (α+β)*T=T := by rw [hαβ]; ring
      nlinarith only [hRbd,hρlo,hprod]
    have hs : 0 < κ*(T+ρ)-α*T-β*1 := by
      have hprod : 0 ≤ κ*(|ρ|+ρ) := mul_nonneg hκ0.le hρlo
      nlinarith only [hSbd,hprod]
    refine ⟨T,1,T+ρ,hr.ne',hs.ne',?_,?_,?_⟩
    · rw [max_eq_right hu.le,max_eq_left (by linarith only [hT,abs_nonneg ρ] : (1:ℝ) ≤ T)]
      intro he
      exact hρ0 (by linarith only [he])
    · rw [form_outerU_all_active h hu.le (by norm_num) hr.le hs.le]
      nlinarith only [hρ]
    · unfold wSlope
      rw [if_pos hr,if_pos hs,h.slope]
      exact neg_ne_zero.mpr h.2.2

/-- A negative-output gate is forced by an arbitrary inward-fork identity. -/
theorem ResidualSystem.exists_negative_gt_one {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hκ : 1 < κ) (h : d.Represents α β κ) :
    ∃ i, d.out i < 0 := by
  obtain ⟨i,hi,hO⟩ := d.exists_outerU hβ hαβ hκ h
  obtain ⟨u,v,w,hr,hs,hw,hz,hd⟩ := hO.spurious_gt_one hα hβ hαβ hκ
  exact d.negative_of_spurious (by linarith only [hκ] : 0 < κ) h u v w hr hs hw i hi hz hd

/-- The full arbitrary-real residual obstruction above one. -/
theorem ResidualSystem.card_ge_four_gt_one {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α+β=1) (hκ : 1 < κ) (h : d.Represents α β κ) :
    4 ≤ Fintype.card ι :=
  card_ge_four_of_roles_and_negative d hαβ (d.forced_roles_gt_one hα hβ hαβ hκ h)
    (d.exists_negative_gt_one hα hβ hαβ hκ h)

#print axioms ResidualSystem.card_ge_four_gt_one
end MaxCaterpillar.Fiber.Count65.ForkExclusion
