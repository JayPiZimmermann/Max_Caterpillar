import research.sN.overnight_20261103.constants.tradeoff_theta.Min
import MaxCaterpillar.Frontier.GeneralN

/-! Width-product lower bounds without any upper bound on either width. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta
open Frontier Frontier.RandomRestriction AffineSkipExtension
variable {N h₁ h₂ : ℕ}

private theorem product_of_min_tradeoff (x h y : ℝ) (hx : 0<x)
    (hfirst : x/4≤h) (hbound : min x (x^2/h)/175000≤y) :
    x^2/700000≤h*y := by
  have hh : 0<h := lt_of_lt_of_le (div_pos hx (by norm_num)) hfirst
  have hp := mul_le_mul_of_nonneg_left hbound hh.le
  rw [←mul_div_assoc,mul_min_of_nonneg _ _ hh.le] at hp
  have hc : h*(x^2/h)=x^2 := by field_simp [hh.ne']; ring
  rw [hc] at hp
  have hl : x^2/4≤h*x := by
    have hs := mul_le_mul_of_nonneg_right hfirst hx.le
    nlinarith only [hs]
  have hr : x^2/4≤x^2 := by nlinarith only [sq_nonneg x]
  have hm := div_le_div_of_le (by norm_num : (0:ℝ)≤175000) (le_min hl hr)
  have ht := hm.trans hp
  convert ht using 1 <;> ring

/-- In the ordinary model, the original first width is at least N²/4
for N≥6. This uses the previously verified first-width lower bound. -/
theorem ordinary_first_quarter [NeZero N] (hN : 6≤N)
    (net : Network N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x) :
    (N:ℝ)^2/4≤(h₁:ℝ) := by
  have hf : 3*(N:ℝ)*(N:ℝ)+12≤6*(h₁:ℝ)+11*(N:ℝ) := by
    exact_mod_cast first_width_quadratic net hnet
  have hn : (6:ℝ)≤N := by exact_mod_cast hN
  have hp : 0≤((N:ℝ)-6)*(3*(N:ℝ)-4) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hn])
  linarith only [hf,hp]

/-- The affine-skip encoding adds 2N first slots. Keeping that exact loss
still gives a quarter-quadratic original first width for N≥15. -/
theorem affine_first_quarter [NeZero N] (hN : 15≤N)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,AffineSkipExtension.eval net x=Maximum N x) :
    (N:ℝ)^2/4≤(h₁:ℝ) := by
  have he : ∀ x,(encode net).eval x=Maximum N x :=
    fun x => (encode_eval net x).trans (hnet x)
  have hf : 3*(N:ℝ)*(N:ℝ)+12≤6*((h₁:ℝ)+(N:ℝ)+(N:ℝ))+11*(N:ℝ) := by
    exact_mod_cast first_width_quadratic (encode net) he
  have hn : (15:ℝ)≤N := by exact_mod_cast hN
  have hp : 0≤((N:ℝ)-15)*(3*(N:ℝ)-1) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hn])
  linarith only [hf,hp]

/-- No first-width cap: every ordinary exact MAX network has quartic width product. -/
theorem ordinary_width_product (hN : 6≤N) (net : Network N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<6) hN)⟩
    (∀ x,net.eval x=Maximum N x) →
    (N:ℝ)^4/700000≤(h₁:ℝ)*(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<6) hN)⟩
  intro hnet
  have hm : ∀ x,AffineSkipExtension.eval (ofOrdinary net) x=Maximum N x :=
    fun x => (eval_ofOrdinary net x).trans (hnet x)
  have hb := affine_min_tradeoff ((by decide : 3≤6).trans hN) (ofOrdinary net) hm
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by decide : 0<6) hN
  have heq : ((N:ℝ)^2)^2=(N:ℝ)^4 := by ring
  rw [←heq] at hb
  have hh := product_of_min_tradeoff ((N:ℝ)^2) (h₁:ℝ) (h₂:ℝ)
    (pow_pos hn 2) (ordinary_first_quarter hN net hnet) hb
  simpa only [heq] using hh

/-- Arbitrary affine skips and biases, no width cap, original widths counted. -/
theorem affine_width_product (hN : 15≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<15) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (N:ℝ)^4/700000≤(h₁:ℝ)*(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<15) hN)⟩
  intro hnet
  have hb := affine_min_tradeoff ((by decide : 3≤15).trans hN) net hnet
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by decide : 0<15) hN
  have heq : ((N:ℝ)^2)^2=(N:ℝ)^4 := by ring
  rw [←heq] at hb
  have hh := product_of_min_tradeoff ((N:ℝ)^2) (h₁:ℝ) (h₂:ℝ)
    (pow_pos hn 2) (affine_first_quarter hN net hnet) hb
  simpa only [heq] using hh

#check @ordinary_width_product
#check @affine_width_product
#print axioms ordinary_first_quarter
#print axioms affine_first_quarter
#print axioms ordinary_width_product
#print axioms affine_width_product
end MaxCaterpillar.OvernightConstants.TradeoffTheta
