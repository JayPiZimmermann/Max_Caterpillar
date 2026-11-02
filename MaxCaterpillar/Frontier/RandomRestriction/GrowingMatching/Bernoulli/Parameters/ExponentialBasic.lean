import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Explicit exponential comparisons for the scalar Bernoulli parameters.
All statements concern real numbers, without a presumed probability law. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters

theorem exp_half_le_two : Real.exp (1/2:ℝ) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  norm_num at h ⊢
  exact h

theorem inv_two_le_exp_neg_half : (1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) := by
  rw [Real.exp_neg]
  simpa only [one_div] using inv_le_inv_of_le (Real.exp_pos (1/2:ℝ)) exp_half_le_two

theorem inverse_power_le_exp (q : ℕ) :
    (1/128:ℝ)^q ≤ Real.exp (-(7/2:ℝ)*(q:ℝ)) := by
  have hseven : (1/128:ℝ) ≤ Real.exp (-(7/2:ℝ)) := by
    calc
      (1/128:ℝ) = (1/2:ℝ)^7 := by norm_num
      _ ≤ (Real.exp (-(1/2:ℝ)))^7 :=
        pow_le_pow_left (by norm_num) inv_two_le_exp_neg_half 7
      _ = Real.exp (-(7/2:ℝ)) := by rw [←Real.exp_nat_mul]; norm_num
  calc
    _ ≤ (Real.exp (-(7/2:ℝ)))^q := pow_le_pow_left (by norm_num) hseven q
    _ = Real.exp (-(7/2:ℝ)*(q:ℝ)) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring

/-- Retain the small exponential margin instead of losing it before the
finite counting step. -/
theorem generic_envelope_strong (μ b t : ℝ) (q : ℕ)
    (hb0 : 0 ≤ b) (hb : b ≤ 1/128) (hq : μ/9 ≤ (q:ℝ)) (ht : t ≤ μ/1000) :
    b^q * Real.exp t ≤ Real.exp (-((7/18:ℝ)-1/1000)*μ) := by
  have hp : b^q ≤ Real.exp (-(7/2:ℝ)*(q:ℝ)) :=
    (pow_le_pow_left hb0 hb q).trans (inverse_power_le_exp q)
  calc
    _ ≤ Real.exp (-(7/2:ℝ)*(q:ℝ))*Real.exp t :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-(7/2:ℝ)*(q:ℝ)+t) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hq,ht])

theorem generic_envelope_coarse (μ b t : ℝ) (q : ℕ)
    (hμ : 0 ≤ μ) (hb0 : 0 ≤ b) (hb : b ≤ 1/128)
    (hq : μ/9 ≤ (q:ℝ)) (ht : t ≤ μ/1000) :
    b^q * Real.exp t ≤ Real.exp (-(3*μ/8)) := by
  apply (generic_envelope_strong μ b t q hb0 hb hq ht).trans
  exact Real.exp_le_exp.mpr (by linarith only [hμ])

private theorem exp_neg_le_half (x : ℝ) (hx : 1 ≤ x) : Real.exp (-x) ≤ (1/2:ℝ) := by
  have he : (2:ℝ) ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith only [h,hx]
  rw [Real.exp_neg]
  simpa only [one_div] using inv_le_inv_of_le (by norm_num : (0:ℝ) < 2) he

private theorem exp_six_ge_two_hundred : (200:ℝ) ≤ Real.exp 6 := by
  have he : (5/2:ℝ) ≤ Real.exp 1 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1)
    norm_num at h ⊢
    exact h
  calc
    (200:ℝ) ≤ (5/2:ℝ)^6 := by norm_num
    _ ≤ (Real.exp 1)^6 := pow_le_pow_left (by norm_num) he 6
    _ = Real.exp 6 := by rw [←Real.exp_nat_mul]; norm_num

private theorem exp_neg_le_one_two_hundred (x : ℝ) (hx : 6 ≤ x) :
    Real.exp (-x) ≤ (1/200:ℝ) := by
  have he : (200:ℝ) ≤ Real.exp x :=
    exp_six_ge_two_hundred.trans (Real.exp_le_exp.mpr hx)
  rw [Real.exp_neg]
  simpa only [one_div] using inv_le_inv_of_le (by norm_num : (0:ℝ) < 200) he

/-- The weaker upper-tail exponent μ/6 is already more than sufficient. -/
theorem upper_tail_small_relative (μ : ℝ) (hμ : 100 ≤ μ) :
    Real.exp (-μ/6) ≤ (1/2:ℝ)*Real.exp (-(2/1000000:ℝ)*μ) := by
  have hx : (1:ℝ) ≤ ((1/6:ℝ)-2/1000000)*μ := by linarith only [hμ]
  have hb := exp_neg_le_half _ hx
  calc
    Real.exp (-μ/6) = Real.exp (-(2/1000000:ℝ)*μ)*
        Real.exp (-(((1/6:ℝ)-2/1000000)*μ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(2/1000000:ℝ)*μ)*(1/2:ℝ) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

theorem lower_tail_small_relative (μ : ℝ) (hμ : 100 ≤ μ) :
    Real.exp (-3*μ/40) ≤ (1/200:ℝ)*Real.exp (-(2/1000000:ℝ)*μ) := by
  have hx : (6:ℝ) ≤ ((3/40:ℝ)-2/1000000)*μ := by linarith only [hμ]
  have hb := exp_neg_le_one_two_hundred _ hx
  calc
    Real.exp (-3*μ/40) = Real.exp (-(2/1000000:ℝ)*μ)*
        Real.exp (-(((3/40:ℝ)-2/1000000)*μ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(2/1000000:ℝ)*μ)*(1/200:ℝ) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

/-- A positive lower bound for the actual conditioning denominator. -/
theorem generic_conditioning_mass_lower (μ : ℝ) (hμ : 100 ≤ μ) :
    (1/2:ℝ)*Real.exp (-(2/1000000:ℝ)*μ) ≤
      Real.exp (-(2/1000000:ℝ)*μ)-Real.exp (-μ/6) := by
  have h := upper_tail_small_relative μ hμ
  linarith only [h]

theorem generic_conditioned_size_ratio (μ Z : ℝ) (hμ : 100 ≤ μ)
    (hZ : (1/2:ℝ)*Real.exp (-(2/1000000:ℝ)*μ) ≤ Z) :
    Real.exp (-3*μ/40)/Z ≤ (1/100:ℝ) := by
  have hZpos : 0 < Z := lt_of_lt_of_le
    (mul_pos (by norm_num : (0:ℝ) < 1/2) (Real.exp_pos _)) hZ
  apply (div_le_iff hZpos).mpr
  have h := lower_tail_small_relative μ hμ
  linarith only [h,hZ]

/-- The three explicit conditional error budgets leave more than .9 mass. -/
theorem generic_coverage (bsize bgood bshort : ℝ)
    (hs : bsize ≤ 1/100) (hg : bgood ≤ 1/1000) (hq : bshort ≤ 16/1000) :
    (9/10:ℝ) ≤ 1-bsize-bgood-bshort := by linarith only [hs,hg,hq]

#print axioms generic_envelope_strong
#print axioms generic_conditioned_size_ratio
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Parameters
