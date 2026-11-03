import research.sN.overnight_20261103.h1_tradeoffs.FeedingJoint
import research.sN.overnight_20261103.h1_tradeoffs.AffineFeeding
import research.sN.overnight_20261103.h1_tradeoffs.SqrtCoefficient

/-! Stronger raw first-width tradeoffs from the sharp simultaneous half cost. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction AffineSkipExtension FeedingCore
open GrowingMatching GrowingMatching.Bernoulli
variable {N h₁ h₂ : ℕ}

/-- Only the original feeding width is charged; the sharp falling-four half
budget replaces the older fourth-power estimate. -/
theorem conditional_affine_feeding_sharp (d : ℕ) (hd : 1≤d)
    (hsize : 10000000000*d^2≤N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) d) (Parameters.matchingOrder (N/2) d))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x, AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : 105*affineFeedingCard net≤16*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ)))≤
      (h₂ : ℝ) := by
  letI := originalNeZero N d hd hsize
  letI := halfNeZero N d hd hsize
  obtain ⟨model,hmax,hnorm,hfall,hcount⟩ := exists_feeding_joint_model
    (n:=N/2) (normalizedModel net)
    (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet)
    (by linarith only [Nat.mul_div_le N 2])
  have hf := normalized_feedingCard_le_original net
  have hL : (∑ j, (rowSupport ((core model).A j)).card.descFactorial 4)≤
      d^2*(N/2)^2 := by
    have hh := hfall.trans ((Nat.mul_le_mul_left 105 hf).trans hwidth)
    nlinarith only [hh]
  have hM : nonBraidCount (core model)≤d^2*(N/2)^2 := by
    have hh := (Nat.mul_le_mul_left 105 (hcount.trans hf)).trans hwidth
    nlinarith only [hh]
  apply FeedingBernoulli.conditional_sqrt_lower_bound hd hsize H model hnorm hmax
  · change (nonBraidCount (core model) : ℝ)≤_
    exact_mod_cast hM
  · change (∑ j, ((rowSupport ((core model).A j)).card.descFactorial 4 : ℝ))≤_
    exact_mod_cast hL

def sharpParameter (n h : ℕ) : ℕ := Nat.sqrt (105*h/(16*n^2))+1

lemma sharpParameter_pos (n h : ℕ) : 1≤sharpParameter n h :=
  Nat.succ_le_succ (Nat.zero_le _)

lemma sharpParameter_budget (n h : ℕ) (hn : 0<n) :
    105*h≤16*(sharpParameter n h)^2*n^2 := by
  have hden : 0<16*n^2 := by positivity
  have hs : 105*h/(16*n^2)<(sharpParameter n h)^2 := by
    simpa only [sharpParameter,Nat.succ_eq_add_one] using
      Nat.lt_succ_sqrt' (105*h/(16*n^2))
  have hh := (Nat.div_lt_iff_lt_mul hden).mp hs
  nlinarith only [hh]

/-- Fully explicit raw-network conclusion with unrestricted total first
width. The original W-column count determines the parameter. -/
theorem conditional_affine_feeding_sharp_explicit
    (net : AffineSkipNetwork N h₁ h₂)
    (hsize : 10000000000*(sharpParameter (N/2) (affineFeedingCard net))^2≤N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (sharpParameter (N/2) (affineFeedingCard net)))
      (Parameters.matchingOrder (N/2) (sharpParameter (N/2) (affineFeedingCard net))))
    (hnet : letI := originalNeZero N (sharpParameter (N/2) (affineFeedingCard net)) (sharpParameter_pos _ _) hsize;
      ∀ x, AffineSkipExtension.eval net x=Maximum N x) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (8000*(sharpParameter (N/2) (affineFeedingCard net) : ℝ)))≤(h₂ : ℝ) :=
  conditional_affine_feeding_sharp _ (sharpParameter_pos _ _) hsize H net hnet
    (sharpParameter_budget _ _ (half_pos _ (sharpParameter_pos _ _) hsize))

lemma quadratic_budget_sharp (C s : ℕ) (hC : C≤s^2)
    (hn : 10≤N/2) (hwidth : h₁≤C*N^2) :
    105*h₁≤16*(6*s)^2*(N/2)^2 := by
  have hN : 10*N≤21*(N/2) := by
    have he := Nat.mod_add_div N 2
    have hr := Nat.mod_lt N (by decide : 0<2)
    linarith only [he,hr,hn]
  have hN2 : 100*N^2≤441*(N/2)^2 := by
    have h := Nat.pow_le_pow_left hN 2
    nlinarith only [h]
  have hcoeff : 46305*C≤57600*s^2 := by nlinarith only [hC]
  have hh : 100*(105*h₁)≤100*(16*(6*s)^2*(N/2)^2) := by
    calc
      100*(105*h₁)≤105*C*(100*N^2) := by nlinarith only [hwidth]
      _≤105*C*(441*(N/2)^2) := Nat.mul_le_mul_left _ hN2
      _=(46305*C)*(N/2)^2 := by ring
      _≤(57600*s^2)*(N/2)^2 := Nat.mul_le_mul_right _ hcoeff
      _=100*(16*(6*s)^2*(N/2)^2) := by ring
  nlinarith only [hh]

/-- The quadratic constant is charged as ceil(sqrt(C)), with denominator
48000 instead of the published 160000*C. Total first width is unrestricted. -/
theorem conditional_affine_feeding_sqrt_coefficient (C : ℕ)
    (hsize : 10000000000*(6*sqrtCeiling C)^2≤N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (6*sqrtCeiling C))
      (Parameters.matchingOrder (N/2) (6*sqrtCeiling C)))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N (6*sqrtCeiling C) (by have h := sqrtCeiling_pos C; linarith only [h]) hsize;
      ∀ x, AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : affineFeedingCard net≤C*N^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (48000*(sqrtCeiling C : ℝ)))≤(h₂ : ℝ) := by
  have hd : 1≤6*sqrtCeiling C := by
    have h := sqrtCeiling_pos C
    linarith only [h]
  have hn : 10≤N/2 := by
    have hsq : 1≤(6*sqrtCeiling C)^2 := by nlinarith only [hd]
    nlinarith only [hsq,hsize]
  have h := conditional_affine_feeding_sharp (6*sqrtCeiling C) hd hsize H net hnet
    (quadratic_budget_sharp C (sqrtCeiling C) (le_sqrtCeiling_sq C) hn hwidth)
  have he : (8000 : ℝ)*(6*sqrtCeiling C : ℕ)=48000*(sqrtCeiling C : ℝ) := by
    push_cast
    ring
  simpa only [he] using h

#check @conditional_affine_feeding_sharp_explicit
#check @conditional_affine_feeding_sqrt_coefficient
#print axioms conditional_affine_feeding_sharp
#print axioms sharpParameter_budget
#print axioms conditional_affine_feeding_sharp_explicit
#print axioms conditional_affine_feeding_sqrt_coefficient
end MaxCaterpillar.ExponentialPush.WidthTradeoff
