import research.sN.overnight_20261103.constants.tradeoff_theta.Coverage
import research.sN.overnight_20261103.constants.tradeoff_theta.Parameters
import research.sN.overnight_20261103.constants.tradeoff_theta.Scalar
import research.sN.overnight_20261103.constants.ThetaEnvelope
import research.sN.overnight_20261103.constants.cherry_concentration.Theta
import research.sN.overnight_20261103.constants.ThetaTwoTransfer
import research.sN.overnight_20261103.constants.ThetaTwoFeeding
import research.sN.overnight_20261103.h1_tradeoffs.FeedingJoint
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! Unconditional quadratic tradeoff charged only to original feeding rows.
The restriction, cutoff and five-input obstruction are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding
open BigOperators Frontier Frontier.RandomRestriction
open GrowingMatching NormalizedNetwork AffineSkipExtension FeedingCore
variable {N m h₁ h₂ : ℕ}

local instance feedingScaledTailNeZero (m : ℕ) : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

theorem model_bound_scaled (C : ℝ) (hC : 1≤C) (hm : 20000*C≤(m:ℝ))
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports (core net)):ℝ)≤C*(m:ℝ)^2)
    (hL : (∑ j,((firstSupports (core net) j).card.descFactorial 4:ℝ))≤27*C*(m:ℝ)^2) :
    (m:ℝ)^2≤42200*C*(h₂:ℝ) := by
  have hC0 : 0≤C := by linarith only [hC]
  have hmR : (20000:ℝ)≤m := by linarith only [hm,hC]
  have hmNat : 20000≤m := by exact_mod_cast hmR
  let K := cutoff m C
  obtain ⟨hK50,hKm,hKu,hKsq,hmsq⟩ := cutoff_bounds m C hC hm
  change 50≤K at hK50
  change K<m at hKm
  change (K:ℝ)≤(m:ℝ)/10 at hKu
  change 100*C*(K:ℝ)^2≤(m:ℝ)^2 at hKsq
  change (m:ℝ)^2≤101*C*(K:ℝ)^2 at hmsq
  have hKp : 0<K := lt_of_lt_of_le (by decide : 0<50) hK50
  have hK0 : (0:ℝ)<K := by exact_mod_cast hKp
  have h10K : 10*K≤m := by
    have hh : (10:ℝ)*(K:ℝ)≤m := by linarith only [hKu]
    exact_mod_cast hh
  have hQ : ((Overnight.Constants.Theta.highShortRankEvent 5 m K).card:ℝ)/
      Fintype.card (Configurations.Configuration 5 m)≤(1/16:ℝ) := by
    rw [Overnight.Constants.Theta.highShortRankEvent_fraction]
    exact CherryConcentration.highBad_fraction_le_sixteenth hmNat hK50 h10K
  have ht := Overnight.Constants.Theta.Feeding.finite_transfer_of_highShortRank_bound
    net hn hnet K ((by decide : 2≤20000).trans hmNat) hKp hKm
    (1/16:ℝ) hQ
  have hcov := coverage m K C hC hm hKu hKsq
    (GrowingMatching.BadFirst.largeSupportCount (firstSupports (core net)):ℝ)
    (∑ j,((firstSupports (core net) j).card.descFactorial 4:ℝ)) hM hL
  have henv := OvernightConstants.Theta.envelope_le m K
    ((by decide : 501≤20000).trans hmNat) hKp hKu
  have hc : (5/8:ℝ)≤(h₂:ℝ)*(261/(K:ℝ)^2) := by
    apply hcov.trans
    apply ht.trans
    simpa only [Overnight.Constants.Theta.highTailRate,mul_assoc] using mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg h₂)
  have hksq : 5*(K:ℝ)^2≤2088*(h₂:ℝ) := by
    have hh : (5/8:ℝ)*(K:ℝ)^2≤(h₂:ℝ)*261 :=
      (le_div_iff (pow_pos hK0 2)).mp (by simpa only [mul_div_assoc] using hc)
    linarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hksq hC0
  have hp : 0≤C*(h₂:ℝ) := mul_nonneg hC0 (Nat.cast_nonneg _)
  linarith only [hmsq,hh,hp]

/-- All normalized exact MAX models, with any real scale C≥1. -/
theorem normalized_scaled [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (C : ℝ) (hC : 1≤C) (hwidth : (feedingCard net:ℝ)≤C*(N:ℝ)^2) :
    (N:ℝ)^2/(175000*C)≤(h₂:ℝ) := by
  have hC0 : 0<C := by linarith only [hC]
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hlinear : (N:ℝ)≤2*(h₂:ℝ)+2 := by
    exact_mod_cast FeedingCore.normalized_linear_bound net hnet
  by_cases hsmall : (N:ℝ)≤50000*C
  · exact scaled_linear_absorption (N:ℝ) C (h₂:ℝ) hNr hC
      (Nat.cast_nonneg _) hsmall hlinear
  · have hbigR : 50000*C<(N:ℝ) := lt_of_not_ge hsmall
    have hbig : 50000≤N := by
      have hh : (50000:ℝ)≤N := by linarith only [hbigR,hC]
      exact_mod_cast hh
    have hhalf : 25000≤N/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hbig
    obtain ⟨m,heq⟩ : ∃ m,N/2=m+5 :=
      ⟨N/2-5,(Nat.sub_add_cancel ((by decide : 5≤25000).trans hhalf)).symm⟩
    have hm : 20000≤m := by linarith only [heq,hhalf]
    have hpair : 2*(m+5)≤N := by
      rw [←heq]
      linarith only [Nat.mul_div_le N 2]
    obtain ⟨model,hmax,hnorm,hfall,hcount⟩ :=
      ExponentialPush.WidthTradeoff.exists_feeding_joint_model (n:=m+5) net hn hnet hpair
    have hround : N≤2*(m+5)+1 := by
      rw [←heq]
      exact NetworkLowerBound.half_arity_rounding N
    have hmR : (20000:ℝ)≤m := by exact_mod_cast hm
    have hroundR : (N:ℝ)≤2*((m:ℝ)+5)+1 := by exact_mod_cast hround
    have hmC : 20000*C≤(m:ℝ) := by linarith only [hroundR,hbigR,hC]
    have hscale : 1000*(N:ℝ)≤2001*(m:ℝ) := by linarith only [hmR,hroundR]
    have hsq : (N:ℝ)^2≤(41/10:ℝ)*(m:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤1000*(N:ℝ)) hscale
      linarith only [hh,sq_nonneg (m:ℝ)]
    have hCsq := mul_le_mul_of_nonneg_left hsq hC0.le
    have hMr : 8*(GrowingMatching.BadFirst.largeSupportCount (firstSupports (core model)):ℝ)≤(feedingCard net:ℝ) := by
      exact_mod_cast hcount
    have hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports (core model)):ℝ)≤C*(m:ℝ)^2 := by
      have hp : 0≤C*(m:ℝ)^2 := mul_nonneg hC0.le (sq_nonneg _)
      linarith only [hMr,hwidth,hCsq,hp]
    have hfallR : 16*(∑ j,((firstSupports (core model) j).card.descFactorial 4:ℝ))≤105*(feedingCard net:ℝ) := by
      exact_mod_cast hfall
    have hL : (∑ j,((firstSupports (core model) j).card.descFactorial 4:ℝ))≤27*C*(m:ℝ)^2 := by
      linarith only [hfallR,hwidth,hCsq]
    have hmodel := model_bound_scaled C hC hmC model hnorm hmax hM hL
    apply (div_le_iff (mul_pos (by norm_num : (0:ℝ)<175000) hC0)).mpr
    have hp : 0≤C*(h₂:ℝ) := mul_nonneg hC0.le (Nat.cast_nonneg _)
    linarith only [hmodel,hsq,hp]

/-- Arbitrary real weights, biases and affine skips, with no structural premise. -/
theorem affine_scaled (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂)
    (C : ℝ) (hC : 1≤C) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (affineFeedingCard net:ℝ)≤C*(N:ℝ)^2 → (N:ℝ)^2/(175000*C)≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hwidth
  have hcard : (feedingCard (normalizedModel net):ℝ)≤(affineFeedingCard net:ℝ) := by
    exact_mod_cast normalized_feedingCard_le_original net
  exact normalized_scaled hN (normalizedModel net)
    (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet) C hC (hcard.trans hwidth)

#print axioms model_bound_scaled
#print axioms normalized_scaled
#print axioms affine_scaled
end MaxCaterpillar.OvernightConstants.TradeoffTheta.Feeding
