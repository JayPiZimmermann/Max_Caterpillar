import research.sN.overnight_20261103.constants.tradeoff.Coverage
import research.sN.overnight_20261103.constants.tradeoff.Parameters
import research.sN.overnight_20261103.constants.tradeoff.ScalarMin
import research.sN.overnight_20261103.constants.Envelope
import research.sN.overnight_20261103.constants.SharpCherries
import research.sN.overnight_20261103.constants.SharpTwoParameterized
import research.sN.overnight_20261103.constants.FallingHalfModel
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! Unconditional quadratic tradeoff for arbitrary real first-width scales.
The restriction, cutoff and five-input obstruction are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace MaxCaterpillar.OvernightConstants.Tradeoff
open BigOperators Frontier Frontier.RandomRestriction
open GrowingMatching NormalizedNetwork AffineSkipExtension
variable {N m h₁ h₂ : ℕ}

local instance scaledTailNeZero (m : ℕ) : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

theorem model_bound_scaled (C : ℝ) (hC : 1≤C) (hm : 100000*C≤(m:ℝ))
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ)≤5*C*(m:ℝ)^2)
    (hL : (∑ j,((firstSupports net j).card.descFactorial 4:ℝ))≤27*C*(m:ℝ)^2) :
    (m:ℝ)^2≤151900*C*(h₂:ℝ) := by
  have hC0 : 0≤C := by linarith only [hC]
  have hmR : (100000:ℝ)≤m := by linarith only [hm,hC]
  have hmNat : 100000≤m := by exact_mod_cast hmR
  let K := cutoff m C
  obtain ⟨hK82,hKm,hKu,hKsq,hmsq⟩ := cutoff_bounds m C hC hm
  change 82≤K at hK82
  change K<m at hKm
  change (K:ℝ)≤(m:ℝ)/12 at hKu
  change 144*C*(K:ℝ)^2≤(m:ℝ)^2 at hKsq
  change (m:ℝ)^2≤147*C*(K:ℝ)^2 at hmsq
  have hKp : 0<K := lt_of_lt_of_le (by decide : 0<82) hK82
  have hK0 : (0:ℝ)<K := by exact_mod_cast hKp
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<100000) hmNat
  have hQ : ((shortRankEvent 5 m K).card:ℝ)/
      Fintype.card (Configurations.Configuration 5 m)≤(41/10:ℝ)*(K:ℝ)/(m:ℝ) := by
    rw [shortRankEvent_fraction]
    exact OvernightConstants.badIsolated_fraction_le hmpos hKm.le hK82
  have ht := Overnight.Constants.conditional_finite_transfer_two_of_shortRank_bound
    localMatchingObstruction_five_two net hn hnet K
    ((by decide : 2≤100000).trans hmNat) (by linarith only [hmNat] : 4≤m+5) hKp hKm
    ((41/10:ℝ)*(K:ℝ)/(m:ℝ)) hQ
  have h5three : (5:ℕ).descFactorial 3=60 := by decide
  have h5two : (5:ℕ).descFactorial 2=20 := by decide
  have h5four : (5:ℕ).descFactorial 4=120 := by decide
  simp only [h5three,h5two,h5four,Nat.cast_ofNat] at ht
  have hshift : (5:ℝ)*((m:ℝ)+5-1)=5*((m:ℝ)+4) := by ring
  have hpair : (20:ℝ)*(K:ℝ)/2=10*(K:ℝ) := by ring
  rw [hshift,hpair] at ht
  have hcov := coverage m K C hC hm hKu hKsq
    (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ)
    (∑ j,((firstSupports net j).card.descFactorial 4:ℝ)) hM hL
  have henv := OvernightConstants.envelope_le m K
    ((by decide : 501≤100000).trans hmNat) hKp hKu
  have hc : (9/20:ℝ)≤(h₂:ℝ)*(465/(K:ℝ)^2) := by
    apply hcov.trans
    apply ht.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg h₂)
  have hksq : 9*(K:ℝ)^2≤9300*(h₂:ℝ) := by
    have hh : (9/20:ℝ)*(K:ℝ)^2≤(h₂:ℝ)*465 :=
      (le_div_iff (pow_pos hK0 2)).mp (by simpa only [mul_div_assoc] using hc)
    linarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hksq hC0
  linarith only [hmsq,hh]

/-- All normalized exact MAX models, with any real scale C≥1. -/
theorem normalized_scaled [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (C : ℝ) (hC : 1≤C) (hwidth : (h₁:ℝ)≤C*(N:ℝ)^2) :
    (N:ℝ)^2/(650000*C)≤(h₂:ℝ) := by
  have hC0 : 0<C := by linarith only [hC]
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hlinear : (N:ℝ)≤2*(h₂:ℝ)+2 := by
    exact_mod_cast FeedingCore.normalized_linear_bound net hnet
  by_cases hsmall : (N:ℝ)≤250000*C
  · exact scaled_linear_absorption (N:ℝ) C (h₂:ℝ) hNr hC
      (Nat.cast_nonneg _) hsmall hlinear
  · have hbigR : 250000*C<(N:ℝ) := lt_of_not_ge hsmall
    have hbig : 250000≤N := by
      have hh : (250000:ℝ)≤N := by linarith only [hbigR,hC]
      exact_mod_cast hh
    have hhalf : 125000≤N/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hbig
    obtain ⟨m,heq⟩ : ∃ m,N/2=m+5 :=
      ⟨N/2-5,(Nat.sub_add_cancel ((by decide : 5≤125000).trans hhalf)).symm⟩
    have hm : 100000≤m := by linarith only [heq,hhalf]
    have hpair : 2*(m+5)≤N := by
      rw [←heq]
      linarith only [Nat.mul_div_le N 2]
    obtain ⟨_S,_hS,model,hmax,hnorm,hfall⟩ :=
      Overnight.Constants.FallingHalf.exists_model (n:=m+5) net hn hnet hpair
    have hround : N≤2*(m+5)+1 := by
      rw [←heq]
      exact NetworkLowerBound.half_arity_rounding N
    have hmR : (100000:ℝ)≤m := by exact_mod_cast hm
    have hroundR : (N:ℝ)≤2*((m:ℝ)+5)+1 := by exact_mod_cast hround
    have hmC : 100000*C≤(m:ℝ) := by linarith only [hroundR,hbigR,hC]
    have hscale : 1000*(N:ℝ)≤2001*(m:ℝ) := by linarith only [hmR,hroundR]
    have hsq : (N:ℝ)^2≤(41/10:ℝ)*(m:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤1000*(N:ℝ)) hscale
      linarith only [hh,sq_nonneg (m:ℝ)]
    have hCsq := mul_le_mul_of_nonneg_left hsq hC0.le
    have hMr : (GrowingMatching.BadFirst.largeSupportCount (firstSupports model):ℝ)≤(h₁:ℝ) := by
      have hh : GrowingMatching.BadFirst.largeSupportCount (firstSupports model)≤h₁ := by
        unfold GrowingMatching.BadFirst.largeSupportCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast hh
    have hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports model):ℝ)≤5*C*(m:ℝ)^2 := by
      have hp : 0≤C*(m:ℝ)^2 := mul_nonneg hC0.le (sq_nonneg _)
      linarith only [hMr,hwidth,hCsq,hp]
    have hfallR : 16*(∑ j,((firstSupports model j).card.descFactorial 4:ℝ))≤105*(h₁:ℝ) := by
      exact_mod_cast hfall
    have hL : (∑ j,((firstSupports model j).card.descFactorial 4:ℝ))≤27*C*(m:ℝ)^2 := by
      linarith only [hfallR,hwidth,hCsq]
    have hmodel := model_bound_scaled C hC hmC model hnorm hmax hM hL
    apply (div_le_iff (mul_pos (by norm_num : (0:ℝ)<650000) hC0)).mpr
    have hp : 0≤C*(h₂:ℝ) := mul_nonneg hC0.le (Nat.cast_nonneg _)
    linarith only [hmodel,hsq,hp]

/-- Arbitrary real weights, biases and affine skips, with no structural premise. -/
theorem affine_scaled (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂)
    (C : ℝ) (hC : 1≤C) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (h₁:ℝ)≤C*(N:ℝ)^2 → (N:ℝ)^2/(650000*C)≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hwidth
  exact normalized_scaled hN (normalizedModel net)
    (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet) C hC hwidth

#print axioms model_bound_scaled
#print axioms normalized_scaled
#print axioms affine_scaled
end MaxCaterpillar.OvernightConstants.Tradeoff
