import research.sN.overnight_20261103.constants.Coverage
import research.sN.overnight_20261103.constants.Envelope
import research.sN.overnight_20261103.constants.SharpCherries
import research.sN.overnight_20261103.constants.SharpTwoParameterized
import research.sN.overnight_20261103.constants.FallingHalfModel
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! Improved unconditional quadratic second-hidden-width constant.
The exact five-input obstruction is supplied by a proved theorem.
All weights, biases and affine skips are arbitrary real numbers. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants
open BigOperators Frontier Frontier.RandomRestriction
open GrowingMatching NormalizedNetwork AffineSkipExtension
variable {N m h₁ h₂ : ℕ}

local instance tailNeZero (m : ℕ) : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

theorem model_bound (hm : 100000≤m)
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ)≤5*(m:ℝ)^2)
    (hL : (∑ j,((firstSupports net j).card.descFactorial 4:ℝ))≤27*(m:ℝ)^2) :
    (m:ℝ)^2/151900≤(h₂:ℝ) := by
  let K := ⌊(m:ℝ)/12⌋₊
  have hmR : (100000:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hKu : (K:ℝ)≤(m:ℝ)/12 := Nat.floor_le (by positivity)
  have hK82 : 82≤K := Nat.le_floor (by norm_num; linarith only [hmR])
  have hKp : 0<K := lt_of_lt_of_le (by decide : 0<82) hK82
  have hK0 : (0:ℝ)<K := by exact_mod_cast hKp
  have hKl : (m:ℝ)≤(121/10:ℝ)*(K:ℝ) := by
    have hh := Nat.lt_floor_add_one ((m:ℝ)/12)
    change (m:ℝ)/12<(K:ℝ)+1 at hh
    linarith only [hh,hmR]
  have hKm : K<m := by
    have hh : (K:ℝ)<m := by linarith only [hKu,hm0]
    exact_mod_cast hh
  have hmpos : 0<m := lt_of_lt_of_le (by decide : 0<100000) hm
  have hQ : ((shortRankEvent 5 m K).card:ℝ)/
      Fintype.card (Configurations.Configuration 5 m)≤(41/10:ℝ)*(K:ℝ)/(m:ℝ) := by
    rw [shortRankEvent_fraction]
    exact badIsolated_fraction_le hmpos hKm.le hK82
  have ht := Overnight.Constants.conditional_finite_transfer_two_of_shortRank_bound
    localMatchingObstruction_five_two net hn hnet K
    ((by decide : 2≤100000).trans hm) (by linarith only [hm] : 4≤m+5) hKp hKm
    ((41/10:ℝ)*(K:ℝ)/(m:ℝ)) hQ
  have h5three : (5:ℕ).descFactorial 3=60 := by decide
  have h5two : (5:ℕ).descFactorial 2=20 := by decide
  have h5four : (5:ℕ).descFactorial 4=120 := by decide
  simp only [h5three,h5two,h5four,Nat.cast_ofNat] at ht
  have hshift : (5:ℝ)*((m:ℝ)+5-1)=5*((m:ℝ)+4) := by ring
  have hpair : (20:ℝ)*(K:ℝ)/2=10*(K:ℝ) := by ring
  rw [hshift,hpair] at ht
  have hcov := coverage m K hm hKu
    (GrowingMatching.BadFirst.largeSupportCount (firstSupports net):ℝ)
    (∑ j,((firstSupports net j).card.descFactorial 4:ℝ)) hM hL
  have henv := envelope_le m K ((by decide : 501≤100000).trans hm) hKp hKu
  have hc : (9/20:ℝ)≤(h₂:ℝ)*(465/(K:ℝ)^2) := by
    apply hcov.trans
    apply ht.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg h₂)
  have hksq : 9*(K:ℝ)^2≤9300*(h₂:ℝ) := by
    have hh : (9/20:ℝ)*(K:ℝ)^2≤(h₂:ℝ)*465 :=
      (le_div_iff (pow_pos hK0 2)).mp (by simpa only [mul_div_assoc] using hc)
    linarith only [hh]
  have hmsq : (m:ℝ)^2≤147*(K:ℝ)^2 := by
    have hh := mul_self_le_mul_self hm0.le hKl
    nlinarith only [hh,sq_nonneg (K:ℝ)]
  apply (div_le_iff (by norm_num : (0:ℝ)<151900)).mpr
  linarith only [hmsq,hksq]

/-- Every exact normalized MAX network with total first width at most N²
has second width at least N²/650000, for every N≥3. -/
theorem normalized_quadratic [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (hwidth : (h₁:ℝ)≤(N:ℝ)^2) :
    (1/650000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hlinear : (N:ℝ)≤2*(h₂:ℝ)+2 := by
    exact_mod_cast FeedingCore.normalized_linear_bound net hnet
  by_cases hsmall : N≤250000
  · have hsmallR : (N:ℝ)≤250000 := by exact_mod_cast hsmall
    have hp : 0≤((N:ℝ)-3)*(250000-(N:ℝ)) :=
      mul_nonneg (by linarith only [hNr]) (by linarith only [hsmallR])
    nlinarith only [hp,hlinear,Nat.cast_nonneg (α:=ℝ) h₂]
  · have hbig : 250000≤N := le_of_lt (lt_of_not_ge hsmall)
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
    have hscale : 1000*(N:ℝ)≤2001*(m:ℝ) := by linarith only [hmR,hroundR]
    have hsq : (N:ℝ)^2≤(41/10:ℝ)*(m:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤1000*(N:ℝ)) hscale
      nlinarith only [hh,sq_nonneg (m:ℝ)]
    have hMr : (GrowingMatching.BadFirst.largeSupportCount (firstSupports model):ℝ)≤(h₁:ℝ) := by
      have hh : GrowingMatching.BadFirst.largeSupportCount (firstSupports model)≤h₁ := by
        unfold GrowingMatching.BadFirst.largeSupportCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast hh
    have hM : (GrowingMatching.BadFirst.largeSupportCount (firstSupports model):ℝ)≤5*(m:ℝ)^2 := by
      nlinarith only [hMr,hwidth,hsq,sq_nonneg (m:ℝ)]
    have hfallR : 16*(∑ j,((firstSupports model j).card.descFactorial 4:ℝ))≤105*(h₁:ℝ) := by
      exact_mod_cast hfall
    have hL : (∑ j,((firstSupports model j).card.descFactorial 4:ℝ))≤27*(m:ℝ)^2 := by
      linarith only [hfallR,hwidth,hsq]
    have hmodel := model_bound hm model hnorm hmax hM hL
    linarith only [hmodel,hsq,sq_nonneg (m:ℝ)]

/-- Full raw affine-skip model; all nine parameter arrays/scalars are free.
No matching obstruction, support statistic, or event bound is assumed. -/
theorem affine_quadratic (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (h₁:ℝ)≤(N:ℝ)^2 → (1/650000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hwidth
  exact normalized_quadratic hN (normalizedModel net)
    (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet) hwidth

#print axioms model_bound
#print axioms normalized_quadratic
#print axioms affine_quadratic
end MaxCaterpillar.OvernightConstants
