import MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff.Coverage
import MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff.Envelope
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! A larger admissible rank cutoff improves the unconditional quadratic
constant for quadratic total first width. The local obstruction H(5,2) is
proved, rather than assumed. All affine skips and biases are permitted. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
open BigOperators GrowingMatching NormalizedNetwork AffineSkipExtension
variable {N m h₁ h₂ : ℕ}

local instance tailNeZero (m : ℕ) : NeZero (m+5) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) (Nat.le_add_left 5 m))⟩

theorem model_bound (hm : 20000≤m)
    (net : NormalizedNetwork (m+5) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (hM : (BadFirst.largeSupportCount (firstSupports net):ℝ)≤2*(m:ℝ)^2)
    (hL : (∑ j,((firstSupports net j).card.descFactorial 4:ℝ))≤100*(m:ℝ)^2) :
    (m:ℝ)^2/2163200≤(h₂:ℝ) := by
  let K := ⌊(m:ℝ)/25⌋₊
  have hmR : (20000:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith only [hmR]
  have hKu : (K:ℝ)≤(m:ℝ)/25 := Nat.floor_le (by positivity)
  have hK4 : 4≤K := Nat.le_floor (by norm_num; linarith only [hmR])
  have hKp : 0<K := lt_of_lt_of_le (by decide : 0<4) hK4
  have hK0 : (0:ℝ)<K := by exact_mod_cast hKp
  have hKl : (m:ℝ)≤26*(K:ℝ) := by
    have hh := Nat.lt_floor_add_one ((m:ℝ)/25)
    change (m:ℝ)/25<(K:ℝ)+1 at hh
    linarith only [hh,hmR]
  have hKm : K<m := by
    have hh : (K:ℝ)<m := by linarith only [hKu,hm0]
    exact_mod_cast hh
  have ht := conditional_finite_transfer localMatchingObstruction_five_two
    (by decide : 0<2) net hn hnet K ((by decide : 2≤20000).trans hm)
    (by linarith only [hm] : 4≤m+5) hK4 hKm
  have h5three : (5:ℕ).descFactorial 3=60 := by decide
  have h5two : (5:ℕ).descFactorial 2=20 := by decide
  have h5four : (5:ℕ).descFactorial 4=120 := by decide
  simp only [show 2*2=4 from rfl,h5three,h5two,h5four,Nat.cast_ofNat] at ht
  have hshift : (5:ℝ)*((m:ℝ)+5-1)=5*((m:ℝ)+4) := by ring
  have hpair : (20:ℝ)*(K:ℝ)/2=10*(K:ℝ) := by ring
  rw [hshift,hpair] at ht
  have hcov := coverage m K hm hKu
    (BadFirst.largeSupportCount (firstSupports net):ℝ)
    (∑ j,((firstSupports net j).card.descFactorial 4:ℝ)) hM hL
  have henv := envelope_le m K ((by decide : 8≤20000).trans hm) hKp hKu
  have hc : (1/2:ℝ)≤(h₂:ℝ)*(1600/(K:ℝ)^2) := by
    apply hcov.trans
    apply ht.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg h₂)
  have hksq : (K:ℝ)^2≤3200*(h₂:ℝ) := by
    have hh : (1/2:ℝ)*(K:ℝ)^2≤(h₂:ℝ)*1600 :=
      (le_div_iff (pow_pos hK0 2)).mp (by simpa only [mul_div_assoc] using hc)
    linarith only [hh]
  have hmsq : (m:ℝ)^2≤676*(K:ℝ)^2 := by
    have hh := mul_self_le_mul_self hm0.le hKl
    nlinarith only [hh]
  apply (div_le_iff (by norm_num : (0:ℝ)<2163200)).mpr
  linarith only [hmsq,hksq]

/-- An unconditional quadratic bound for exact normalized networks with
quadratic total first width. Every support statistic is derived internally. -/
theorem normalized_quadratic [NeZero N] (hN : 3≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (hwidth : (h₁:ℝ)≤(N:ℝ)^2) :
    (1/10000000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  have hNr : (3:ℝ)≤N := by exact_mod_cast hN
  have hlinear : (N:ℝ)≤2*(h₂:ℝ)+2 := by
    exact_mod_cast FeedingCore.normalized_linear_bound net hnet
  by_cases hsmall : N≤50000
  · have hsmallR : (N:ℝ)≤50000 := by exact_mod_cast hsmall
    have hh := mul_le_mul_of_nonneg_left hsmallR (Nat.cast_nonneg (α:=ℝ) N)
    nlinarith only [hh,hlinear,hNr]
  · have hbig : 50000≤N := le_of_lt (lt_of_not_ge hsmall)
    have hhalf : 25000≤N/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr hbig
    obtain ⟨m,heq⟩ : ∃ m,N/2=m+5 :=
      ⟨N/2-5,(Nat.sub_add_cancel ((by decide : 5≤25000).trans hhalf)).symm⟩
    have hm : 20000≤m := by linarith only [heq,hhalf]
    have hpair : 2*(m+5)≤N := by
      rw [←heq]
      linarith only [Nat.mul_div_le N 2]
    obtain ⟨_S,_hS,model,hmax,hnorm,hfour,hcount⟩ :=
      NormalizedTotalHalf.exists_model (n:=m+5) net hn hnet hpair
    have hround : N≤2*(m+5)+1 := by
      rw [←heq]
      exact NetworkLowerBound.half_arity_rounding N
    have hmR : (20000:ℝ)≤m := by exact_mod_cast hm
    have hroundR : (N:ℝ)≤2*((m:ℝ)+5)+1 := by exact_mod_cast hround
    have hscale : 9*(N:ℝ)≤20*(m:ℝ) := by linarith only [hmR,hroundR]
    have hsq : 81*(N:ℝ)^2≤400*(m:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤9*(N:ℝ)) hscale
      nlinarith only [hh]
    have hMr : 4*(ActualHalfRestriction.nonBraidCount model:ℝ)≤(h₁:ℝ) := by
      exact_mod_cast hcount
    have hM : (BadFirst.largeSupportCount (firstSupports model):ℝ)≤2*(m:ℝ)^2 := by
      change (ActualHalfRestriction.nonBraidCount model:ℝ)≤2*(m:ℝ)^2
      nlinarith only [hMr,hwidth,hsq,sq_nonneg (m:ℝ)]
    have hFr : 4*(ActualHalfRestriction.fourthMoment model:ℝ)≤81*(h₁:ℝ) := by
      exact_mod_cast hfour
    have hF : (ActualHalfRestriction.fourthMoment model:ℝ)≤100*(m:ℝ)^2 := by
      linarith only [hFr,hwidth,hsq]
    have hfall : (∑ j,(firstSupports model j).card.descFactorial 4)≤
        ActualHalfRestriction.fourthMoment model :=
      Finset.sum_le_sum (fun j _ => NetworkLowerBound.falling_four_le_support_cost _)
    have hfallR : (∑ j,((firstSupports model j).card.descFactorial 4:ℝ))≤
        (ActualHalfRestriction.fourthMoment model:ℝ) := by exact_mod_cast hfall
    have hL := hfallR.trans hF
    have hmodel := model_bound hm model hnorm hmax hM hL
    have hscale' : 10*(N:ℝ)≤21*(m:ℝ) := by linarith only [hmR,hroundR]
    have hsq' : (N:ℝ)^2≤(9/2:ℝ)*(m:ℝ)^2 := by
      have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤10*(N:ℝ)) hscale'
      nlinarith only [hh,sq_nonneg (m:ℝ)]
    linarith only [hmodel,hsq',sq_nonneg (m:ℝ)]

/-- Full affine-skip scope, arbitrary real weights and biases. The total
first hidden width is at most N²; no structural or probability premise remains. -/
theorem affine_quadratic (hN : 3≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
    (h₁:ℝ)≤(N:ℝ)^2 → (1/10000000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<3) hN)⟩
  intro hnet hwidth
  exact normalized_quadratic hN (normalizedModel net)
    (normalizedModel_translation_normalized net hnet)
    (normalizedModel_computes_max net hnet) hwidth

#print axioms model_bound
#print axioms normalized_quadratic
#print axioms affine_quadratic
end MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff
