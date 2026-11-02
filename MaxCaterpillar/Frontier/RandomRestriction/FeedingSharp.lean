import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer
import MaxCaterpillar.Frontier.RandomRestriction.FeedingSharpScalar

/-! The full affine-skip, original-feeding tradeoff with constant 1/40000000.
The geometric and counting inputs are unchanged; only scalar losses are reduced. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp
open BigOperators NormalizedNetwork NetworkLowerBound FeedingCore AffineSkipExtension
variable {N h₁ h₂ : ℕ}

theorem normalized_feeding_tradeoff [NeZero N] (hN : 1040≤N)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) :
    (1/40000000:ℝ)*min ((N:ℝ)^2) ((N:ℝ)^4/(feedingCard net:ℝ))≤(h₂:ℝ) := by
  have hlr : (N:ℝ)≤2*(h₂:ℝ)+2 := by
    exact_mod_cast normalized_linear_bound net hnet
  have hNr : (1040:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  by_cases hwidth : 1000*(feedingCard net:ℝ)≤(N:ℝ)^3
  · letI : NeZero (N/2) := ⟨Nat.ne_of_gt
      (Nat.div_pos (le_trans (by decide : 2≤1040) hN) (by decide : 0<2))⟩
    obtain ⟨S,_hS,half,hmax,hnorm,_hmoment,hM,hreg⟩ :=
      exists_feeding_half_model (n:=N/2) ((by decide : 5≤1040).trans hN) net hn hnet
        (by linarith only [Nat.mul_div_le N 2])
    have hc : 4*(ActualHalfRestriction.nonBraidCount (core half):ℝ)≤(feedingCard net:ℝ) := by
      exact_mod_cast hM
    have hb := WeightedTradeoff.half_restriction_count_budget
      (N:ℝ) (N/2:ℕ) (feedingCard net:ℝ)
      (ActualHalfRestriction.nonBraidCount (core half):ℝ)
      (Nat.cast_nonneg _) (half_arity_ge_real hN) (half_arity_rounding_real N) hwidth hc
    rw [←descFactorial_three_real ((by decide : 2≤520).trans (half_arity_ge hN))] at hb
    have hbudget : 240*ActualHalfRestriction.nonBraidCount (core half)≤(N/2).descFactorial 3 := by
      exact_mod_cast hb
    have hcount := model_counting_feeding half hnorm hmax (half_arity_ge hN) hbudget
    apply forty_million_tradeoff (N:ℝ) (N/2:ℕ)
      (feedingCard net:ℝ) (regularizedMoment (core half):ℝ) (h₂:ℝ)
      hNr (half_arity_ge_real hN) (half_arity_rounding_real N)
    · exact_mod_cast one_le_regularizedMoment (core half)
    · exact_mod_cast hreg
    · exact hlr
    · exact hcount
  · exact linear_absorption (N:ℝ) (feedingCard net:ℝ) (h₂:ℝ)
      hNr (lt_of_not_ge hwidth) hlr

/-- Arbitrary real weights, all affine skips and biases, with the denominator
counting original first neurons feeding the second hidden layer. -/
theorem affine_feeding_tradeoff (hN : 1040≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
      (1/40000000:ℝ)*min ((N:ℝ)^2)
        ((N:ℝ)^4/(affineFeedingCard net:ℝ))≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  have hnorm := normalizedModel_translation_normalized net hnet
  have hmax := normalizedModel_computes_max net hnet
  have hbound := normalized_feeding_tradeoff hN (normalizedModel net) hnorm hmax
  have hp : (0:ℝ)<(feedingCard (normalizedModel net):ℝ) := by
    have hh := feedingCard_pos ((by decide : 5≤1040).trans hN) (normalizedModel net) hnorm hmax
    exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hh)
  have hc : (feedingCard (normalizedModel net):ℝ)≤(affineFeedingCard net:ℝ) := by
    exact_mod_cast normalized_feedingCard_le_original net
  have hratio : (N:ℝ)^4/(affineFeedingCard net:ℝ)≤
      (N:ℝ)^4/(feedingCard (normalizedModel net):ℝ) :=
    div_le_div_of_le_left (pow_nonneg (Nat.cast_nonneg N) 4) hp hc
  exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hratio) (by norm_num)).trans hbound

/-- Quadratic first feeding width forces quadratic second hidden width in
the full affine-skip model, with no cap on output-only first neurons. -/
theorem affine_feeding_quadratic (hN : 1040≤N) (net : AffineSkipNetwork N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,AffineSkipExtension.eval net x=Maximum N x) →
      (affineFeedingCard net:ℝ)≤(N:ℝ)^2 →
      (1/40000000:ℝ)*(N:ℝ)^2≤(h₂:ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet hwidth
  have hp : (0:ℝ)<(affineFeedingCard net:ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0<1)
      (affineFeedingCard_pos ((by decide : 5≤1040).trans hN) net hnet)
  have hratio : (N:ℝ)^2≤(N:ℝ)^4/(affineFeedingCard net:ℝ) := by
    apply (le_div_iff hp).mpr
    calc
      (N:ℝ)^2*(affineFeedingCard net:ℝ)≤(N:ℝ)^2*(N:ℝ)^2 :=
        mul_le_mul_of_nonneg_left hwidth (sq_nonneg _)
      _=(N:ℝ)^4 := by ring
  have hh := affine_feeding_tradeoff hN net hnet
  rwa [min_eq_left hratio] at hh

#print axioms normalized_feeding_tradeoff
#print axioms affine_feeding_tradeoff
#print axioms affine_feeding_quadratic
end MaxCaterpillar.Frontier.RandomRestriction.FeedingSharp
