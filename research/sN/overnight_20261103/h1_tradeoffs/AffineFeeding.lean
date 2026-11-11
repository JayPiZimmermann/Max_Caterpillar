import research.sN.overnight_20261103.h1_tradeoffs.WidthParameter
import research.sN.overnight_20261103.h1_tradeoffs.feeding.FeedingLower
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! Raw affine-skip Bernoulli bounds charged only to original feeding rows.
There is no bound on the total first hidden width. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction AffineSkipExtension FeedingCore
open GrowingMatching GrowingMatching.AffineGeneralRows GrowingMatching.Bernoulli
variable {N h₁ h₂ : ℕ}

/-- Arbitrarily many original first neurons may feed only the output.
The counted feeding width is defined by nonzero columns of the ORIGINAL W. -/
theorem conditional_affine_feeding_tradeoff (d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) d) (Parameters.matchingOrder (N/2) d))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hwidth : 81*affineFeedingCard net ≤ 4*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  letI := originalNeZero N d hd hsize
  letI := halfNeZero N d hd hsize
  have hN : 5 ≤ N := by
    have hd2 : 1 ≤ d^2 := by nlinarith only [hd]
    have hn := Nat.div_le_self N 2
    nlinarith only [hsize,hd2,hn]
  obtain ⟨S,_hS,model,hmax,hnorm,hmoment,_hcount,_hreg⟩ :=
    exists_feeding_half_model (n := N/2) hN (normalizedModel net)
      (normalizedModel_translation_normalized net hnet)
      (normalizedModel_computes_max net hnet)
      (by linarith only [Nat.mul_div_le N 2])
  have hraw : 4*fourthMoment (core model) ≤ 81*affineFeedingCard net :=
    hmoment.trans (Nat.mul_le_mul_left 81 (normalized_feedingCard_le_original net))
  have hm : fourthMoment (core model) ≤ d^2*(N/2)^2 := by
    have h := hraw.trans hwidth
    nlinarith only [h]
  have hcount := (nonBraidCount_le_fourthMoment (core model)).trans hm
  have hsum : (∑ j, (rowSupport ((core model).A j)).card.descFactorial 4) ≤
      d^2*(N/2)^2 :=
    (Finset.sum_le_sum (fun j _ => falling_four_le_large_support_cost _)).trans hm
  apply FeedingBernoulli.conditional_sqrt_lower_bound hd hsize H model hnorm hmax
  · change (nonBraidCount (core model) : ℝ) ≤ _
    exact_mod_cast hcount
  · change (∑ j, ((rowSupport ((core model).A j)).card.descFactorial 4 : ℝ)) ≤ _
    exact_mod_cast hsum

/-- The actual original feeding width determines the parameter. Total first
width and the number of output-only first neurons are unrestricted. -/
theorem conditional_affine_feeding_tradeoff_explicit
    (net : AffineSkipNetwork N h₁ h₂)
    (hsize : 10000000000*(widthParameter (N/2) (affineFeedingCard net))^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) (widthParameter (N/2) (affineFeedingCard net)))
      (Parameters.matchingOrder (N/2) (widthParameter (N/2) (affineFeedingCard net))))
    (hnet : letI := originalNeZero N (widthParameter (N/2) (affineFeedingCard net)) (widthParameter_pos _ _) hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (8000*(widthParameter (N/2) (affineFeedingCard net) : ℝ))) ≤ (h₂ : ℝ) :=
  conditional_affine_feeding_tradeoff _ (widthParameter_pos _ _) hsize H net hnet
    (widthParameter_budget _ _ (half_pos _ (widthParameter_pos _ _) hsize))

#check @conditional_affine_feeding_tradeoff_explicit
#print axioms conditional_affine_feeding_tradeoff
#print axioms conditional_affine_feeding_tradeoff_explicit
end MaxCaterpillar.ExponentialPush.WidthTradeoff
