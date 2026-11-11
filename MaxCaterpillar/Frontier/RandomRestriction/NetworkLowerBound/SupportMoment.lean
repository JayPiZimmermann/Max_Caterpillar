import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound.BadEvents
import MaxCaterpillar.Frontier.RandomRestriction.Configurations

/-! # Actual model support budgets imply the three bad-event bounds -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
open BigOperators Configurations NormalizedNetwork
variable {n m h₁ h₂ : ℕ}

noncomputable def regularizedMoment (net : NormalizedNetwork n h₁ h₂) : ℕ :=
  max (ActualHalfRestriction.fourthMoment net) 1
noncomputable def supports (net : NormalizedNetwork n h₁ h₂) : Fin h₁ → Finset (Fin n) :=
  fun j => rowSupport (net.A j)

lemma one_le_regularizedMoment (net : NormalizedNetwork n h₁ h₂) :
    1≤regularizedMoment net := le_max_right _ _

lemma falling_four_le_support_cost (r : ℕ) :
    r.descFactorial 4 ≤ if 3≤r then r^4 else 0 := by
  by_cases hr : 3≤r
  · rw [if_pos hr]
    exact Nat.descFactorial_le_pow r 4
  · rw [if_neg hr,Nat.descFactorial_eq_zero_iff_lt.mpr
      (lt_trans (lt_of_not_ge hr) (by decide : 3<4))]

lemma fallingMoment_le (net : NormalizedNetwork n h₁ h₂) :
    (∑ j,(supports net j).card.descFactorial 4) ≤ regularizedMoment net := by
  apply le_trans _ (le_max_left _ _)
  exact Finset.sum_le_sum (fun j _ => falling_four_le_support_cost _)

lemma fallingMoment_real_le (net : NormalizedNetwork n h₁ h₂) :
    (∑ j,((supports net j).card.descFactorial 4 : ℝ)) ≤ (regularizedMoment net : ℝ) := by
  exact_mod_cast fallingMoment_le net

lemma model_badFirst_quarter (net : NormalizedNetwork (m+5) h₁ h₂)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount net ≤ (m+5).descFactorial 3) :
    4*((badFirstConfigurations (supports net)).card : ℝ) ≤
      (Fintype.card (Configuration m) : ℝ) := by
  apply badFirstConfigurations_card_le
  simpa only [supports,BadFirst.largeSupportCount_rowSupport] using hbudget

/-- The full-index fourth moment controls the literal feeding event; no
largest support or feeding-row cardinality hypothesis is required. -/
lemma model_feedingBad_quarter (net : NormalizedNetwork (m+5) h₁ h₂) (K : ℕ)
    (hm : 400≤m) (hK : 4≤K) (hsmall : (K : ℝ)≤(m : ℝ)/100)
    (hbudget : 16*(regularizedMoment net : ℝ)*(K : ℝ)^2≤(m : ℝ)^4) :
    4*((feedingBadConfigurationsThree (supports net) K).card : ℝ) ≤
      (Fintype.card (Configuration m) : ℝ) := by
  apply feedingBadConfigurationsThree_card_le_quarter _ K hm hK hsmall
  calc
    16*(∑ j,((supports net j).card.descFactorial 4 : ℝ))*(K : ℝ)^2 ≤
        16*(regularizedMoment net : ℝ)*(K : ℝ)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fallingMoment_real_le net) (by norm_num)) (sq_nonneg _)
    _ ≤ _ := hbudget

#print axioms fallingMoment_le
#print axioms model_badFirst_quarter
#print axioms model_feedingBad_quarter
end MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound
