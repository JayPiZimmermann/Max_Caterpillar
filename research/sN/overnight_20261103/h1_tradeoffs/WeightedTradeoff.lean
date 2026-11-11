import research.sN.overnight_20261103.h1_tradeoffs.weighted.Clipped
import research.sN.overnight_20261103.h1_tradeoffs.WidthParameter
import research.sN.overnight_20261103.h1_tradeoffs.feeding.FeedingLower

/-! Original support-sensitive bounds: no first-width count is assumed. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction AffineSkipExtension FeedingCore
open GrowingMatching GrowingMatching.Bernoulli
open WeightedSupport
variable {N n h₁ h₂ : ℕ}

def supportCostNat (r : ℕ) : ℕ := if 3≤r then max 1 (r.descFactorial 4) else 0

def supportCost (r : ℕ) : ℝ := supportCostNat r

lemma supportCost_zero : supportCost 0=0 := by norm_num [supportCost,supportCostNat]

lemma supportCost_nonneg (r : ℕ) : 0≤supportCost r := Nat.cast_nonneg _

lemma falling_le_supportCostNat (r : ℕ) : r.descFactorial 4≤supportCostNat r := by
  by_cases hr : 3≤r
  · rw [supportCostNat,if_pos hr]
    exact le_max_right _ _
  · rw [supportCostNat,if_neg hr,Nat.descFactorial_eq_zero_iff_lt.mpr
      (lt_trans (lt_of_not_ge hr) (by decide : 3<4))]

lemma count_le_supportCostNat (r : ℕ) : (if 3≤r then 1 else 0)≤supportCostNat r := by
  unfold supportCostNat
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- Charge each original zero-bias, zero-sum feeding row by its actual
support size. Braid rows and rows with support larger than n cost zero. -/
noncomputable def originalSupportBudget (n : ℕ)
    (net : AffineSkipNetwork N h₁ h₂) : ℝ :=
  affineFeedingSupportBudget (clipCost n supportCost) net

theorem budgets_of_support_cost (model : NormalizedNetwork n h₁ h₂) (B : ℝ)
    (hcost : (∑ j,supportCost (rowSupport ((core model).A j)).card)≤B) :
    (nonBraidCount (core model) : ℝ)≤B ∧
      (∑ j,((rowSupport ((core model).A j)).card.descFactorial 4 : ℝ))≤B := by
  classical
  have hfall : (∑ j,(rowSupport ((core model).A j)).card.descFactorial 4)≤
      ∑ j,supportCostNat (rowSupport ((core model).A j)).card := by
    exact Finset.sum_le_sum fun j _ => falling_le_supportCostNat _
  have hcount : nonBraidCount (core model)≤
      ∑ j,supportCostNat (rowSupport ((core model).A j)).card := by
    have hh := Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => count_le_supportCostNat (rowSupport ((core model).A j)).card)
    simpa only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
      Nat.cast_id,nonBraidCount,mul_one] using hh
  have hfallR : (∑ j,((rowSupport ((core model).A j)).card.descFactorial 4 : ℝ))≤
      ∑ j,supportCost (rowSupport ((core model).A j)).card := by
    unfold supportCost
    exact_mod_cast hfall
  have hcountR : (nonBraidCount (core model) : ℝ)≤
      ∑ j,supportCost (rowSupport ((core model).A j)).card := by
    unfold supportCost
    exact_mod_cast hcount
  exact ⟨hcountR.trans hcost,hfallR.trans hcost⟩

/-- A conditional exponential lower bound with no hypothesis on h₁ or even
the number of feeding rows. Only the displayed original support budget is
charged, and arbitrary large-support feeding dictionaries are permitted. -/
theorem conditional_affine_support_tradeoff (d : ℕ) (hd : 1≤d)
    (hsize : 10000000000*d^2≤N/2)
    (H : LocalMatchingObstruction
      (Parameters.minimumArity (N/2) d) (Parameters.matchingOrder (N/2) d))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hbudget : originalSupportBudget (N/2) net≤(d : ℝ)^2*((N/2 : ℕ) : ℝ)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ)))≤
      (h₂ : ℝ) := by
  letI := originalNeZero N d hd hsize
  letI := halfNeZero N d hd hsize
  obtain ⟨S,_hS,model,hmax,hnorm,hcost⟩ := exists_affine_feeding_clipped_model
    (n:=N/2) net hnet (by linarith only [Nat.mul_div_le N 2])
    supportCost supportCost_zero supportCost_nonneg
  obtain ⟨hM,hL⟩ := budgets_of_support_cost model ((d : ℝ)^2*((N/2 : ℕ) : ℝ)^2)
    (hcost.trans hbudget)
  exact FeedingBernoulli.conditional_sqrt_lower_bound hd hsize H model hnorm hmax hM hL

#check @conditional_affine_support_tradeoff
#print axioms budgets_of_support_cost
#print axioms conditional_affine_support_tradeoff
end MaxCaterpillar.ExponentialPush.WidthTradeoff
