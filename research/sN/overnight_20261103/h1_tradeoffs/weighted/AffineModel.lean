import research.sN.overnight_20261103.h1_tradeoffs.weighted.Model
import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization

/-! The weighted support budget is measured on the original nine arrays. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WeightedSupport
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction FeedingCore AffineSkipExtension
variable {N n h₁ h₂ : ℕ}

/-- Only zero-bias, zero-sum original rows feeding an original second neuron
can survive the faithful normalization. No other first rows are charged. -/
noncomputable def affineFeedingSupportBudget (cost : ℕ → ℝ)
    (net : AffineSkipNetwork N h₁ h₂) : ℝ := by
  classical
  exact ∑ j, if net.b j=0 ∧ (∑ i,net.A j i)=0 ∧ (∃ k,net.W k j≠0) then
    cost (rowSupport (net.A j)).card/(2 : ℝ)^(rowSupport (net.A j)).card else 0

theorem normalized_budget_le_original (cost : ℕ → ℝ) (hzero : cost 0=0)
    (hnonneg : ∀ r, 0 ≤ cost r) (net : AffineSkipNetwork N h₁ h₂) :
    feedingSupportBudget cost (normalizedModel net) ≤ affineFeedingSupportBudget cost net := by
  classical
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : (normalizedModel net).Feeding j
  · have hf := normalizedModel_feeding_original net j hj
    simp only [if_pos hj]
    rw [normalizedModel_first_row]
    by_cases hb : net.b j=0 ∧ (∑ i,net.A j i)=0
    · simp only [if_pos hb,hb.1,hb.2,hf,and_self,if_true,le_refl]
    · rw [if_neg hb]
      simp only [rowSupport_zero,Finset.card_empty,hzero,zero_div]
      split_ifs <;> first | exact div_nonneg (hnonneg _) (pow_nonneg (by norm_num : (0:ℝ)≤2) _) | exact le_rfl
  · simp only [if_neg hj]
    split_ifs <;> first | exact div_nonneg (hnonneg _) (pow_nonneg (by norm_num : (0:ℝ)≤2) _) | exact le_rfl

/-- Actual same-width half model with a support-sensitive budget on the
original affine network. Arbitrary biases and output skips are allowed. -/
theorem exists_affine_feeding_weighted_model [NeZero N] [NeZero n]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x=Maximum N x) (hpair : 2*n ≤ N)
    (cost : ℕ → ℝ) (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      (∑ j, cost (rowSupport ((core model).A j)).card) ≤ affineFeedingSupportBudget cost net := by
  obtain ⟨S,hS,model,hmax,hnorm,hbudget⟩ :=
    exists_feeding_weighted_model (normalizedModel net)
      (normalizedModel_translation_normalized net hnet)
      (normalizedModel_computes_max net hnet) hpair cost hzero hnonneg
  exact ⟨S,hS,model,hmax,hnorm,
    hbudget.trans (normalized_budget_le_original cost hzero hnonneg net)⟩

#check @exists_affine_feeding_weighted_model
#print axioms normalized_budget_le_original
#print axioms exists_affine_feeding_weighted_model
end MaxCaterpillar.ExponentialPush.WeightedSupport
