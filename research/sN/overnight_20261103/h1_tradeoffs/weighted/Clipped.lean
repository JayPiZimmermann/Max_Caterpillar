import research.sN.overnight_20261103.h1_tradeoffs.weighted.AffineModel

/-! Supports larger than the selected arity cannot survive at all.
They may be omitted from the weighted original-network budget. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WeightedSupport
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction FeedingCore AffineSkipExtension
variable {N n h₁ h₂ : ℕ}

def clipCost (n : ℕ) (cost : ℕ → ℝ) (r : ℕ) : ℝ := if r ≤ n then cost r else 0

lemma clipCost_zero (n : ℕ) (cost : ℕ → ℝ) (hzero : cost 0=0) :
    clipCost n cost 0=0 := by simp only [clipCost,Nat.zero_le,if_true,hzero]

lemma clipCost_nonneg (n : ℕ) (cost : ℕ → ℝ) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∀ r, 0 ≤ clipCost n cost r := by
  intro r
  unfold clipCost
  split_ifs
  · exact hnonneg r
  · exact le_rfl

lemma clipCost_row_eq (cost : ℕ → ℝ) (a : Point n) :
    clipCost n cost (rowSupport a).card=cost (rowSupport a).card := by
  have hc : (rowSupport a).card ≤ n :=
    (Finset.card_le_univ (rowSupport a)).trans_eq (Fintype.card_fin n)
  exact if_pos hc

/-- The original budget ignores every support larger than n. There may
be arbitrarily many such original feeding rows, with arbitrary real weights. -/
theorem exists_affine_feeding_clipped_model [NeZero N] [NeZero n]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x=Maximum N x) (hpair : 2*n ≤ N)
    (cost : ℕ → ℝ) (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      (∑ j, cost (rowSupport ((core model).A j)).card) ≤
        affineFeedingSupportBudget (clipCost n cost) net := by
  obtain ⟨S,hS,model,hmax,hnorm,hbudget⟩ :=
    exists_affine_feeding_weighted_model net hnet hpair (clipCost n cost)
      (clipCost_zero n cost hzero) (clipCost_nonneg n cost hnonneg)
  simp only [clipCost_row_eq] at hbudget
  exact ⟨S,hS,model,hmax,hnorm,hbudget⟩

#check @exists_affine_feeding_clipped_model
#print axioms exists_affine_feeding_clipped_model
end MaxCaterpillar.ExponentialPush.WeightedSupport
