import research.sN.overnight_20261103.h1_tradeoffs.weighted.Average
import MaxCaterpillar.Frontier.RandomRestriction.FeedingHalf

/-! Same-width actual MAX half models with weighted original-support budgets. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WeightedSupport
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction FeedingCore
variable {N n h₁ h₂ : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def supportBudget (cost : ℕ → ℝ) (net : NormalizedNetwork N h₁ h₂) : ℝ :=
  ∑ j, cost (rowSupport (net.A j)).card/(2 : ℝ)^(rowSupport (net.A j)).card

noncomputable def feedingSupportBudget (cost : ℕ → ℝ)
    (net : NormalizedNetwork N h₁ h₂) : ℝ := by
  classical
  exact ∑ j, if net.Feeding j then
    cost (rowSupport (net.A j)).card/(2 : ℝ)^(rowSupport (net.A j)).card else 0

/-- Every original support keeps its own exponentially discounted cost.
No width or support-size cap is assumed. -/
theorem exists_weighted_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n ≤ N)
    (cost : ℕ → ℝ) (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      (∑ j, cost (rowSupport (model.A j)).card) ≤ supportBudget cost net := by
  classical
  obtain ⟨S,hS,hbudget⟩ := exists_half_weighted_restriction hpair
    (fun j => rowSupport (net.A j)) cost hzero hnonneg
  subst n
  obtain ⟨model,hmax,hnorm,hrows,_⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost :
      (∑ j, cost (rowSupport (model.A j)).card)=
        ∑ j, if rowSupport (net.A j) ⊆ S then cost (rowSupport (net.A j)).card else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrows j,selectedEmbedding_image]
    by_cases hs : rowSupport (net.A j) ⊆ S
    · rw [if_pos hs,card_rowSupport_restrict (selectedEmbedding S) (net.A j)
        (by rwa [selectedEmbedding_image]),if_pos hs]
    · simp only [if_neg hs,rowSupport_zero,Finset.card_empty,hzero]
  exact ⟨S,rfl,model,hmax,hnorm,by rwa [hcost]⟩

lemma feeding_sum_real (net : NormalizedNetwork N h₁ h₂) (f : Fin h₁ → ℝ) :
    (∑ i : Fin (feedingCard net), f (feedingEquiv net i).val)=
      ∑ j, if net.Feeding j then f j else 0 := by
  classical
  calc
    _ = ∑ j : {j : Fin h₁ // net.Feeding j}, f j.val :=
      Fintype.sum_equiv (feedingEquiv net) _ _ (fun _ => rfl)
    _ = ∑ j in Finset.univ.filter net.Feeding, f j :=
      (Finset.sum_subtype _ (fun j => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) f).symm
    _ = _ := Finset.sum_filter _ _

/-- Output-only first neurons have zero cost. The support discount and
feeding predicate both refer to the original normalized model. -/
theorem exists_feeding_weighted_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n ≤ N)
    (cost : ℕ → ℝ) (hzero : cost 0=0) (hnonneg : ∀ r, 0 ≤ cost r) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      (∑ j, cost (rowSupport ((core model).A j)).card) ≤ feedingSupportBudget cost net := by
  classical
  let T : Fin (feedingCard net) → Finset (Fin N) :=
    fun i => rowSupport (net.A (feedingEquiv net i).val)
  obtain ⟨S,hS,hbudget⟩ := exists_half_weighted_restriction hpair T cost hzero hnonneg
  subst n
  obtain ⟨model,hmax,hnorm,hrows,hfeed⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost :
      (∑ j, cost (rowSupport ((core model).A j)).card) ≤
        ∑ j, if net.Feeding j then
          (if rowSupport (net.A j) ⊆ S then cost (rowSupport (net.A j)).card else 0) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : model.Feeding j
    · have hf := hfeed j hj
      simp only [core,if_pos hj,if_pos hf]
      rw [hrows j,selectedEmbedding_image]
      by_cases hs : rowSupport (net.A j) ⊆ S
      · rw [if_pos hs,card_rowSupport_restrict (selectedEmbedding S) (net.A j)
          (by rwa [selectedEmbedding_image]),if_pos hs]
      · simp only [if_neg hs,rowSupport_zero,Finset.card_empty,hzero,le_refl]
    · simp only [core,if_neg hj,rowSupport_zero,Finset.card_empty,hzero]
      split_ifs <;> first | exact hnonneg _ | exact le_rfl
  have hleft := feeding_sum_real net (fun j =>
    if rowSupport (net.A j) ⊆ S then cost (rowSupport (net.A j)).card else 0)
  have hright := feeding_sum_real net (fun j =>
    cost (rowSupport (net.A j)).card/(2 : ℝ)^(rowSupport (net.A j)).card)
  change (∑ i : Fin (feedingCard net),
      if rowSupport (net.A (feedingEquiv net i).val) ⊆ S
      then cost (rowSupport (net.A (feedingEquiv net i).val)).card else 0) ≤
    ∑ i : Fin (feedingCard net), cost (rowSupport (net.A (feedingEquiv net i).val)).card/
      (2 : ℝ)^(rowSupport (net.A (feedingEquiv net i).val)).card at hbudget
  rw [hleft,hright] at hbudget
  exact ⟨S,rfl,model,hmax,hnorm,hcost.trans hbudget⟩

#check @exists_feeding_weighted_model
#print axioms exists_weighted_model
#print axioms exists_feeding_weighted_model
end MaxCaterpillar.ExponentialPush.WeightedSupport
