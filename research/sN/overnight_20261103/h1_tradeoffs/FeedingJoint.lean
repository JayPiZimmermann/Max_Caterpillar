import research.sN.overnight_20261103.constants.FallingJoint
import MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer

/-! A sharp joint half budget charged only to original feeding rows. -/
set_option autoImplicit false
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction AffineSkipExtension FeedingCore
open Overnight.Constants.FallingHalf
variable {N n h₁ h₂ : ℕ}

/-- The same actual half model simultaneously controls falling-four cost and
non-braid count using only first rows feeding the second hidden layer. -/
theorem exists_feeding_joint_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j, (rowSupport ((core model).A j)).card.descFactorial 4)≤105*feedingCard net ∧
      8*nonBraidCount (core model)≤feedingCard net := by
  classical
  let T : Fin (feedingCard net) → Finset (Fin N) :=
    fun i => rowSupport (net.A (feedingEquiv net i).val)
  obtain ⟨S,hS,hbudget⟩ := exists_half_support_joint hpair T
  subst n
  obtain ⟨model,hmax,hnorm,hrows,hfeed⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost : (∑ j, jointCost (rowSupport ((core model).A j)).card) ≤
      ∑ j, if net.Feeding j then
        (if rowSupport (net.A j)⊆S then jointCost (rowSupport (net.A j)).card else 0)
        else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : model.Feeding j
    · have hf := hfeed j hj
      simp only [core,if_pos hj,if_pos hf]
      rw [hrows j,selectedEmbedding_image]
      by_cases hs : rowSupport (net.A j)⊆S
      · rw [if_pos hs,card_rowSupport_restrict (selectedEmbedding S) (net.A j)
          (by rwa [selectedEmbedding_image]),if_pos hs]
      · simp only [if_neg hs,rowSupport_zero,Finset.card_empty,jointCost_zero,le_refl]
    · simp only [core,if_neg hj,rowSupport_zero,Finset.card_empty,jointCost_zero,Nat.zero_le]
  have hb : 8*(∑ j, jointCost (rowSupport ((core model).A j)).card)≤105*feedingCard net := by
    have he := feeding_sum net (fun j =>
      if rowSupport (net.A j)⊆S then jointCost (rowSupport (net.A j)).card else 0)
    change 8*(∑ i : Fin (feedingCard net),
      if rowSupport (net.A (feedingEquiv net i).val)⊆S
      then jointCost (rowSupport (net.A (feedingEquiv net i).val)).card else 0)≤
        105*feedingCard net at hbudget
    rw [he] at hbudget
    exact (Nat.mul_le_mul_left 8 hcost).trans hbudget
  have hfall : 2*(∑ j, (rowSupport ((core model).A j)).card.descFactorial 4)≤
      ∑ j, jointCost (rowSupport ((core model).A j)).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => falling_le_jointCost _
  have hcount : 105*nonBraidCount (core model)≤
      ∑ j, jointCost (rowSupport ((core model).A j)).card := by
    have hh := Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => count_le_jointCost (rowSupport ((core model).A j)).card)
    simpa only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
      Nat.cast_id,nonBraidCount,mul_comm] using hh
  exact ⟨model,hmax,hnorm,by linarith only [hb,hfall],by linarith only [hb,hcount]⟩

#check @exists_feeding_joint_model
#print axioms exists_feeding_joint_model
end MaxCaterpillar.ExponentialPush.WidthTradeoff
