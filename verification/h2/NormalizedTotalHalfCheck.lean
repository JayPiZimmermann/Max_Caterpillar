import MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf
import MaxCaterpillar.Theorems

/-! Independent expanded support-statistic contracts and a concrete witness. -/
set_option autoImplicit false
noncomputable section
namespace NormalizedTotalHalfCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction
attribute [local instance] Classical.propDecidable

example {N n h₁ h₂ : ℕ} [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hmax : ∀ x,net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*(∑ j,if 3≤(rowSupport (model.A j)).card
        then (rowSupport (model.A j)).card^4 else 0)≤81*h₁ ∧
      4*(Finset.univ.filter fun j => 3≤(rowSupport (model.A j)).card).card≤h₁ := by
  simpa only [fourthMoment,nonBraidCount] using
    NormalizedTotalHalf.exists_model net hn hmax hpair

-- A nonlinear actual MAX4 network supplies the hypotheses for a two-input
-- restriction; both hidden index sets retain their original sizes.
example : ∃ model : NormalizedNetwork 2 (firstWidth 4) (secondWidth 4),
    (∀ x,model.eval x=Maximum 2 x) ∧ model.TranslationNormalized ∧
    4*fourthMoment model≤81*firstWidth 4 ∧
    4*nonBraidCount model≤firstWidth 4 := by
  obtain ⟨net,hnet,_hbias,_hrational⟩ := caterpillar_net 4
  obtain ⟨_S,_hS,model,hmax,hnorm,hmoment,hcount⟩ :=
    NormalizedTotalHalf.exists_model (n:=2) (ofOrdinary net)
      (ofOrdinary_translation_normalized net hnet)
      (ofOrdinary_computes_max net hnet) (by decide)
  exact ⟨model,hmax,hnorm,hmoment,hcount⟩

#check @NormalizedTotalHalf.exists_model
#print axioms NormalizedTotalHalf.exists_model
end NormalizedTotalHalfCheck
