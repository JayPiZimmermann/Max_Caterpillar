import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization
import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction

/-! # A same-width half restriction for normalized affine-skip models

All first rows are charged, including output-only rows. The selected set
and generic tied point are constructed; odd ambient arity is allowed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
open BigOperators NormalizedNetwork ActualHalfRestriction AffineSkipExtension
variable {N n h₁ h₂ : ℕ}

/-- The generic normalized model admits the same half moment restriction
as an ordinary network. Both original hidden index sets are retained. -/
theorem exists_normalized_half_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hnet : ∀ x,net.eval x=Maximum N x)
    (hnorm : net.TranslationNormalized) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*fourthMoment model≤81*h₁ ∧ 4*nonBraidCount model≤h₁ := by
  classical
  obtain ⟨S,hS,hbudget⟩ := exists_half_support_fourth_moment hpair
    (fun j => rowSupport (net.A j))
  subst n
  obtain ⟨model,hmax,hn,hrows,_hfeed⟩ :=
    exists_localized_normalized net hnet hnorm.1 (selectedEmbedding S)
  have hc := indexed_support_cost_le_of_masked_restriction (selectedEmbedding S)
    net.A model.A (fun j => rowSupport (net.A j)⊆Finset.univ.image (selectedEmbedding S))
    (fun r => r^4) (fun _ h => h) hrows
  rw [selectedEmbedding_image] at hc
  have hm : 4*fourthMoment model≤81*h₁ :=
    (Nat.mul_le_mul_left 4 hc).trans hbudget
  exact ⟨S,rfl,model,hmax,hn,hm,count_budget_of_moment model hm⟩

/-- Arbitrary original affine biases and skips cause no width increase in
the exact half model or either simultaneous support budget. -/
theorem exists_affine_half_model [NeZero N] [NeZero n]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,AffineSkipExtension.eval net x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*fourthMoment model≤81*h₁ ∧ 4*nonBraidCount model≤h₁ :=
  exists_normalized_half_model (normalizedModel net) (normalizedModel_computes_max net hnet)
    (normalizedModel_translation_normalized net hnet) hpair

#check @exists_affine_half_model
#print axioms exists_normalized_half_model
#print axioms exists_affine_half_model
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows
