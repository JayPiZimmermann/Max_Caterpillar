import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
import MaxCaterpillar.Frontier.Constructions

set_option autoImplicit false
namespace ActualHalfRestrictionCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction NormalizedNetwork ActualHalfRestriction

-- All normalization sums and both statistics are expanded in this contract.
example {N h₁ h₂ : ℕ} [NeZero N] (hN : 1040 ≤ N) (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    letI : NeZero (N/2) := ⟨Nat.ne_of_gt
      (Nat.div_pos (le_trans (by decide : 2 ≤ 1040) hN) (by decide : 0 < 2))⟩
    ∃ S : Finset (Fin N), S.card = N/2 ∧
      ∃ model : NormalizedNetwork (N/2) h₁ h₂,
        (∀ x, model.eval x = Maximum (N/2) x) ∧
        (∀ j, ∑ i, model.A j i = 0) ∧
        (∀ k, ∑ i, model.U k i = 0) ∧ (∑ i, model.L i = 1) ∧
        4*(∑ j, if 3 ≤ (rowSupport (model.A j)).card
          then (rowSupport (model.A j)).card^4 else 0) ≤ 81*h₁ ∧
        4*(Finset.univ.filter fun j => 3 ≤ (rowSupport (model.A j)).card).card ≤ h₁ ∧
        4*max (∑ j, if 3 ≤ (rowSupport (model.A j)).card
          then (rowSupport (model.A j)).card^4 else 0) 1 ≤ 81*h₁ := by
  letI : NeZero (N/2) := ⟨Nat.ne_of_gt
    (Nat.div_pos (le_trans (by decide : 2 ≤ 1040) hN) (by decide : 0 < 2))⟩
  obtain ⟨S,hS,model,hmax,hnorm,hA,hM,hreg⟩ := exists_actual_half_model hN net hnet
  exact ⟨S,hS,model,hmax,hnorm.1,hnorm.2.1,hnorm.2.2,hA,hM,hreg⟩

-- A genuine odd-input network is restricted without identifying any inputs.
example : ∃ S : Finset (Fin 3), S.card = 1 ∧
    ∃ model : NormalizedNetwork 1 4 3,
      (∀ x, model.eval x = Maximum 1 x) ∧ model.TranslationNormalized ∧
      4*fourthMoment model ≤ 81*4 ∧ 4*nonBraidCount model ≤ 4 ∧
      4*max (fourthMoment model) 1 ≤ 81*4 :=
  exists_actual_model maxThreeNet maxThreeNet_eval (by norm_num)

#check @exists_actual_half_model
#print axioms exists_half_support_fourth_moment
#print axioms actual_first_width_pos
#print axioms moment_controls_count
#print axioms count_budget_of_moment
#print axioms regularized_moment_budget
#print axioms exists_actual_model
#print axioms exists_actual_half_model
end ActualHalfRestrictionCheck
