import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction.Support
import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction.ModelStats

/-! # One actual coordinate restriction controls both support statistics

The input is the ordinary arbitrary-bias network and its all-real-input MAX
identity. Whole supports are selected before localization; no inputs are
identified, including when the original arity is odd.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
open BigOperators NormalizedNetwork
variable {N n h₁ h₂ : ℕ}

lemma actual_first_width_pos [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) : 1 ≤ h₁ := by
  obtain ⟨j,_hj⟩ := net.toZ.exists_neg (net.toZ_eval_of_max hnet)
  exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)

/-- For any positive selected half-pair count, one actual restricted model
simultaneously satisfies the fourth-moment and non-braid-count budgets.
Both its widths remain the original index types. -/
theorem exists_actual_model [NeZero N] [NeZero n] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (hpair : 2*n ≤ N) :
    ∃ S : Finset (Fin N), S.card = n ∧
      ∃ model : NormalizedNetwork n h₁ h₂,
        (∀ x, model.eval x = Maximum n x) ∧ model.TranslationNormalized ∧
        4*fourthMoment model ≤ 81*h₁ ∧
        4*nonBraidCount model ≤ h₁ ∧
        4*max (fourthMoment model) 1 ≤ 81*h₁ := by
  classical
  obtain ⟨S,hS,hbudget⟩ := exists_half_support_fourth_moment hpair
    (fun j => rowSupport (net.W₁ j))
  subst n
  obtain ⟨model,hmax,hnorm,_hrows,_hfeed,hcost⟩ :=
    exists_ordinary_set_restriction net hnet S
  have hm : 4*fourthMoment model ≤ 81*h₁ := by
    have hc := hcost (fun r => r^4)
    exact (Nat.mul_le_mul_left 4 hc).trans hbudget
  exact ⟨S,rfl,model,hmax,hnorm,hm,count_budget_of_moment model hm,
    regularized_moment_budget model (actual_first_width_pos net hnet) hm⟩

/-- The requested arbitrary-parity half restriction. The positive selected
arity instance is derived internally from N≥1040; no normalized-model or
support-budget assumption is supplied by the caller. -/
theorem exists_actual_half_model [NeZero N] (hN : 1040 ≤ N) (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    letI : NeZero (N/2) := ⟨Nat.ne_of_gt
      (Nat.div_pos (le_trans (by decide : 2 ≤ 1040) hN) (by decide : 0 < 2))⟩
    ∃ S : Finset (Fin N), S.card = N/2 ∧
      ∃ model : NormalizedNetwork (N/2) h₁ h₂,
        (∀ x, model.eval x = Maximum (N/2) x) ∧ model.TranslationNormalized ∧
        4*fourthMoment model ≤ 81*h₁ ∧
        4*nonBraidCount model ≤ h₁ ∧
        4*max (fourthMoment model) 1 ≤ 81*h₁ := by
  letI : NeZero (N/2) := ⟨Nat.ne_of_gt
    (Nat.div_pos (le_trans (by decide : 2 ≤ 1040) hN) (by decide : 0 < 2))⟩
  exact exists_actual_model net hnet (by linarith only [Nat.mul_div_le N 2])

#check @exists_actual_model
#check @exists_actual_half_model
#print axioms exists_actual_model
#print axioms exists_actual_half_model
end MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
