import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork

/-! # Actual indexed support statistics of a normalized skip model -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
open BigOperators NormalizedNetwork
variable {N h₁ h₂ : ℕ}

noncomputable def fourthMoment (net : NormalizedNetwork N h₁ h₂) : ℕ :=
  ∑ j, if 3 ≤ (rowSupport (net.A j)).card then (rowSupport (net.A j)).card^4 else 0

noncomputable def nonBraidCount (net : NormalizedNetwork N h₁ h₂) : ℕ :=
  (Finset.univ.filter fun j => 3 ≤ (rowSupport (net.A j)).card).card

/-- Each genuinely non-braid row costs at least 3^4=81. -/
lemma moment_controls_count (net : NormalizedNetwork N h₁ h₂) :
    81 * nonBraidCount net ≤ fourthMoment net := by
  classical
  have h : (∑ j, if 3 ≤ (rowSupport (net.A j)).card then 81 else 0) ≤ fourthMoment net := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : 3 ≤ (rowSupport (net.A j)).card
    · simp only [if_pos hj]
      have hp := Nat.pow_le_pow_left hj 4
      norm_num at hp
      exact hp
    · simp only [if_neg hj,le_refl]
  simpa only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,nonBraidCount,mul_comm] using h

lemma count_budget_of_moment (net : NormalizedNetwork N h₁ h₂)
    (hbudget : 4 * fourthMoment net ≤ 81 * h₁) :
    4 * nonBraidCount net ≤ h₁ := by
  have hc := moment_controls_count net
  linarith only [hc,hbudget]

/-- Replacing a zero fourth moment by one preserves the same uniform budget
when an actual original first layer is nonempty. -/
lemma regularized_moment_budget (net : NormalizedNetwork N h₁ h₂)
    (hh₁ : 1 ≤ h₁) (hbudget : 4 * fourthMoment net ≤ 81 * h₁) :
    4 * max (fourthMoment net) 1 ≤ 81 * h₁ := by
  rcases le_total (fourthMoment net) 1 with h | h
  · rw [max_eq_right h]
    linarith only [hh₁]
  · rw [max_eq_left h]
    exact hbudget

#check @fourthMoment
#print axioms moment_controls_count
#print axioms regularized_moment_budget
end MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
