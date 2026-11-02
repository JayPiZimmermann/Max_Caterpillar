import MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction

/-! A simultaneous half-restriction budget for all first rows of a normalized
skip network. Both hidden index types are retained. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf
open BigOperators NormalizedNetwork ActualHalfRestriction
variable {N n h₁ h₂ : ℕ}

/-- The same selected set and actual indexed model obey both support budgets.
This counts every original first row, including rows feeding only the output. -/
theorem exists_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N),S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x,model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      4*fourthMoment model≤81*h₁ ∧ 4*nonBraidCount model≤h₁ := by
  classical
  obtain ⟨S,hS,hbudget⟩ := exists_half_support_fourth_moment hpair
    (fun j => rowSupport (net.A j))
  subst n
  obtain ⟨model,hmax,hnorm,hrows,_hfeed⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost : fourthMoment model=
      ∑ j,if 3≤(rowSupport (net.A j)).card ∧ rowSupport (net.A j)⊆S
        then (rowSupport (net.A j)).card^4 else 0 := by
    unfold fourthMoment
    apply Finset.sum_congr rfl
    intro j _
    rw [hrows j,selectedEmbedding_image]
    by_cases hs : rowSupport (net.A j)⊆S
    · rw [if_pos hs,card_rowSupport_restrict (selectedEmbedding S) (net.A j)
        (by rwa [selectedEmbedding_image])]
      simp only [hs,and_true]
    · simp only [if_neg hs,rowSupport_zero,Finset.card_empty,
        show ¬3≤0 from by decide,hs,and_false,ite_false]
  have hm : 4*fourthMoment model≤81*h₁ := by
    rw [hcost]
    exact hbudget
  exact ⟨S,rfl,model,hmax,hnorm,hm,count_budget_of_moment model hm⟩

#check @exists_model
#print axioms exists_model
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf
