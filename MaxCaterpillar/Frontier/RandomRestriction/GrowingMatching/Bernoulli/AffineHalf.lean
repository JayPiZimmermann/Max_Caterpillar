import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.AffineGeneralRows.Budgets

/-! # Actual same-width affine half models for the Bernoulli size regime

This leaf contains no Bernoulli transfer assumption. It constructs one
normalized half model, with both all-first-row budgets, directly from the
original nine arrays, exact MAX and a quadratic total first-width budget.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Affine
open BigOperators NormalizedNetwork ActualHalfRestriction AffineSkipExtension AffineGeneralRows
variable {N h₁ h₂ : ℕ}

lemma half_size_weakening (C : ℕ)
    (hsize : 10000000000*(quadraticParameter C)^2≤N/2) :
    8000*(quadraticParameter C)^2≤N/2 :=
  (Nat.mul_le_mul_right _ (by norm_num : (8000:ℕ)≤10000000000)).trans hsize

def bernoulliOriginalDimension_neZero (N C : ℕ) (hC : 1≤C)
    (hsize : 10000000000*(quadraticParameter C)^2≤N/2) : NeZero N :=
  originalDimension_neZero N C hC (half_size_weakening C hsize)

def bernoulliHalfDimension_neZero (N C : ℕ) (hC : 1≤C)
    (hsize : 10000000000*(quadraticParameter C)^2≤N/2) : NeZero (N/2) :=
  halfDimension_neZero N C hC (half_size_weakening C hsize)

/-- The same actual selected model supplies the two literal support budgets
needed by a Bernoulli transfer. Every original first slot, including an
output-only slot, is charged. Both original hidden widths are unchanged. -/
theorem exists_affine_quadratic_half_budgets (C : ℕ) (hC : 1≤C)
    (hsize : 10000000000*(quadraticParameter C)^2≤N/2)
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := bernoulliOriginalDimension_neZero N C hC hsize;
      ∀ x,AffineSkipExtension.eval net x=Maximum N x)
    (hwidth : h₁≤C*N^2) :
    letI := bernoulliHalfDimension_neZero N C hC hsize;
    ∃ S : Finset (Fin N),S.card=N/2 ∧ ∃ model : NormalizedNetwork (N/2) h₁ h₂,
      (∀ x,model.eval x=Maximum (N/2) x) ∧ model.TranslationNormalized ∧
      (nonBraidCount model : ℝ)≤(quadraticParameter C : ℝ)^2*((N/2:ℕ):ℝ)^2 ∧
      (∑ j,((rowSupport (model.A j)).card.descFactorial 4 : ℝ))≤
        (quadraticParameter C : ℝ)^2*((N/2:ℕ):ℝ)^2 := by
  letI := bernoulliOriginalDimension_neZero N C hC hsize
  letI := bernoulliHalfDimension_neZero N C hC hsize
  obtain ⟨S,hS,model,hmax,hnorm,hmoment,_hcount⟩ :=
    exists_affine_half_model (n:=N/2) net hnet (by linarith only [Nat.mul_div_le N 2])
  have hbudget := fourthMoment_le_quadratic_budget C hC
    (half_positive N C hC (half_size_weakening C hsize)) hwidth model hmoment
  obtain ⟨hM,hL⟩ := general_rows_budgets_of_fourthMoment C model hbudget
  exact ⟨S,hS,model,hmax,hnorm,hM,hL⟩

#check @exists_affine_quadratic_half_budgets
#print axioms exists_affine_quadratic_half_budgets
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Affine
