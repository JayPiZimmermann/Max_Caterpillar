import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.FromZ

/-! # Ordinary arbitrary-bias MAX networks have faithful indexed normal forms

Bias removal is an already proved exact consequence of positive homogeneity.
The first and second hidden indices are the original finite types; no new
neuron is introduced and no finite coefficient alphabet is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N h₁ h₂ : ℕ}

noncomputable def ofOrdinary (net : Network N h₁ h₂) : NormalizedNetwork N h₁ h₂ :=
  fromZ net.toZ

theorem ofOrdinary_computes_max [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    ∀ x, (ofOrdinary net).eval x = Maximum N x :=
  fromZ_computes_max net.toZ (net.toZ_eval_of_max hnet)

theorem ofOrdinary_translation_normalized [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    (ofOrdinary net).TranslationNormalized :=
  fromZ_translation_normalized net.toZ (net.toZ_eval_of_max hnet)

/-- The first covectors are actual original rows or zero, with the same index. -/
theorem ofOrdinary_first_row (net : Network N h₁ h₂) (j : Fin h₁) :
    (ofOrdinary net).A j =
      if (∑ i, net.W₁ j i) = 0 then net.W₁ j else 0 := rfl

theorem ofOrdinary_support_subset (net : Network N h₁ h₂) (j : Fin h₁) :
    rowSupport ((ofOrdinary net).A j) ⊆ rowSupport (net.W₁ j) :=
  fromZ_support_subset net.toZ j

theorem ofOrdinary_feeding_original (net : Network N h₁ h₂) (j : Fin h₁)
    (hj : (ofOrdinary net).Feeding j) : ∃ k, net.W₂ k j ≠ 0 :=
  fromZ_feeding_original net.toZ j hj

/-- The normalized function is exactly the one-sided all-ones derivative
of the original function. This is an exact equality for every positive step,
not an asymptotic numerical statement. -/
theorem ofOrdinary_exact_direction [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (x : Point N) {ε : ℝ} (hε : 0 < ε) :
    net.eval (diag 1 + ε • x) = net.eval (diag 1) + ε * (ofOrdinary net).eval x := by
  rw [hnet,hnet,ofOrdinary_computes_max net hnet,Maximum_diag]
  have he : diag 1 + ε • x = ε • x + diag 1 := add_comm _ _
  rw [he,Maximum_add_diag,Maximum_smul hε]
  ring

#check @ofOrdinary_computes_max
#print axioms ofOrdinary_computes_max
#print axioms ofOrdinary_translation_normalized
#print axioms ofOrdinary_exact_direction
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
