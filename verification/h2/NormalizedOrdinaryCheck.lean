import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Ordinary
import MaxCaterpillar.Fiber.Star65.Construction

set_option autoImplicit false
namespace NormalizedOrdinaryCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction NormalizedNetwork

example {N h₁ h₂ : ℕ} [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) :
    ∃ model : NormalizedNetwork N h₁ h₂,
      (∀ x, model.eval x = Maximum N x) ∧ model.TranslationNormalized ∧
      (∀ j, model.A j = if (∑ i, net.W₁ j i) = 0 then net.W₁ j else 0) ∧
      (∀ j, model.Feeding j → ∃ k, net.W₂ k j ≠ 0) := by
  exact ⟨ofOrdinary net,ofOrdinary_computes_max net hnet,
    ofOrdinary_translation_normalized net hnet,ofOrdinary_first_row net,
    ofOrdinary_feeding_original net⟩

example {N h₁ h₂ : ℕ} [NeZero N] (net : Network N h₁ h₂)
    (hnet : ∀ x, net.eval x = Maximum N x) (x : Point N) {ε : ℝ} (hε : 0 < ε) :
    net.eval (diag 1 + ε • x) = net.eval (diag 1) + ε*(ofOrdinary net).eval x :=
  ofOrdinary_exact_direction net hnet x hε

-- A concrete all-input ordinary network witnesses the model reduction.
example : ∀ x, (ofOrdinary (Fiber.Star65.branchINet 1 0)).eval x = Maximum 4 x :=
  ofOrdinary_computes_max _
    (fun x => Fiber.Star65.branchINet_eval (by norm_num) (by norm_num) (by norm_num) x)

#check @ofOrdinary_computes_max
#print axioms ofOrdinary_computes_max
#print axioms ofOrdinary_translation_normalized
#print axioms ofOrdinary_first_row
#print axioms ofOrdinary_feeding_original
#print axioms ofOrdinary_exact_direction
end NormalizedOrdinaryCheck
