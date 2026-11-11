import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Monotone
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance

set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
attribute [local instance] Classical.propDecidable

namespace GrowingMatchingMonotoneChecks

/-- The entire conclusion concerns actual larger-input networks, with the
same q and their own actual signed braid interaction graph. -/
theorem expanded_actual_type {k₀ n q : ℕ} [NeZero k₀] [NeZero n]
    (H : LocalMatchingObstruction k₀ q) (hkn : k₀ ≤ n) (hq : 0 < q) :
    ∀ (h₁ h₂ : ℕ) (model : NormalizedNetwork n h₁ h₂)
      (hn : model.TranslationNormalized),
      (∀ j, (NormalizedNetwork.rowSupport (model.A j)).card ≤ 2) →
      (∀ x, model.eval x = Maximum n x) →
      ∃ r : Fin h₂, ∃ B ∈ matchings (braidInteractionGraph model hn r) q,
        matchingVertices B ⊆ (Finset.univ : Finset (Fin n)) :=
  localMatchingObstruction_mono_arity H hkn hq

/-- Boundary control: equality of the input arities is allowed. -/
theorem equal_arity {k q : ℕ} [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0 < q) :
    LocalMatchingObstruction k q :=
  localMatchingObstruction_mono_arity H (le_refl k) hq

/-- The known five-input obstruction propagates without increasing q. -/
theorem known_five_two_upward {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    LocalMatchingObstruction n 2 :=
  localMatchingObstruction_mono_arity localMatchingObstruction_five_two hn (by decide)

/-- A strict arity increase provides a concrete nonidentity control. -/
theorem six_two : LocalMatchingObstruction 6 2 :=
  known_five_two_upward (by decide)

end GrowingMatchingMonotoneChecks

#print axioms localMatchingObstruction_mono_arity
#print axioms GrowingMatchingMonotoneChecks.expanded_actual_type
#print axioms GrowingMatchingMonotoneChecks.equal_arity
#print axioms GrowingMatchingMonotoneChecks.known_five_two_upward
#print axioms GrowingMatchingMonotoneChecks.six_two
