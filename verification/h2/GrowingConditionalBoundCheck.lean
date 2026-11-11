import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
import MaxCaterpillar.Theorems

/-! The structural hypothesis is expanded as an actual network obstruction,
not a desired count or a probability estimate. Growing levels remain open. -/
set_option autoImplicit false
noncomputable section
namespace GrowingConditionalBoundCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction GrowingMatching Configurations
attribute [local instance] Classical.propDecidable

local instance totalNeZero {k m : ℕ} [NeZero k] : NeZero (m+k) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.le_add_left k m))⟩

example {k m q h₁ h₂ : ℕ} [NeZero k]
    (H : ∀ (a b : ℕ) (model : NormalizedNetwork k a b) (hn : model.TranslationNormalized),
      (∀ j,(NormalizedNetwork.rowSupport (model.A j)).card≤2) →
      (∀ x,model.eval x=Maximum k x) →
      ∃ r : Fin b,∃ B∈matchings (braidInteractionGraph model hn r) q,
        matchingVertices B⊆Finset.univ)
    (hq : 0<q) (net : NormalizedNetwork (m+k) h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum (m+k) x)
    (K : ℕ) (hm : 2≤m) (htotal : 4≤m+k) (hK : 4≤K) (hKm : K<m) :
    let c : ℝ := 7*(K : ℝ)/(24*(m : ℝ)*((m : ℝ)-1))
    1-8*(K : ℝ)/(m : ℝ)-
      (BadFirst.largeSupportCount (firstSupports net) : ℝ)*(k.descFactorial 3 : ℝ)/((m+k).descFactorial 3 : ℝ)-
      (∑ j,((firstSupports net j).card.descFactorial 4 : ℝ))/((m+k).descFactorial 4 : ℝ)*
        ((K : ℝ)^2*(1+(k : ℝ)/(m : ℝ))/(1-(K : ℝ)/(m : ℝ))+
          (k.descFactorial 2 : ℝ)*(K : ℝ)/2) ≤
      (h₂ : ℝ)*((k.descFactorial (2*q) : ℝ)/((m+k).descFactorial (2*q) : ℝ))*
        (c^q)⁻¹*Real.exp (c*((k : ℝ)*((m : ℝ)+(k : ℝ)-1))) :=
  conditional_finite_transfer H hq net hn hnet K hm htotal hK hKm

-- A proved structural instance exists: the closed star certificate gives H(5,2).
example : LocalMatchingObstruction 5 2 := localMatchingObstruction_five_two

-- Genuine actual networks exist for admissible k=5,m=5,K=4. No claim of
-- positivity of the full lower-side expression is part of this nonvacuity test.
example : ∃ model : NormalizedNetwork (5+5) (firstWidth 10) (secondWidth 10),
    (∀ x,model.eval x=Maximum (5+5) x) ∧ model.TranslationNormalized := by
  obtain ⟨net,hmax,_hbias,_hrational⟩ := caterpillar_net 10
  exact ⟨NormalizedNetwork.ofOrdinary net,NormalizedNetwork.ofOrdinary_computes_max net hmax,
    NormalizedNetwork.ofOrdinary_translation_normalized net hmax⟩

#check @conditional_finite_transfer
#print axioms shortRankEvent_fraction_le
#print axioms actual_event_cover
#print axioms finite_union_fraction_bound
#print axioms conditional_finite_transfer
#print axioms localMatchingObstruction_five_two
end GrowingConditionalBoundCheck
