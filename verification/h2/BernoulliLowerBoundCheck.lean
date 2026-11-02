import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.LowerBound
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
import MaxCaterpillar.Theorems

/-! Exact conditional scope. The growing structural H is open; no instance
of H at the literal large parameters is asserted by this checker. -/
set_option autoImplicit false
noncomputable section
namespace BernoulliLowerBoundCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction GrowingMatching Bernoulli
attribute [local instance] Classical.propDecidable

-- Literal matching parameters, independently exposed from their definitions.
example (n d : ℕ) : Parameters.matchingOrder n d=
    ⌊(Real.sqrt (n : ℝ)/(1000*(d : ℝ)))/8⌋₊ := rfl
example (n d : ℕ) : Parameters.minimumArity n d=
    4*⌊(Real.sqrt (n : ℝ)/(1000*(d : ℝ)))/8⌋₊+1 := rfl

-- H is a quantified actual-network obstruction, never a count/probability
-- estimate. M and L are the literal ALL-first-row support statistics.
example {n d h₁ h₂ : ℕ} [NeZero n] (hd : 1≤d) (hsize : 10000000000*d^2≤n)
    (H : ∀ (a b : ℕ) (model : NormalizedNetwork (Parameters.minimumArity n d) a b)
      (hn : model.TranslationNormalized),
      (∀ j,(NormalizedNetwork.rowSupport (model.A j)).card≤2) →
      (∀ x,model.eval x=Maximum (Parameters.minimumArity n d) x) →
      ∃ r : Fin b,∃ B∈matchings (braidInteractionGraph model hn r) (Parameters.matchingOrder n d),
        matchingVertices B⊆Finset.univ)
    (net : NormalizedNetwork n h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum n x)
    (hM : ((Finset.univ.filter fun j : Fin h₁=>
        3≤(NormalizedNetwork.rowSupport (net.A j)).card).card : ℝ)≤(d : ℝ)^2*(n : ℝ)^2)
    (hL : (∑ j,((NormalizedNetwork.rowSupport (net.A j)).card.descFactorial 4 : ℝ))≤
      (d : ℝ)^2*(n : ℝ)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt (n : ℝ)/(8000*(d : ℝ)))≤(h₂ : ℝ) := by
  apply conditional_sqrt_lower_bound hd hsize H net hn hnet
  · simpa only [largeSupports,firstSupports] using hM
  · exact hL

-- Numeric parameter feasibility is established independently of H.
example : Parameters.ParameterBounds 10000000000 1 :=
  Parameters.parameter_bounds _ _ (by decide) (by norm_num)

-- A proved low structural level and actual real MAX models exist. These
-- controls do not claim the unproved growing-H premise at the large choices.
example : LocalMatchingObstruction 5 2 := localMatchingObstruction_five_two
example : ∃ model : NormalizedNetwork 10 (firstWidth 10) (secondWidth 10),
    (∀ x,model.eval x=Maximum 10 x) ∧ model.TranslationNormalized := by
  obtain ⟨net,hmax,_hbias,_hrational⟩ := caterpillar_net 10
  exact ⟨NormalizedNetwork.ofOrdinary net,NormalizedNetwork.ofOrdinary_computes_max net hmax,
    NormalizedNetwork.ofOrdinary_translation_normalized net hmax⟩

#check @finite_conditional_bound
#check @conditional_sqrt_lower_bound
#print axioms actual_raw_event_cover
#print axioms conditional_union_bound
#print axioms finite_conditional_bound
#print axioms conditional_sqrt_lower_bound
#print axioms localMatchingObstruction_five_two
end BernoulliLowerBoundCheck
