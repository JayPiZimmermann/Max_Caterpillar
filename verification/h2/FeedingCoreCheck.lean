import MaxCaterpillar.Frontier.RandomRestriction.FeedingCounting

set_option autoImplicit false
noncomputable section
namespace FeedingCoreCheck
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction NormalizedNetwork FeedingCore
open DominantGap Cartesian

example {N h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂) (x : Point N) (k : Fin h₂) :
    (core net).inner k x=net.inner k x := core_inner net k x

example {N h₁ h₂ : ℕ} (net : NormalizedNetwork N h₁ h₂) (x : Point N) :
    (absorb net : NormalizedNetwork N h₁ (h₂+h₁)).eval x=net.eval x := absorb_eval net x

-- Only first rows actually entering a second neuron are support-constrained.
-- There is no premise on first-output coefficients B or nonfeeding A rows.
example {h₁ h₂ : ℕ} (net : NormalizedNetwork 5 h₁ h₂)
    (hn : net.TranslationNormalized)
    (hs : ∀ j,(∃ k,net.W k j≠0) → (rowSupport (net.A j)).card≤2)
    (hmax : ∀ x,net.eval x=Maximum 5 x) :
    ∃ k : Fin h₂,HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) Finset.univ :=
  exists_original_matching_of_feeding_braid net hn hs hmax

example {N m h₁ h₂ : ℕ} [NeZero N]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin 5 ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,(∃ k,net.W k j≠0) → 3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) :=
  structural_witness_of_generic_embedding_feeding net hn hnet f e p T hcomp h hno

-- The last explicit budget is a half-restriction transfer obligation, rather
-- than an assumed count/probability estimate. Expand the cutoff quantifiers.
example {m h₁ h₂ : ℕ} (net : NormalizedNetwork (m+5) h₁ h₂)
    (hn : net.TranslationNormalized) (hnet : ∀ x,net.eval x=Maximum (m+5) x)
    (hm : 400≤m)
    (hbudget : 240*ActualHalfRestriction.nonBraidCount (core net)≤(m+5).descFactorial 3) :
    ∀ K : ℕ,4≤K → (K : ℝ)≤(m : ℝ)/100 →
      16*(NetworkLowerBound.regularizedMoment (core net) : ℝ)*(K : ℝ)^2≤(m : ℝ)^4 →
      (42/100 : ℝ)*(K : ℝ)^2≤400*(h₂ : ℝ) :=
  model_counting_feeding_on_tail net hn hnet hm hbudget

#check @exists_original_matching_of_feeding_braid
#check @structural_witness_of_generic_embedding_feeding
#check @model_counting_feeding_on_tail
#print axioms core_inner
#print axioms core_edgeWeight
#print axioms absorb_eval
#print axioms absorb_normalized
#print axioms absorb_auxiliary_edgeWeight
#print axioms exists_original_matching_of_feeding_braid
#print axioms structural_witness_of_generic_embedding_feeding
#print axioms model_counting_feeding_on_tail
end FeedingCoreCheck
