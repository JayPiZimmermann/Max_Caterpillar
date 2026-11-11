import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Union

set_option autoImplicit false
namespace BernoulliGoodEventPointwiseCheck
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (ACRole BRole rankAverage)
open GrowingMatching.Bernoulli.GoodEvent
variable {n m d : ℕ}

example (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m)) :
    ((placementEvent e q B).card:ℝ)/Fintype.card (Equiv.Perm (Fin m))≤
      (B.card:ℝ)/(m.descFactorial d:ℝ) := placementEvent_fraction_le e q B

example (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin d ↪ Fin m))
    (hn : ¬∃ f : Fin d ↪ Fin m,∀ i,e (f i)=q i) :
    placementEvent e q B=∅ := placementEvent_empty_of_no_factor e q B hn

example (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T)
    (hm : 4≤Sampling.tailCount S) (hK : K<Sampling.tailCount S) :
    caseAMean T S K R≤caseARate (Sampling.tailCount S) K := caseAMean_le T S K R hm hK

example (T S : Finset (Fin n)) (K : ℕ) (R : BRole T)
    (hm : 4≤Sampling.tailCount S) (hK : K<Sampling.tailCount S) :
    caseBMean T S K R≤caseBRate (Sampling.tailCount S) K*
      (if R.selected∈S then (1:ℝ) else 0) := caseBMean_le T S K R hm hK

example (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T)
    (hm : 4≤Sampling.tailCount S) (hK : K<Sampling.tailCount S) :
    caseCMean T S K R≤caseCRate (Sampling.tailCount S) K*
      (if R.other⊆S then (1:ℝ) else 0) := caseCMean_le T S K R hm hK

example (T S : Finset (Fin n)) (K : ℕ) :
    supportBadFraction T S K=
      ((supportBadConfigurations T S K).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))×
          Equiv.Perm (Fin (Sampling.tailCount S))) := rfl

example (T S : Finset (Fin n)) (K : ℕ) :
    supportBadFraction T S K=rankAverage K (fun Γ=>
      ((supportBadAt T S Γ).card:ℝ)/Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S)))) :=
  supportBadFraction_eq_rankAverage T S K

example (T S : Finset (Fin n)) (K : ℕ) :
    supportBadFraction T S K≤(∑ R : ACRole T,caseAMean T S K R)+
      (∑ R : BRole T,caseBMean T S K R)+(∑ R : ACRole T,caseCMean T S K R) :=
  supportBadFraction_le_roleMeans T S K

example {κ : Type*} [Fintype κ] (supports : κ→Finset (Fin n))
    (S : Finset (Fin n)) (K : ℕ) :
    familyBadFraction supports S K≤∑ j,supportBadFraction (supports j) S K :=
  familyBadFraction_le_sum supports S K

#print axioms placementEvent_card_eq
#print axioms placementEvent_fraction_le
#print axioms placementEvent_empty_of_no_factor
#print axioms placementRankMean_caseA_le
#print axioms placementRankMean_caseB_le
#print axioms placementRankMean_caseC_le
#print axioms caseAMean_le
#print axioms caseBMean_le
#print axioms caseCMean_le
#print axioms supportBadFraction_eq_rankAverage
#print axioms supportBadFraction_le_roleMeans
#print axioms familyBadFraction_le_sum
end BernoulliGoodEventPointwiseCheck
