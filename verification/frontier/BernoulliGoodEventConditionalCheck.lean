import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Conditional

set_option autoImplicit false
namespace BernoulliGoodEventConditionalCheck
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent (ACRole BRole)
open GrowingMatching.Bernoulli.GoodEvent
variable {n : ℕ}

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (i : Fin n) :
    condMean p D (fun S=>if i∈S then (1:ℝ) else 0)≤p :=
  condMean_mem_le hp0 hp1 D hD hpos i

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (I : Finset (Fin n)) (hI : I.card=2) :
    condMean p D (fun S=>if I⊆S then (1:ℝ) else 0)≤p^2 :=
  condMean_pair_subset_le hp0 hp1 D hD hpos I hI

example {m0 m K : ℕ} (h0 : 4≤m0) (hm : m0≤m) (hK : K<m0) :
    caseARate m K≤caseARate m0 K ∧ caseBRate m K≤caseBRate m0 K ∧
    caseCRate m K≤caseCRate m0 K :=
  ⟨caseARate_le_of_tail_lower_bound h0 hm hK,
    caseBRate_le_of_tail_lower_bound h0 hm hK,caseCRate_le_of_tail_lower_bound h0 hm⟩

example (p : ℝ) (m K : ℕ) : badSupportRate p m K=
    (K:ℝ)^2/((1-(K:ℝ)/(m:ℝ))*(m.descFactorial 4:ℝ))+
    p*(K:ℝ)^2/((m:ℝ)*(1-(K:ℝ)/(m:ℝ))*(m.descFactorial 3:ℝ))+
    p^2*(K:ℝ)/(2*(m.descFactorial 2:ℝ)) := rfl

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hpos : 0<mass p D)
    (T : Finset (Fin n)) (R : ACRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0) (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseAMean T S K R)≤caseARate m0 K :=
  conditional_caseAMean_le hp0 hp1 D hpos T R m0 K h0 hK htail

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (R : BRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0) (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseBMean T S K R)≤caseBRate m0 K*p :=
  conditional_caseBMean_le hp0 hp1 D hD hpos T R m0 K h0 hK htail

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (R : ACRole T) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0) (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>caseCMean T S K R)≤caseCRate m0 K*p^2 :=
  conditional_caseCMean_le hp0 hp1 D hD hpos T R m0 K h0 hK htail

example {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (T : Finset (Fin n)) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0) (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>supportBadFraction T S K)≤
      (T.card.descFactorial 4:ℝ)*badSupportRate p m0 K :=
  conditional_supportBadFraction_le hp0 hp1 D hD hpos T m0 K h0 hK htail

example {κ : Type*} [Fintype κ] {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1)
    (D : Finset (Finset (Fin n))) (hD : IsLowerSet (D : Set (Finset (Fin n))))
    (hpos : 0<mass p D) (supports : κ→Finset (Fin n)) (m0 K : ℕ)
    (h0 : 4≤m0) (hK : K<m0) (htail : ∀ S∈D,m0≤Sampling.tailCount S) :
    condMean p D (fun S=>familyBadFraction supports S K)≤
      (∑ j,((supports j).card.descFactorial 4:ℝ))*
       ((K:ℝ)^2/((1-(K:ℝ)/(m0:ℝ))*(m0.descFactorial 4:ℝ))+
        p*(K:ℝ)^2/((m0:ℝ)*(1-(K:ℝ)/(m0:ℝ))*(m0.descFactorial 3:ℝ))+
        p^2*(K:ℝ)/(2*(m0.descFactorial 2:ℝ))) :=
  conditional_familyBadFraction_le hp0 hp1 D hD hpos supports m0 K h0 hK htail

#print axioms condMean_mono_on
#print axioms condMean_const
#print axioms condMean_add
#print axioms condMean_const_mul
#print axioms condMean_sum
#print axioms condMean_le_const
#print axioms condMean_mem_le
#print axioms condMean_pair_subset_le
#print axioms caseARate_le_of_tail_lower_bound
#print axioms caseBRate_le_of_tail_lower_bound
#print axioms caseCRate_le_of_tail_lower_bound
#print axioms badSupportRate_eq_roleRates
#print axioms conditional_caseAMean_le
#print axioms conditional_caseBMean_le
#print axioms conditional_caseCMean_le
#print axioms conditional_supportBadFraction_le
#print axioms conditional_familyBadFraction_le
end BernoulliGoodEventConditionalCheck
