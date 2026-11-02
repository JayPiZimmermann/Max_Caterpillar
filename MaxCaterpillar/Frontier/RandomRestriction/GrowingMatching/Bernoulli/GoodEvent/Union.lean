import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Pointwise

/-! # Literal union probabilities for intrinsic original-label bad events -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {n : ℕ}

private theorem rankAverage_add' {m : ℕ} (K : ℕ) (f g : Finset (Fin m)→ℝ) :
    rankAverage K (fun Γ=>f Γ+g Γ)=rankAverage K f+rankAverage K g := by
  unfold rankAverage
  simp only [mul_add,Finset.sum_add_distrib]

private theorem rankAverage_sum' {m : ℕ} {ι : Type*} [Fintype ι]
    (K : ℕ) (f : ι→Finset (Fin m)→ℝ) :
    rankAverage K (fun Γ=>∑ i,f i Γ)=∑ i,rankAverage K (f i) := by
  unfold rankAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def supportBadFraction (T S : Finset (Fin n)) (K : ℕ) : ℝ :=
  ((supportBadConfigurations T S K).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))×
      Equiv.Perm (Fin (Sampling.tailCount S)))

noncomputable def familyBadFraction {κ : Type*} [Fintype κ]
    (supports : κ→Finset (Fin n)) (S : Finset (Fin n)) (K : ℕ) : ℝ :=
  ((familyBadConfigurations supports S K).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))×
      Equiv.Perm (Fin (Sampling.tailCount S)))

theorem supportBadFraction_eq_rankAverage (T S : Finset (Fin n)) (K : ℕ) :
    supportBadFraction T S K=rankAverage K (fun Γ=>
      ((supportBadAt T S Γ).card:ℝ)/
        Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S)))) := by
  classical
  have hc : ((supportBadConfigurations T S K).card:ℝ)=
      ∑ ρ : Equiv.Perm (Fin (Sampling.tailCount S)),
        ((supportBadAt T S (smallRankGaps ρ K)).card:ℝ) := by
    rw [supportBadConfigurations,Finset.natCast_card_filter,Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.sum_boole]
    change ((Finset.univ.filter (fun τ=>τ∈supportBadAt T S (smallRankGaps ρ K))).card:ℝ)=_
    rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
  unfold supportBadFraction rankAverage
  rw [hc,Fintype.card_prod,Nat.cast_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem supportBadAt_card_le (T S : Finset (Fin n))
    (Γ : Finset (Fin (Sampling.tailCount S))) :
    (supportBadAt T S Γ).card≤
      (∑ R : ACRole T,(caseA T S Γ R).card)+
      (∑ R : BRole T,(caseB T S Γ R).card)+
      (∑ R : ACRole T,(caseC T S Γ R).card) := by
  classical
  unfold supportBadAt
  exact ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)).trans
      (Nat.add_le_add (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
        Finset.card_biUnion_le)

theorem supportBadFraction_le_roleMeans (T S : Finset (Fin n)) (K : ℕ) :
    supportBadFraction T S K≤(∑ R : ACRole T,caseAMean T S K R)+
      (∑ R : BRole T,caseBMean T S K R)+(∑ R : ACRole T,caseCMean T S K R) := by
  classical
  rw [supportBadFraction_eq_rankAverage]
  have hfixed := rankAverage_mono K _ _ (fun Γ=>
    div_le_div_of_le (by positivity : (0:ℝ)≤
      Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))))
      (show ((supportBadAt T S Γ).card:ℝ)≤
        (∑ R : ACRole T,((caseA T S Γ R).card:ℝ))+
        (∑ R : BRole T,((caseB T S Γ R).card:ℝ))+
        (∑ R : ACRole T,((caseC T S Γ R).card:ℝ)) by
          exact_mod_cast supportBadAt_card_le T S Γ))
  apply hfixed.trans_eq
  unfold caseAMean caseBMean caseCMean
  simp only [add_div,Finset.sum_div]
  rw [rankAverage_add',rankAverage_add',rankAverage_sum',rankAverage_sum',rankAverage_sum']

theorem familyBadFraction_le_sum {κ : Type*} [Fintype κ]
    (supports : κ→Finset (Fin n)) (S : Finset (Fin n)) (K : ℕ) :
    familyBadFraction supports S K≤∑ j,supportBadFraction (supports j) S K := by
  classical
  have hc : (familyBadConfigurations supports S K).card≤
      ∑ j,(supportBadConfigurations (supports j) S K).card := Finset.card_biUnion_le
  unfold familyBadFraction supportBadFraction
  rw [←Finset.sum_div]
  apply div_le_div_of_le (by positivity)
  exact_mod_cast hc

#print axioms supportBadFraction_eq_rankAverage
#print axioms supportBadFraction_le_roleMeans
#print axioms familyBadFraction_le_sum
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
