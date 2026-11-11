import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Events
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.UniformPlacementRank

/-! # Actual fixed-selected-set bad-role probabilities

The means average the literal tail-permutation event fractions over literal
rank permutations. Fixed original labels may fail to belong to the tail; the
uniform-placement inequality already handles that case by an empty event.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {n m : ℕ}

theorem caseCTailPlacements_card_le (Γ : Finset (Fin m)) :
    (caseCTailPlacements Γ).card≤(adjacentPairs Γ).card := by
  classical
  let f : (Fin 2 ↪ Fin m)→Fin m×Fin m := fun q=>(q 0,q 1)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Function.Embedding.ext
    intro i
    have h0 := congrArg Prod.fst hab
    have h1 := congrArg Prod.snd hab
    fin_cases i <;> assumption
  have hsub : (caseCTailPlacements Γ).image f⊆adjacentPairs Γ := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_caseCTailPlacements Γ q).mp hq⟩
  calc
    _ = ((caseCTailPlacements Γ).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_of_subset hsub

theorem rankAverage_caseC_count_le (K : ℕ) (hKm : K≤m) :
    rankAverage K (fun Γ : Finset (Fin m)=>(caseCTailPlacements Γ).card)≤2*(K:ℝ) := by
  apply (rankAverage_mono K
    (fun Γ : Finset (Fin m)=>((caseCTailPlacements Γ).card:ℝ))
    (fun Γ : Finset (Fin m)=>((adjacentPairs Γ).card:ℝ))
    (fun Γ=>Nat.cast_le.mpr (caseCTailPlacements_card_le Γ))).trans
  exact rankAverage_adjacent_count_le hKm

theorem placementRankMean_caseC_le (e : Fin m ↪ Fin n) (q : Fin 2 ↪ Fin n)
    (K : ℕ) (hKm : K≤m) :
    placementRankMean e q caseCTailPlacements K≤caseCRate m K := by
  apply (placementRankMean_le e q caseCTailPlacements K).trans
  exact div_le_div_of_le (by positivity : (0:ℝ)≤m.descFactorial 2)
    (rankAverage_caseC_count_le K hKm)

noncomputable def caseAMean (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T) : ℝ :=
  rankAverage K (fun Γ=>((caseA T S Γ R).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))))
noncomputable def caseBMean (T S : Finset (Fin n)) (K : ℕ) (R : BRole T) : ℝ :=
  rankAverage K (fun Γ=>((caseB T S Γ R).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))))
noncomputable def caseCMean (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T) : ℝ :=
  rankAverage K (fun Γ=>((caseC T S Γ R).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin (Sampling.tailCount S))))

theorem caseAMean_le (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T)
    (hm : 4≤Sampling.tailCount S) (hKm : K<Sampling.tailCount S) :
    caseAMean T S K R≤caseARate (Sampling.tailCount S) K := by
  exact placementRankMean_caseA_le (Sampling.tail S) R.embedding K
    (lt_of_lt_of_le (by decide : 0<4) hm) hKm

theorem caseBMean_le (T S : Finset (Fin n)) (K : ℕ) (R : BRole T)
    (hm : 4≤Sampling.tailCount S) (hKm : K<Sampling.tailCount S) :
    caseBMean T S K R≤caseBRate (Sampling.tailCount S) K*
      (if R.selected∈S then (1:ℝ) else 0) := by
  classical
  by_cases hs : R.selected∈S
  · simp only [if_pos hs,mul_one]
    change rankAverage K (fun Γ=>((caseB T S Γ R).card:ℝ)/_)≤_
    simp only [caseB,if_pos hs]
    exact placementRankMean_caseB_le (Sampling.tail S) (firstThreeLabels R.embedding)
      K (lt_of_lt_of_le (by decide : 0<4) hm) hKm
  · simp only [caseBMean,caseB,if_neg hs,Finset.card_empty,Nat.cast_zero,zero_div,
      rankAverage_const,mul_zero,le_refl]

theorem caseCMean_le (T S : Finset (Fin n)) (K : ℕ) (R : ACRole T)
    (hm : 4≤Sampling.tailCount S) (hKm : K<Sampling.tailCount S) :
    caseCMean T S K R≤caseCRate (Sampling.tailCount S) K*
      (if R.other⊆S then (1:ℝ) else 0) := by
  classical
  by_cases hs : R.other⊆S
  · simp only [if_pos hs,mul_one]
    change rankAverage K (fun Γ=>((caseC T S Γ R).card:ℝ)/_)≤_
    simp only [caseC,if_pos hs]
    exact placementRankMean_caseC_le (Sampling.tail S) (firstTwoLabels R.embedding) K hKm.le
  · simp only [caseCMean,caseC,if_neg hs,Finset.card_empty,Nat.cast_zero,zero_div,
      rankAverage_const,mul_zero,le_refl]

#print axioms caseCTailPlacements_card_le
#print axioms placementRankMean_caseC_le
#print axioms caseAMean_le
#print axioms caseBMean_le
#print axioms caseCMean_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
