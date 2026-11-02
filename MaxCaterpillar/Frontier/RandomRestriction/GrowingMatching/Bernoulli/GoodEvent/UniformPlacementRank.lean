import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.UniformPlacement
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent.Rates
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventRankMoments

/-! # Actual rank averages of original-label tail placements -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
open BigOperators
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
variable {n m d : ℕ}

/-- The literal uniform-tail fraction averaged over the literal uniform rank
permutation, with no product-law or genericity hypothesis. -/
noncomputable def placementRankMean (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin m)→Finset (Fin d ↪ Fin m)) (K : ℕ) : ℝ :=
  rankAverage K (fun Γ=>((placementEvent e q (B Γ)).card:ℝ)/
    Fintype.card (Equiv.Perm (Fin m)))

lemma rankAverage_div (K : ℕ) (f : Finset (Fin m)→ℝ) (a : ℝ) :
    rankAverage K (fun Γ=>f Γ/a)=rankAverage K f/a := by
  unfold rankAverage
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem placementRankMean_le (e : Fin m ↪ Fin n) (q : Fin d ↪ Fin n)
    (B : Finset (Fin m)→Finset (Fin d ↪ Fin m)) (K : ℕ) :
    placementRankMean e q B K ≤
      rankAverage K (fun Γ=>((B Γ).card:ℝ))/(m.descFactorial d:ℝ) := by
  unfold placementRankMean
  calc
    _ ≤ rankAverage K (fun Γ=>(B Γ).card/(m.descFactorial d:ℝ)) :=
      rankAverage_mono K _ _ (fun Γ=>placementEvent_fraction_le e q (B Γ))
    _ = _ := rankAverage_div K _ _

theorem placementRankMean_caseA_le (e : Fin m ↪ Fin n) (q : Fin 4 ↪ Fin n)
    (K : ℕ) (hm : 0<m) (hKm : K<m) :
    placementRankMean e q caseAPlacements K≤caseARate m K := by
  apply (placementRankMean_le e q caseAPlacements K).trans
  have h := div_le_div_of_le (by positivity : (0:ℝ)≤m.descFactorial 4)
    (rankAverage_caseA_count_le hm hKm)
  convert h using 1 <;> unfold caseARate <;> rw [div_div]

theorem placementRankMean_caseB_le (e : Fin m ↪ Fin n) (q : Fin 3 ↪ Fin n)
    (K : ℕ) (hm : 0<m) (hKm : K<m) :
    placementRankMean e q caseBPlacements K≤caseBRate m K := by
  apply (placementRankMean_le e q caseBPlacements K).trans
  have h := div_le_div_of_le (by positivity : (0:ℝ)≤m.descFactorial 3)
    (rankAverage_caseB_count_le hm hKm)
  convert h using 1 <;> unfold caseBRate <;> rw [div_div]

#print axioms placementRankMean_le
#print axioms placementRankMean_caseA_le
#print axioms placementRankMean_caseB_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.GoodEvent
