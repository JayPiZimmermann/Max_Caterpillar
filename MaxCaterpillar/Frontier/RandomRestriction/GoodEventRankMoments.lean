import MaxCaterpillar.Frontier.RandomRestriction.GoodEventSubset
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventMoments

/-! # Actual uniform-rank run moments

The geometric-series hypotheses are supplied by the proved cardinal bound
for the literal event I subset smallRankGaps(rho,K), with rho uniform among
all permutations. No distributional conclusion is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {m K : ℕ}

noncomputable def rankAverage (K : ℕ) (f : Finset (Fin m) → ℝ) : ℝ :=
  ∑ ρ : Equiv.Perm (Fin m),
    (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) * f (smallRankGaps ρ K)

theorem rankAverage_const (K : ℕ) (c : ℝ) :
    rankAverage (m := m) K (fun _ => c) = c := by
  unfold rankAverage
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hc : (Fintype.card (Equiv.Perm (Fin m)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hc]
  <;> ring

theorem rankAverage_mono (K : ℕ) (f g : Finset (Fin m) → ℝ)
    (hfg : ∀ Γ, f Γ ≤ g Γ) : rankAverage K f ≤ rankAverage K g := by
  apply Finset.sum_le_sum
  intro ρ _
  exact mul_le_mul_of_nonneg_left (hfg _)
    (div_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem rank_containment_weight_le (hm : 0 < m) (hKm : K ≤ m)
    (I : Finset (Fin m)) :
    containmentWeight
      (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
      (fun ρ => smallRankGaps ρ K) I ≤ ((K : ℝ) / m) ^ I.card := by
  classical
  unfold containmentWeight
  rw [← Finset.mul_sum, Finset.sum_boole]
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact subset_smallRankGaps_fraction_le hm hKm I

/-- The expected number of tail positions in the anchor run. -/
theorem rankAverage_anchor_count_le (hm : 0 < m) (hKm : K < m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((anchoredRun Γ).card : ℝ)) ≤
      (K : ℝ) / ((m : ℝ) * (1 - (K : ℝ) / m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : (0 : ℝ) ≤ (K : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hmR.le
  have hqone : (K : ℝ) / m < 1 := (div_lt_one hmR).mpr (by exact_mod_cast hKm)
  have hh := weighted_anchor_count_le
    (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    (fun ρ => smallRankGaps ρ K) ((K : ℝ) / m) hq hqone
    (rank_containment_weight_le hm hKm.le)
  change rankAverage K (fun Γ : Finset (Fin m) => ((anchoredRun Γ).card : ℝ)) ≤ _ at hh
  simpa only [div_div] using hh

/-- The expected number of ordered distinct tail pairs in a common run. -/
theorem rankAverage_ordered_run_count_le (hm : 0 < m) (hKm : K < m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((orderedRunPairs Γ).card : ℝ)) ≤
      2 * (K : ℝ) / (1 - (K : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : (0 : ℝ) ≤ (K : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hmR.le
  have hqone : (K : ℝ) / m < 1 := (div_lt_one hmR).mpr (by exact_mod_cast hKm)
  have hh := weighted_ordered_run_count_le
    (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    (fun ρ => smallRankGaps ρ K) ((K : ℝ) / m) hq hqone
    (rank_containment_weight_le hm hKm.le)
  change rankAverage K (fun Γ : Finset (Fin m) => ((orderedRunPairs Γ).card : ℝ)) ≤ _ at hh
  convert hh using 1
  field_simp [hmR.ne', (sub_pos.mpr hqone).ne']
  <;> ring

/-- Fixed distinct four-role placements: the adjacent-pair count is bounded
pointwise before averaging the possibly dependent run-pair count. -/
theorem rankAverage_caseA_count_le (hm : 0 < m) (hKm : K < m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((caseAPlacements Γ).card : ℝ)) ≤
      4 * (K : ℝ) ^ 2 / (1 - (K : ℝ) / m) := by
  have hp : ∀ ρ : Equiv.Perm (Fin m),
      ((caseAPlacements (smallRankGaps ρ K)).card : ℝ) ≤
        2 * (K : ℝ) * ((orderedRunPairs (smallRankGaps ρ K)).card : ℝ) := by
    intro ρ
    have hh := caseAPlacements_card_le (smallRankGaps ρ K)
    rw [card_smallRankGaps hKm.le] at hh
    exact_mod_cast hh
  have hfirst : rankAverage K (fun Γ : Finset (Fin m) => ((caseAPlacements Γ).card : ℝ)) ≤
      2 * (K : ℝ) * rankAverage K (fun Γ : Finset (Fin m) => ((orderedRunPairs Γ).card : ℝ)) := by
    unfold rankAverage
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ _
    have hh := mul_le_mul_of_nonneg_left (hp ρ)
      (by positivity : (0 : ℝ) ≤ 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    nlinarith only [hh]
  calc
    _ ≤ _ := hfirst
    _ ≤ 2 * (K : ℝ) * (2 * (K : ℝ) / (1 - (K : ℝ) / m)) :=
      mul_le_mul_of_nonneg_left (rankAverage_ordered_run_count_le hm hKm) (by positivity)
    _ = _ := by ring

/-- Fixed distinct three-tail-role placements with the third role in the
anchor run. The fourth support role is selected later in the global model. -/
theorem rankAverage_caseB_count_le (hm : 0 < m) (hKm : K < m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((caseBPlacements Γ).card : ℝ)) ≤
      2 * (K : ℝ) ^ 2 / ((m : ℝ) * (1 - (K : ℝ) / m)) := by
  have hp : ∀ ρ : Equiv.Perm (Fin m),
      ((caseBPlacements (smallRankGaps ρ K)).card : ℝ) ≤
        2 * (K : ℝ) * ((anchoredRun (smallRankGaps ρ K)).card : ℝ) := by
    intro ρ
    have hh := caseBPlacements_card_le (smallRankGaps ρ K)
    rw [card_smallRankGaps hKm.le] at hh
    exact_mod_cast hh
  have hfirst : rankAverage K (fun Γ : Finset (Fin m) => ((caseBPlacements Γ).card : ℝ)) ≤
      2 * (K : ℝ) * rankAverage K (fun Γ : Finset (Fin m) => ((anchoredRun Γ).card : ℝ)) := by
    unfold rankAverage
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ _
    have hh := mul_le_mul_of_nonneg_left (hp ρ)
      (by positivity : (0 : ℝ) ≤ 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    nlinarith only [hh]
  calc
    _ ≤ _ := hfirst
    _ ≤ 2 * (K : ℝ) * ((K : ℝ) / ((m : ℝ) * (1 - (K : ℝ) / m))) :=
      mul_le_mul_of_nonneg_left (rankAverage_anchor_count_le hm hKm) (by positivity)
    _ = _ := by ring

theorem rankAverage_adjacent_count_le (hKm : K ≤ m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((adjacentPairs Γ).card : ℝ)) ≤ 2 * (K : ℝ) := by
  have hp : ∀ ρ : Equiv.Perm (Fin m),
      ((adjacentPairs (smallRankGaps ρ K)).card : ℝ) ≤ 2 * (K : ℝ) := by
    intro ρ
    have hh := adjacentPairs_card_le (smallRankGaps ρ K)
    rw [card_smallRankGaps hKm] at hh
    exact_mod_cast hh
  unfold rankAverage
  calc
    _ ≤ ∑ ρ : Equiv.Perm (Fin m),
        (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) * (2 * (K : ℝ)) :=
      Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hp ρ) (by positivity)
    _ = _ := rankAverage_const K (2 * (K : ℝ))

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
