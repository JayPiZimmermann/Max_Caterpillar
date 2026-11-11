import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesProbability

/-! Remove the small-K rounding loss in the literal isolated-gap bad-event bound. -/
set_option autoImplicit false
namespace MaxCaterpillar.OvernightConstants
open BigOperators Frontier.RandomRestriction Frontier.RandomRestriction.GoodEvent
variable {m K : ℕ}

theorem badIsolated_forces_adjacencies (hKm : K ≤ m) (hK : 82 ≤ K)
    (ρ : Equiv.Perm (Fin m)) (hρ : ρ ∈ badIsolatedEvent m K) :
    (10/41:ℝ)*(K : ℝ) ≤ ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
  have hc := card_le_isolated_add_one_add_two_adjacent (smallRankGaps ρ K)
  rw [card_smallRankGaps hKm] at hc
  have hcR : (K : ℝ) ≤ ((isolatedGaps (smallRankGaps ρ K)).card : ℝ) + 1 +
      2 * ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by exact_mod_cast hc
  have hKR : (82 : ℝ) ≤ K := by exact_mod_cast hK
  have hbad := (mem_badIsolatedEvent ρ).mp hρ
  linarith only [hcR,hKR,hbad]

/-- Actual finite rank permutations, no independence hypothesis. -/
theorem badIsolated_fraction_le (hm : 0 < m) (hKm : K ≤ m) (hK : 82 ≤ K) :
    ((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m)) ≤
      (41/10:ℝ) * (K : ℝ) / m := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hKpos : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 82) hK
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin m)⟩
  have hsum : ((badIsolatedEvent m K).card : ℝ) * ((10/41:ℝ) * (K : ℝ)) ≤
      ∑ ρ : Equiv.Perm (Fin m),
        ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
    calc
      ((badIsolatedEvent m K).card : ℝ) * ((10/41:ℝ) * (K : ℝ)) =
          ∑ _ρ in badIsolatedEvent m K, (10/41:ℝ) * (K : ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ ρ in badIsolatedEvent m K,
          ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact badIsolated_forces_adjacencies hKm hK ρ hρ
      _ ≤ ∑ ρ : Equiv.Perm (Fin m),
          ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro ρ _ _
        exact Nat.cast_nonneg _
  have hmark :
      (((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m))) *
        ((10/41:ℝ) * (K : ℝ)) ≤
      rankAverage K (fun Γ : Finset (Fin m) => ((selectedGapAdjacencies Γ).card : ℝ)) := by
    unfold rankAverage
    rw [← Finset.mul_sum]
    calc
      (((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m))) *
          ((10/41:ℝ) * (K : ℝ)) =
          (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) *
            (((badIsolatedEvent m K).card : ℝ) * ((10/41:ℝ) * (K : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hP.le)
  apply (mul_le_mul_right (mul_pos (by norm_num : (0:ℝ)<10/41) hKpos)).mp
  calc
    _ ≤ (K : ℝ) ^ 2 / m := hmark.trans (rankAverage_selectedGapAdjacencies_le hm hKm)
    _ = ((41/10:ℝ) * (K : ℝ) / m) * ((10/41:ℝ) * (K : ℝ)) := by ring

#print axioms badIsolated_forces_adjacencies
#print axioms badIsolated_fraction_le
end MaxCaterpillar.OvernightConstants
