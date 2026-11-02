import MaxCaterpillar.Frontier.RandomRestriction.GoodEventCherriesGeometry
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventRankMoments

/-! # Actual rank-permutation bounds for isolated low-rank cherry gaps

Two requested adjacent gaps are bounded through the proved rank inclusion
law. The bad-event probability then follows from the literal finite sum,
with no independence or distributional hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators
variable {m K : ℕ}

/-- Each possible adjacency is determined by its first gap. -/
theorem allGapAdjacencies_card_le : (allGapAdjacencies (m := m)).card ≤ m := by
  classical
  have hinj : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m)
      (↑(allGapAdjacencies (m := m)) : Set (Fin m × Fin m)) := by
    intro p hp q hq hfirst
    apply Prod.ext hfirst
    apply Fin.ext
    have hp' := (mem_allGapAdjacencies p.1 p.2).mp hp
    have hq' := (mem_allGapAdjacencies q.1 q.2).mp hq
    calc
      p.2.val = p.1.val + 1 := hp'.symm
      _ = q.1.val + 1 := congrArg (fun x : Fin m => x.val + 1) hfirst
      _ = q.2.val := hq'
  calc
    (allGapAdjacencies (m := m)).card =
        (allGapAdjacencies.image (Prod.fst : Fin m × Fin m → Fin m)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_of_subset (Finset.subset_univ _)
    _ = m := by simp

/-- A selected adjacency requests exactly its two distinct gap labels. -/
theorem weighted_selectedGapAdjacencies_count_eq {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (Γ : Ω → Finset (Fin m)) :
    (∑ ω, p ω * ((selectedGapAdjacencies (Γ ω)).card : ℝ)) =
      ∑ e in allGapAdjacencies, containmentWeight p Γ {e.1,e.2} := by
  classical
  simp only [selectedGapAdjacencies,Finset.natCast_card_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  unfold containmentWeight
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]

/-- Uniform actual ranks have expected selected-adjacency count at most K²/m. -/
theorem rankAverage_selectedGapAdjacencies_le (hm : 0 < m) (hKm : K ≤ m) :
    rankAverage K (fun Γ : Finset (Fin m) => ((selectedGapAdjacencies Γ).card : ℝ)) ≤
      (K : ℝ) ^ 2 / m := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  change (∑ ρ : Equiv.Perm (Fin m),
    (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) *
      ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ)) ≤ _
  rw [weighted_selectedGapAdjacencies_count_eq]
  calc
    (∑ e in allGapAdjacencies, containmentWeight
        (fun _ : Equiv.Perm (Fin m) => 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
        (fun ρ => smallRankGaps ρ K) {e.1,e.2}) ≤
        ∑ _e in allGapAdjacencies (m := m), ((K : ℝ) / m) ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      have hadj := (mem_allGapAdjacencies e.1 e.2).mp he
      have hlt : e.1.val < e.2.val := by rw [← hadj]; exact Nat.lt_succ_self _
      have hne : e.1 ≠ e.2 := fun h => (ne_of_lt hlt) (congrArg Fin.val h)
      have hpair : ({e.1,e.2} : Finset (Fin m)).card = 2 := by simp [hne]
      simpa only [hpair] using rank_containment_weight_le hm hKm {e.1,e.2}
    _ = ((allGapAdjacencies (m := m)).card : ℝ) * ((K : ℝ) / m) ^ 2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (m : ℝ) * ((K : ℝ) / m) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast allGapAdjacencies_card_le (m := m)
    _ = (K : ℝ) ^ 2 / m := by field_simp [hmR.ne'] <;> ring

/-- The actual rank permutations with fewer than K/2 isolated nonanchor gaps. -/
noncomputable def badIsolatedEvent (m K : ℕ) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun ρ =>
    ((isolatedGaps (smallRankGaps ρ K)).card : ℝ) < (K : ℝ) / 2

@[simp] theorem mem_badIsolatedEvent (ρ : Equiv.Perm (Fin m)) :
    ρ ∈ badIsolatedEvent m K ↔
      ((isolatedGaps (smallRankGaps ρ K)).card : ℝ) < (K : ℝ) / 2 := by
  classical
  simp only [badIsolatedEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Bad isolated-gap count forces a selected adjacency count of at least K/8. -/
theorem badIsolatedEvent_forces_adjacencies (hKm : K ≤ m) (hK : 4 ≤ K)
    (ρ : Equiv.Perm (Fin m)) (hρ : ρ ∈ badIsolatedEvent m K) :
    (K : ℝ) / 8 ≤ ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
  have hc := card_le_isolated_add_one_add_two_adjacent (smallRankGaps ρ K)
  rw [card_smallRankGaps hKm] at hc
  have hcR : (K : ℝ) ≤ ((isolatedGaps (smallRankGaps ρ K)).card : ℝ) + 1 +
      2 * ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by exact_mod_cast hc
  have hKR : (4 : ℝ) ≤ K := by exact_mod_cast hK
  have hbad := (mem_badIsolatedEvent ρ).mp hρ
  linarith only [hcR,hKR,hbad]

/-- Markov's bound, proved as a count over the literal finite permutation event. -/
theorem badIsolatedEvent_fraction_le (hm : 0 < m) (hKm : K ≤ m) (hK : 4 ≤ K) :
    ((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m)) ≤
      8 * (K : ℝ) / m := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hKpos : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) hK
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin m)⟩
  have hsum : ((badIsolatedEvent m K).card : ℝ) * ((K : ℝ) / 8) ≤
      ∑ ρ : Equiv.Perm (Fin m),
        ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
    calc
      ((badIsolatedEvent m K).card : ℝ) * ((K : ℝ) / 8) =
          ∑ _ρ in badIsolatedEvent m K, (K : ℝ) / 8 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ ρ in badIsolatedEvent m K,
          ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact badIsolatedEvent_forces_adjacencies hKm hK ρ hρ
      _ ≤ ∑ ρ : Equiv.Perm (Fin m),
          ((selectedGapAdjacencies (smallRankGaps ρ K)).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro ρ _ _
        exact Nat.cast_nonneg _
  have hmark :
      (((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m))) *
        ((K : ℝ) / 8) ≤
      rankAverage K (fun Γ : Finset (Fin m) => ((selectedGapAdjacencies Γ).card : ℝ)) := by
    unfold rankAverage
    rw [← Finset.mul_sum]
    calc
      (((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m))) *
          ((K : ℝ) / 8) =
          (1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ)) *
            (((badIsolatedEvent m K).card : ℝ) * ((K : ℝ) / 8)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hP.le)
  apply (mul_le_mul_right (div_pos hKpos (by norm_num : (0 : ℝ) < 8))).mp
  calc
    _ ≤ (K : ℝ) ^ 2 / m := hmark.trans (rankAverage_selectedGapAdjacencies_le hm hKm)
    _ = (8 * (K : ℝ) / m) * ((K : ℝ) / 8) := by field_simp [hmR.ne'] <;> ring

/-- The stated eight-percent bound in the low-rank regime. -/
theorem badIsolatedEvent_fraction_le_eight_percent
    (hm : 0 < m) (hKm : K ≤ m) (hK : 4 ≤ K) (hsmall : 100 * K ≤ m) :
    ((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m)) ≤
      (8 / 100 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsmallR : (100 : ℝ) * K ≤ m := by exact_mod_cast hsmall
  apply (badIsolatedEvent_fraction_le hm hKm hK).trans
  apply (div_le_iff hmR).mpr
  nlinarith only [hsmallR]

/-- Integer division version of the low-rank condition. -/
theorem badIsolatedEvent_fraction_le_eight_percent_of_div
    (hm : 0 < m) (hKm : K ≤ m) (hK : 4 ≤ K) (hsmall : K ≤ m / 100) :
    ((badIsolatedEvent m K).card : ℝ) / Fintype.card (Equiv.Perm (Fin m)) ≤
      (8 / 100 : ℝ) := by
  apply badIsolatedEvent_fraction_le_eight_percent hm hKm hK
  have hh := (Nat.le_div_iff_mul_le (by decide : 0 < 100)).mp hsmall
  simpa only [Nat.mul_comm] using hh

#print axioms rankAverage_selectedGapAdjacencies_le
#print axioms badIsolatedEvent_fraction_le
#print axioms badIsolatedEvent_fraction_le_eight_percent_of_div
end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
