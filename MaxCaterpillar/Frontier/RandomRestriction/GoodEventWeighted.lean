import MaxCaterpillar.Frontier.RandomRestriction.GoodEventProbability

/-! # Weighted good-event bound for an actual finite family of supports

This is the finite union of concrete A/B/C configuration events, sampled by
one full permutation and one gap-rank permutation. The weight is falling4,
not a largest-support-size assumption.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {m : ℕ} {κ : Type*} [Fintype κ]

noncomputable def feedingBadConfigurations (T : κ → Finset (Fin (m + 5))) (K : ℕ) :
    Finset (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.biUnion fun j => supportBadConfigurations (T j) K

noncomputable def feedingBadFraction (T : κ → Finset (Fin (m + 5))) (K : ℕ) : ℝ :=
  ((feedingBadConfigurations T K).card : ℝ) /
    (Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) : ℝ)

theorem feedingBadFraction_le (T : κ → Finset (Fin (m + 5))) (K : ℕ)
    (hm : 400 ≤ m) (hKlow : 4 ≤ K) (hKhigh : (K : ℝ) ≤ (m : ℝ) / 100) :
    feedingBadFraction T K ≤
      4 * (∑ j, (T j).card.descFactorial 4 : ℝ) * (K : ℝ) ^ 2 / (m : ℝ) ^ 4 := by
  classical
  have hD : (0 : ℝ) <
      Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos
  have hc : ((feedingBadConfigurations T K).card : ℝ) ≤
      ∑ j, ((supportBadConfigurations (T j) K).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ)
      (t := fun j => supportBadConfigurations (T j) K))
  unfold feedingBadFraction
  calc
    _ ≤ (∑ j, ((supportBadConfigurations (T j) K).card : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) : ℝ) :=
      div_le_div_of_le hD.le hc
    _ = ∑ j, supportBadFraction (T j) K := by
      rw [Finset.sum_div]
      rfl
    _ ≤ ∑ j, 4 * ((T j).card.descFactorial 4 : ℝ) * (K : ℝ) ^ 2 / (m : ℝ) ^ 4 :=
      Finset.sum_le_sum fun j _ => supportBadFraction_le (T j) K hm hKlow hKhigh
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]

/-- Integer form for the eventual finite configuration-space union bound. -/
theorem feedingBadConfigurations_card_mul (T : κ → Finset (Fin (m + 5))) (K : ℕ)
    (hm : 400 ≤ m) (hKlow : 4 ≤ K) (hKhigh : (K : ℝ) ≤ (m : ℝ) / 100) :
    (feedingBadConfigurations T K).card * m ^ 4 ≤
      4 * (∑ j, (T j).card.descFactorial 4) * K ^ 2 *
        Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) := by
  have hD : (0 : ℝ) <
      Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm : 0 < m)
  have hh := feedingBadFraction_le T K hm hKlow hKhigh
  have hc := (div_le_div_iff hD (pow_pos hmR 4)).mp hh
  exact_mod_cast hc

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
