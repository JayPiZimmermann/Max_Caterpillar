import MaxCaterpillar.Frontier.RandomRestriction.GoodEventRankMoments
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventConstants
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesFiveTail
import MaxCaterpillar.Frontier.RandomRestriction.UniformTuplesRoles

/-! # Actual finite support bad events on full permutations and gap ranks

All three cases share one actual full permutation of m+5 labels. Its first
five positions are selected, and the rest form the tail. Role spaces contain
unordered support pairs; their fixed embeddings introduce no extra factor.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
open BigOperators

variable {m : ℕ}

noncomputable def roleEvents {κ : Type*} [Fintype κ]
    (e : κ → (Fin 4 ↪ Fin (m + 5))) (B : Finset (Fin 4 ↪ Fin (m + 5))) :
    Finset (Equiv.Perm (Fin (m + 5))) := by
  classical
  exact Finset.univ.biUnion fun r => UniformTuples.event (e r) B

theorem roleEvents_card_mul_le {κ : Type*} [Fintype κ]
    (e : κ → (Fin 4 ↪ Fin (m + 5))) (B : Finset (Fin 4 ↪ Fin (m + 5))) :
    (roleEvents e B).card * (m + 5).descFactorial 4 ≤
      Fintype.card κ * B.card * Fintype.card (Equiv.Perm (Fin (m + 5))) := by
  classical
  have hc : (roleEvents e B).card ≤ ∑ r : κ, (UniformTuples.event (e r) B).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ (∑ r : κ, (UniformTuples.event (e r) B).card) * (m + 5).descFactorial 4 :=
      Nat.mul_le_mul_right _ hc
    _ = ∑ r : κ, (UniformTuples.event (e r) B).card * (m + 5).descFactorial 4 :=
      Finset.sum_mul
    _ = ∑ _r : κ, B.card * Fintype.card (Equiv.Perm (Fin (m + 5))) := by
      apply Finset.sum_congr rfl
      intro r _
      simpa only [UniformTuples.card_tuples] using UniformTuples.card_event_mul_tuple_card (e r) B
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The literal union of the three support-witness events from the cost
argument. Every witness uses four distinct labels of the actual support. -/
noncomputable def supportBadAt (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m)) :
    Finset (Equiv.Perm (Fin (m + 5))) :=
  (roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseA Γ) ∪
    roleEvents (fun r : BRole T => BRole.embedding r) (fullCaseB Γ)) ∪
    roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseC Γ)

theorem supportBadAt_card_mul_le (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m)) :
    (supportBadAt T Γ).card * (m + 5).descFactorial 4 ≤
      (Fintype.card (ACRole T) * (fullCaseA Γ).card +
        Fintype.card (BRole T) * (fullCaseB Γ).card +
        Fintype.card (ACRole T) * (fullCaseC Γ).card) *
        Fintype.card (Equiv.Perm (Fin (m + 5))) := by
  classical
  have hc : (supportBadAt T Γ).card ≤
      (roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseA Γ)).card +
      (roleEvents (fun r : BRole T => BRole.embedding r) (fullCaseB Γ)).card +
      (roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseC Γ)).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hh := Nat.mul_le_mul_right ((m + 5).descFactorial 4) hc
  have hA := roleEvents_card_mul_le (fun r : ACRole T => ACRole.embedding r) (fullCaseA Γ)
  have hB := roleEvents_card_mul_le (fun r : BRole T => BRole.embedding r) (fullCaseB Γ)
  have hC := roleEvents_card_mul_le (fun r : ACRole T => ACRole.embedding r) (fullCaseC Γ)
  nlinarith only [hh, hA, hB, hC]

theorem supportBadAt_fraction_le (T : Finset (Fin (m + 5))) (Γ : Finset (Fin m)) :
    ((supportBadAt T Γ).card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin (m + 5))) : ℝ) ≤
      ((Fintype.card (ACRole T) : ℝ) * (fullCaseA Γ).card +
        (Fintype.card (BRole T) : ℝ) * (fullCaseB Γ).card +
        (Fintype.card (ACRole T) : ℝ) * (fullCaseC Γ).card) /
        ((m + 5).descFactorial 4 : ℝ) := by
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (m + 5))) := by
    exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < ((m + 5).descFactorial 4 : ℝ) := by
    rw [fifth_prefix_descFactorial_four]
    positivity
  apply (div_le_div_iff hP hD).mpr
  exact_mod_cast supportBadAt_card_mul_le T Γ

noncomputable def supportBadConfigurations (T : Finset (Fin (m + 5))) (K : ℕ) :
    Finset (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter fun p => p.1 ∈ supportBadAt T (smallRankGaps p.2 K)

noncomputable def supportBadFraction (T : Finset (Fin (m + 5))) (K : ℕ) : ℝ :=
  ((supportBadConfigurations T K).card : ℝ) /
    (Fintype.card (Equiv.Perm (Fin (m + 5)) × Equiv.Perm (Fin m)) : ℝ)

theorem supportBadFraction_eq_rankAverage (T : Finset (Fin (m + 5))) (K : ℕ) :
    supportBadFraction T K = rankAverage K (fun Γ =>
      ((supportBadAt T Γ).card : ℝ) / (Fintype.card (Equiv.Perm (Fin (m + 5))) : ℝ)) := by
  classical
  have hc : ((supportBadConfigurations T K).card : ℝ) =
      ∑ ρ : Equiv.Perm (Fin m), ((supportBadAt T (smallRankGaps ρ K)).card : ℝ) := by
    rw [supportBadConfigurations, Finset.natCast_card_filter, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.sum_boole]
    change ((Finset.univ.filter (fun τ => τ ∈ supportBadAt T (smallRankGaps ρ K))).card : ℝ) = _
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold supportBadFraction rankAverage
  rw [hc, Fintype.card_prod, Nat.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

private theorem rankAverage_linear_three (K : ℕ) (a b c D : ℝ)
    (f g h : Finset (Fin m) → ℝ) :
    rankAverage K (fun Γ => (a * f Γ + b * g Γ + c * h Γ) / D) =
      (a * rankAverage K f + b * rankAverage K g + c * rankAverage K h) / D := by
  unfold rankAverage
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, add_div, add_div,
    Finset.sum_div, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

private theorem role_fraction_identity (a b R k u D : ℝ)
    (ha : 4 * a = R) (hb : 2 * b = R) :
    (a * (4 * k^2 / (1-k/u)) + b * (10*k^2/(u*(1-k/u))) + a*(40*k))/D =
      R / D * (k^2*(1+5/u)/(1-k/u)+10*k) := by
  have ha' : a = R / 4 := by linarith only [ha]
  have hb' : b = R / 2 := by linarith only [hb]
  rw [ha', hb']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Actual full-permutation/rank bad-support probability. All finite tuple
and rank distribution inputs have been proved from their actual samples. -/
theorem supportBadFraction_le (T : Finset (Fin (m + 5))) (K : ℕ)
    (hm : 400 ≤ m) (hKlow : 4 ≤ K) (hKhigh : (K : ℝ) ≤ (m : ℝ) / 100) :
    supportBadFraction T K ≤
      4 * (T.card.descFactorial 4 : ℝ) * (K : ℝ) ^ 2 / (m : ℝ) ^ 4 := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hmR : (400 : ℝ) ≤ m := by exact_mod_cast hm
  have hKlt : K < m := by
    have hh : (K : ℝ) < m := by linarith only [hKhigh, hmR]
    exact_mod_cast hh
  have hD : (0 : ℝ) < ((m + 5).descFactorial 4 : ℝ) := by
    rw [fifth_prefix_descFactorial_four]
    positivity
  let a : ℝ := Fintype.card (ACRole T)
  let b : ℝ := Fintype.card (BRole T)
  let R : ℝ := T.card.descFactorial 4
  have ha : 4 * a = R := by
    change (4 : ℝ) * (Fintype.card (ACRole T) : ℝ) = (T.card.descFactorial 4 : ℝ)
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (card_acRole_mul_four T)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hh
  have hb : 2 * b = R := by
    change (2 : ℝ) * (Fintype.card (BRole T) : ℝ) = (T.card.descFactorial 4 : ℝ)
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (card_bRole_mul_two T)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hh
  have hab : 0 ≤ a ∧ 0 ≤ b := ⟨Nat.cast_nonneg _, Nat.cast_nonneg _⟩
  have hfixed := rankAverage_mono K
    (fun Γ => ((supportBadAt T Γ).card : ℝ) /
      (Fintype.card (Equiv.Perm (Fin (m + 5))) : ℝ))
    (fun Γ => (a * ((fullCaseA Γ).card : ℝ) + b * ((fullCaseB Γ).card : ℝ) +
      a * ((fullCaseC Γ).card : ℝ)) / ((m + 5).descFactorial 4 : ℝ))
    (supportBadAt_fraction_le T)
  rw [← supportBadFraction_eq_rankAverage] at hfixed
  have hfullA : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseA Γ).card : ℝ)) ≤
      4 * (K : ℝ) ^ 2 / (1 - (K : ℝ) / m) := by
    exact (rankAverage_mono K _ _ (fun Γ => by exact_mod_cast fullCaseA_card_le Γ)).trans
      (rankAverage_caseA_count_le hmpos hKlt)
  have hfullB : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseB Γ).card : ℝ)) ≤
      10 * (K : ℝ) ^ 2 / ((m : ℝ) * (1 - (K : ℝ) / m)) := by
    have h0 := rankAverage_mono K
      (fun Γ : Finset (Fin m) => ((fullCaseB Γ).card : ℝ))
      (fun Γ : Finset (Fin m) => 5 * ((caseBPlacements Γ).card : ℝ))
      (fun Γ => by
        change ((fullCaseB Γ).card : ℝ) ≤ 5 * ((caseBPlacements Γ).card : ℝ)
        exact_mod_cast fullCaseB_card_le Γ)
    have heq : rankAverage K (fun Γ : Finset (Fin m) => 5 * ((caseBPlacements Γ).card : ℝ)) =
        5 * rankAverage K (fun Γ : Finset (Fin m) => ((caseBPlacements Γ).card : ℝ)) := by
      unfold rankAverage
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    rw [heq] at h0
    have hh := mul_le_mul_of_nonneg_left (rankAverage_caseB_count_le hmpos hKlt)
      (by norm_num : (0 : ℝ) ≤ 5)
    exact h0.trans (hh.trans_eq (by ring))
  have hfullC : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseC Γ).card : ℝ)) ≤
      40 * (K : ℝ) := by
    have h0 := rankAverage_mono K
      (fun Γ : Finset (Fin m) => ((fullCaseC Γ).card : ℝ))
      (fun Γ : Finset (Fin m) => 20 * ((adjacentPairs Γ).card : ℝ))
      (fun Γ => by
        change ((fullCaseC Γ).card : ℝ) ≤ 20 * ((adjacentPairs Γ).card : ℝ)
        exact_mod_cast fullCaseC_card_le Γ)
    have heq : rankAverage K (fun Γ : Finset (Fin m) => 20 * ((adjacentPairs Γ).card : ℝ)) =
        20 * rankAverage K (fun Γ : Finset (Fin m) => ((adjacentPairs Γ).card : ℝ)) := by
      unfold rankAverage
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    rw [heq] at h0
    have hh := mul_le_mul_of_nonneg_left (rankAverage_adjacent_count_le hKlt.le)
      (by norm_num : (0 : ℝ) ≤ 20)
    nlinarith only [h0, hh]
  rw [rankAverage_linear_three] at hfixed
  have hnum := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hfullA hab.1)
    (mul_le_mul_of_nonneg_left hfullB hab.2))
    (mul_le_mul_of_nonneg_left hfullC hab.1)
  have hprob := hfixed.trans (div_le_div_of_le hD.le hnum)
  have heq : (a * (4 * (K : ℝ)^2 / (1 - (K : ℝ)/m)) +
      b * (10 * (K : ℝ)^2 / ((m : ℝ)*(1 - (K : ℝ)/m))) + a * (40*(K : ℝ))) /
      ((m+5).descFactorial 4 : ℝ) =
      R / ((m+5).descFactorial 4 : ℝ) *
        ((K : ℝ)^2*(1+5/(m : ℝ))/(1-(K : ℝ)/m)+10*(K : ℝ)) := by
    exact role_fraction_identity a b R (K : ℝ) (m : ℝ) _ ha hb
  rw [heq] at hprob
  exact hprob.trans (full_permutation_good_event_scalar_le m (K : ℝ) R hm
    (by exact_mod_cast hKlow) hKhigh (Nat.cast_nonneg _))

end MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
