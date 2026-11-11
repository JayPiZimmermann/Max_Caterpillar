import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEventMembership
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventRankMoments

/-! # Actual support-bad probability with the full selected-arity dependence

The sample consists of a genuine full permutation of m+k original labels and
an independent genuine permutation of the m gap ranks. The literal A/B/C bad
event is already defined in Membership. Finite tuple counts, exact unordered
role counts and actual rank moments imply the bound; no bad-probability or
conditional uniformity conclusion is supplied as a hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
open BigOperators GoodEventPlacements
open MaxCaterpillar.Frontier.RandomRestriction.GoodEvent
  (ACRole BRole smallRankGaps rankAverage rankAverage_mono
   rankAverage_caseA_count_le rankAverage_caseB_count_le rankAverage_adjacent_count_le
   card_acRole_mul_four card_bRole_mul_two caseAPlacements caseBPlacements adjacentPairs)
variable {m : ℕ}

theorem roleEvents_card_mul_le {n : ℕ} {κ : Type*} [Fintype κ]
    (e : κ → (Fin 4 ↪ Fin n)) (B : Finset (Fin 4 ↪ Fin n)) :
    (roleEvents e B).card * n.descFactorial 4 ≤
      Fintype.card κ * B.card * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hc : (roleEvents e B).card ≤ ∑ r : κ, (UniformTuples.event (e r) B).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ (∑ r : κ, (UniformTuples.event (e r) B).card) * n.descFactorial 4 :=
      Nat.mul_le_mul_right _ hc
    _ = ∑ r : κ, (UniformTuples.event (e r) B).card * n.descFactorial 4 :=
      Finset.sum_mul
    _ = ∑ _r : κ, B.card * Fintype.card (Equiv.Perm (Fin n)) := by
      apply Finset.sum_congr rfl
      intro r _
      simpa only [UniformTuples.card_tuples] using UniformTuples.card_event_mul_tuple_card (e r) B
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem supportBadAt_card_mul_le (k : ℕ) (T : Finset (Fin (m+k))) (Γ : Finset (Fin m)) :
    (supportBadAt k T Γ).card * (m+k).descFactorial 4 ≤
      (Fintype.card (ACRole T) * (fullCaseA k Γ).card +
        Fintype.card (BRole T) * (fullCaseB k Γ).card +
        Fintype.card (ACRole T) * (fullCaseC k Γ).card) *
        Fintype.card (Equiv.Perm (Fin (m+k))) := by
  classical
  have hc : (supportBadAt k T Γ).card ≤
      (roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseA k Γ)).card +
      (roleEvents (fun r : BRole T => BRole.embedding r) (fullCaseB k Γ)).card +
      (roleEvents (fun r : ACRole T => ACRole.embedding r) (fullCaseC k Γ)).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hh := Nat.mul_le_mul_right ((m+k).descFactorial 4) hc
  have hA := roleEvents_card_mul_le (fun r : ACRole T => ACRole.embedding r) (fullCaseA k Γ)
  have hB := roleEvents_card_mul_le (fun r : BRole T => BRole.embedding r) (fullCaseB k Γ)
  have hC := roleEvents_card_mul_le (fun r : ACRole T => ACRole.embedding r) (fullCaseC k Γ)
  nlinarith only [hh, hA, hB, hC]

private theorem full_four_count_pos (k : ℕ) (hn : 4 ≤ m+k) :
    (0 : ℝ) < ((m+k).descFactorial 4 : ℝ) := by
  have hnz : (m+k).descFactorial 4 ≠ 0 := by
    intro hh
    exact (not_lt_of_ge hn) (Nat.descFactorial_eq_zero_iff_lt.mp hh)
  exact_mod_cast Nat.pos_of_ne_zero hnz

theorem supportBadAt_fraction_le (k : ℕ) (T : Finset (Fin (m+k)))
    (Γ : Finset (Fin m)) (hn : 4 ≤ m+k) :
    ((supportBadAt k T Γ).card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin (m+k))) : ℝ) ≤
      ((Fintype.card (ACRole T) : ℝ) * (fullCaseA k Γ).card +
        (Fintype.card (BRole T) : ℝ) * (fullCaseB k Γ).card +
        (Fintype.card (ACRole T) : ℝ) * (fullCaseC k Γ).card) /
        ((m+k).descFactorial 4 : ℝ) := by
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (m+k))) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_div_iff hP (full_four_count_pos k hn)).mpr
  exact_mod_cast supportBadAt_card_mul_le k T Γ

noncomputable def supportBadFraction (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ) : ℝ :=
  ((supportBadConfigurations k T K).card : ℝ) /
    (Fintype.card (Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) : ℝ)

theorem supportBadFraction_eq_rankAverage (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ) :
    supportBadFraction k T K = rankAverage K (fun Γ =>
      ((supportBadAt k T Γ).card : ℝ) / (Fintype.card (Equiv.Perm (Fin (m+k))) : ℝ)) := by
  classical
  have hc : ((supportBadConfigurations k T K).card : ℝ) =
      ∑ ρ : Equiv.Perm (Fin m), ((supportBadAt k T (smallRankGaps ρ K)).card : ℝ) := by
    rw [supportBadConfigurations, Finset.natCast_card_filter, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.sum_boole]
    change ((Finset.univ.filter (fun τ => τ ∈ supportBadAt k T (smallRankGaps ρ K))).card : ℝ) = _
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

private theorem rankAverage_scale (K : ℕ) (c : ℝ) (f : Finset (Fin m) → ℝ) :
    rankAverage K (fun Γ => c * f Γ) = c * rankAverage K f := by
  unfold rankAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

private theorem role_fraction_identity (a b R K m k d D : ℝ)
    (ha : 4*a=R) (hb : 2*b=R) :
    (a*(4*K^2/(1-K/m)) + b*(2*k*K^2/(m*(1-K/m))) + a*(2*d*K))/D =
      R/D * (K^2*(1+k/m)/(1-K/m)+d*K/2) := by
  have ha' : a=R/4 := by linarith only [ha]
  have hb' : b=R/2 := by linarith only [hb]
  rw [ha',hb']
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The exact selected-arity bad-support bound, for the genuine finite sample.
No selected-five scalar estimate or lower bound on K is required. -/
theorem supportBadFraction_le (k : ℕ) (T : Finset (Fin (m+k))) (K : ℕ)
    (hm : 0 < m) (hKm : K < m) (hn : 4 ≤ m+k) :
    supportBadFraction k T K ≤
      (T.card.descFactorial 4 : ℝ) / ((m+k).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1+(k : ℝ)/(m : ℝ)) / (1-(K : ℝ)/(m : ℝ)) +
          (k.descFactorial 2 : ℝ)*(K : ℝ)/2) := by
  have hD := full_four_count_pos k hn
  let a : ℝ := Fintype.card (ACRole T)
  let b : ℝ := Fintype.card (BRole T)
  let R : ℝ := T.card.descFactorial 4
  have ha : 4*a=R := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (card_acRole_mul_four T)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
  have hb : 2*b=R := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (card_bRole_mul_two T)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
  have hab : 0 ≤ a ∧ 0 ≤ b := ⟨Nat.cast_nonneg _,Nat.cast_nonneg _⟩
  have hfixed := rankAverage_mono K
    (fun Γ => ((supportBadAt k T Γ).card : ℝ) /
      (Fintype.card (Equiv.Perm (Fin (m+k))) : ℝ))
    (fun Γ => (a*((fullCaseA k Γ).card : ℝ) + b*((fullCaseB k Γ).card : ℝ) +
      a*((fullCaseC k Γ).card : ℝ)) / ((m+k).descFactorial 4 : ℝ))
    (fun Γ => supportBadAt_fraction_le k T Γ hn)
  rw [←supportBadFraction_eq_rankAverage] at hfixed
  have hA : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseA k Γ).card : ℝ)) ≤
      4*(K : ℝ)^2/(1-(K : ℝ)/m) := by
    exact (rankAverage_mono K _ _ (fun Γ => by exact_mod_cast fullCaseA_card_le k Γ)).trans
      (rankAverage_caseA_count_le hm hKm)
  have hB : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseB k Γ).card : ℝ)) ≤
      2*(k : ℝ)*(K : ℝ)^2/((m : ℝ)*(1-(K : ℝ)/m)) := by
    have h0 := rankAverage_mono K
      (fun Γ : Finset (Fin m) => ((fullCaseB k Γ).card : ℝ))
      (fun Γ : Finset (Fin m) => (k : ℝ)*((caseBPlacements Γ).card : ℝ))
      (fun Γ => by
        change ((fullCaseB k Γ).card : ℝ) ≤ (k : ℝ)*((caseBPlacements Γ).card : ℝ)
        exact_mod_cast fullCaseB_card_le k Γ)
    rw [rankAverage_scale] at h0
    have hh := mul_le_mul_of_nonneg_left (rankAverage_caseB_count_le hm hKm)
      (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    exact h0.trans (hh.trans_eq (by ring))
  have hC : rankAverage K (fun Γ : Finset (Fin m) => ((fullCaseC k Γ).card : ℝ)) ≤
      2*(k.descFactorial 2 : ℝ)*(K : ℝ) := by
    have h0 := rankAverage_mono K
      (fun Γ : Finset (Fin m) => ((fullCaseC k Γ).card : ℝ))
      (fun Γ : Finset (Fin m) => (k.descFactorial 2 : ℝ)*((adjacentPairs Γ).card : ℝ))
      (fun Γ => by
        change ((fullCaseC k Γ).card : ℝ) ≤
          (k.descFactorial 2 : ℝ)*((adjacentPairs Γ).card : ℝ)
        exact_mod_cast fullCaseC_card_le k Γ)
    rw [rankAverage_scale] at h0
    have hh := mul_le_mul_of_nonneg_left (rankAverage_adjacent_count_le hKm.le)
      (Nat.cast_nonneg (k.descFactorial 2) : (0 : ℝ) ≤ k.descFactorial 2)
    exact h0.trans (hh.trans_eq (by ring))
  rw [rankAverage_linear_three] at hfixed
  have hnum := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hA hab.1)
    (mul_le_mul_of_nonneg_left hB hab.2))
    (mul_le_mul_of_nonneg_left hC hab.1)
  have hprob := hfixed.trans (div_le_div_of_le hD.le hnum)
  exact hprob.trans_eq (role_fraction_identity a b R (K : ℝ) (m : ℝ)
    (k : ℝ) (k.descFactorial 2 : ℝ) _ ha hb)

variable {κ : Type*} [Fintype κ]

/-- Literal union over a finite family of original supports. -/
noncomputable def feedingBadConfigurations (k : ℕ)
    (T : κ → Finset (Fin (m+k))) (K : ℕ) :
    Finset (Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.biUnion fun j => supportBadConfigurations k (T j) K

noncomputable def feedingBadFraction (k : ℕ) (T : κ → Finset (Fin (m+k))) (K : ℕ) : ℝ :=
  ((feedingBadConfigurations k T K).card : ℝ) /
    (Fintype.card (Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) : ℝ)

/-- The actual family union is controlled by the sum of falling-four support
weights; no maximum-support or independent-event assumption is made. -/
theorem feedingBadFraction_le (k : ℕ) (T : κ → Finset (Fin (m+k))) (K : ℕ)
    (hm : 0 < m) (hKm : K < m) (hn : 4 ≤ m+k) :
    feedingBadFraction k T K ≤
      (∑ j, ((T j).card.descFactorial 4 : ℝ)) / ((m+k).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1+(k : ℝ)/(m : ℝ)) / (1-(K : ℝ)/(m : ℝ)) +
          (k.descFactorial 2 : ℝ)*(K : ℝ)/2) := by
  classical
  have hD : (0 : ℝ) <
      Fintype.card (Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) := by
    exact_mod_cast Fintype.card_pos
  have hc : ((feedingBadConfigurations k T K).card : ℝ) ≤
      ∑ j, ((supportBadConfigurations k (T j) K).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ)
      (t := fun j => supportBadConfigurations k (T j) K))
  unfold feedingBadFraction
  calc
    _ ≤ (∑ j, ((supportBadConfigurations k (T j) K).card : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) : ℝ) :=
      div_le_div_of_le hD.le hc
    _ = ∑ j, supportBadFraction k (T j) K := by
      rw [Finset.sum_div]
      rfl
    _ ≤ ∑ j, ((T j).card.descFactorial 4 : ℝ) / ((m+k).descFactorial 4 : ℝ) *
        ((K : ℝ)^2 * (1+(k : ℝ)/(m : ℝ)) / (1-(K : ℝ)/(m : ℝ)) +
          (k.descFactorial 2 : ℝ)*(K : ℝ)/2) :=
      Finset.sum_le_sum fun j _ => supportBadFraction_le k (T j) K hm hKm hn
    _ = _ := by rw [Finset.sum_div,Finset.sum_mul]

@[simp] theorem mem_feedingBadConfigurations (k : ℕ)
    (T : κ → Finset (Fin (m+k))) (K : ℕ)
    (p : Equiv.Perm (Fin (m+k)) × Equiv.Perm (Fin m)) :
    p ∈ feedingBadConfigurations k T K ↔ ∃ j, p ∈ supportBadConfigurations k (T j) K := by
  classical
  simp [feedingBadConfigurations]

#print axioms roleEvents_card_mul_le
#print axioms supportBadAt_card_mul_le
#print axioms supportBadAt_fraction_le
#print axioms supportBadFraction_eq_rankAverage
#print axioms supportBadFraction_le
#print axioms feedingBadFraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.GoodEvent
