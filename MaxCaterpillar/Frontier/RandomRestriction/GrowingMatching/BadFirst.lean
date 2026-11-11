import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Selected

/-! # Actual first exceptional event at arbitrary selected arity

Every original support of size at least three contributes at most one
three-label containment bound. No sum over all triples, maximum support
size, or probability-law assumption is used.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
open BigOperators
variable {n k : ℕ} {κ : Type*} [Fintype κ]

noncomputable def largeSupportRows (T : κ → Finset (Fin n)) : Finset κ := by
  classical
  exact Finset.univ.filter (fun j => 3 ≤ (T j).card)

noncomputable def largeSupportCount (T : κ → Finset (Fin n)) : ℕ :=
  (largeSupportRows T).card

/-- Full permutations map labels to positions; the first k positions select
exactly GoodEvent.smallRankGaps sigma k. -/
noncomputable def badFirstEvent (k : ℕ) (T : κ → Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun σ =>
    ∃ j, 3 ≤ (T j).card ∧ T j ⊆ GoodEvent.smallRankGaps σ k)

@[simp] theorem mem_largeSupportRows (T : κ → Finset (Fin n)) (j : κ) :
    j ∈ largeSupportRows T ↔ 3 ≤ (T j).card := by
  classical
  simp only [largeSupportRows,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_badFirstEvent (k : ℕ) (T : κ → Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ badFirstEvent k T ↔
      ∃ j, 3 ≤ (T j).card ∧ T j ⊆ GoodEvent.smallRankGaps σ k := by
  classical
  simp only [badFirstEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Choose one actual three-element subset of this support, not all triples. -/
theorem support_containment_card_mul_le (hkn : k ≤ n) (T : Finset (Fin n))
    (hT : 3 ≤ T.card) :
    (GoodEvent.containmentEvent k T).card * n.descFactorial 3 ≤
      k.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  obtain ⟨I,hIT,hcard⟩ := Finset.exists_smaller_set T 3 hT
  have hsub : GoodEvent.containmentEvent k T ⊆ GoodEvent.containmentEvent k I := by
    intro σ hσ
    exact (GoodEvent.mem_containmentEvent I σ).mpr
      (hIT.trans ((GoodEvent.mem_containmentEvent T σ).mp hσ))
  have hc := Nat.mul_le_mul_right (n.descFactorial 3) (Finset.card_le_of_subset hsub)
  have he := GrowingMatching.containment_card_mul_descFactorial hkn I
  rw [hcard] at he
  exact hc.trans he.le

theorem badFirstEvent_eq_biUnion (k : ℕ) (T : κ → Finset (Fin n)) :
    badFirstEvent k T =
      (largeSupportRows T).biUnion (fun j => GoodEvent.containmentEvent k (T j)) := by
  classical
  ext σ
  simp [badFirstEvent,largeSupportRows]

/-- Integer finite union bound, also valid below selected arity three. -/
theorem badFirstEvent_card_mul_le (hkn : k ≤ n) (T : κ → Finset (Fin n)) :
    (badFirstEvent k T).card * n.descFactorial 3 ≤
      largeSupportCount T * k.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hc : (badFirstEvent k T).card ≤
      ∑ j in largeSupportRows T, (GoodEvent.containmentEvent k (T j)).card := by
    rw [badFirstEvent_eq_biUnion]
    exact Finset.card_biUnion_le
  calc
    _ ≤ (∑ j in largeSupportRows T, (GoodEvent.containmentEvent k (T j)).card) *
        n.descFactorial 3 := Nat.mul_le_mul_right _ hc
    _ = ∑ j in largeSupportRows T,
        (GoodEvent.containmentEvent k (T j)).card * n.descFactorial 3 := Finset.sum_mul
    _ ≤ ∑ _j in largeSupportRows T,
        k.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact support_containment_card_mul_le hkn (T j) ((mem_largeSupportRows T j).mp hj)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,largeSupportCount]
      ring

private lemma descFactorial_three_pos (hn : 3 ≤ n) : 0 < n.descFactorial 3 :=
  Nat.pos_of_ne_zero (fun hz => (not_lt_of_ge hn) (Nat.descFactorial_eq_zero_iff_lt.mp hz))

/-- The literal permutation fraction, with the exact falling-factorial numerator. -/
theorem badFirstEvent_fraction_le (hkn : k ≤ n) (hn : 3 ≤ n)
    (T : κ → Finset (Fin n)) :
    ((badFirstEvent k T).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) ≤
      (largeSupportCount T : ℝ) * (k.descFactorial 3 : ℝ) / (n.descFactorial 3 : ℝ) := by
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin n)⟩
  have hD : (0 : ℝ) < n.descFactorial 3 := by exact_mod_cast descFactorial_three_pos hn
  apply (div_le_div_iff hP hD).mpr
  exact_mod_cast badFirstEvent_card_mul_le hkn T

/-- Requests of support size three cannot fit in a smaller selected set. -/
theorem badFirstEvent_empty_of_arity_lt_three (hkn : k ≤ n) (hk : k < 3)
    (T : κ → Finset (Fin n)) : badFirstEvent k T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro σ hσ
  obtain ⟨j,hlarge,hsub⟩ := (mem_badFirstEvent k T σ).mp hσ
  have hc := Finset.card_le_of_subset hsub
  rw [GoodEvent.card_smallRankGaps hkn σ] at hc
  exact (not_le_of_gt hk) (hlarge.trans hc)

/-- Honest first-bad-event budget, expressed without division. -/
theorem badFirstEvent_card_four_mul_le (hkn : k ≤ n) (hn : 3 ≤ n)
    (T : κ → Finset (Fin n))
    (hbudget : 4 * largeSupportCount T * k.descFactorial 3 ≤ n.descFactorial 3) :
    4 * (badFirstEvent k T).card ≤ Fintype.card (Equiv.Perm (Fin n)) := by
  apply (mul_le_mul_right (descFactorial_three_pos hn)).mp
  calc
    (4 * (badFirstEvent k T).card) * n.descFactorial 3 =
        4 * ((badFirstEvent k T).card * n.descFactorial 3) := by ring
    _ ≤ 4 * (largeSupportCount T * k.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n))) :=
      Nat.mul_le_mul_left 4 (badFirstEvent_card_mul_le hkn T)
    _ = (4 * largeSupportCount T * k.descFactorial 3) * Fintype.card (Equiv.Perm (Fin n)) := by ring
    _ ≤ n.descFactorial 3 * Fintype.card (Equiv.Perm (Fin n)) :=
      Nat.mul_le_mul_right _ hbudget
    _ = Fintype.card (Equiv.Perm (Fin n)) * n.descFactorial 3 := Nat.mul_comm _ _

#check @badFirstEvent_fraction_le
#print axioms support_containment_card_mul_le
#print axioms badFirstEvent_card_mul_le
#print axioms badFirstEvent_fraction_le
#print axioms badFirstEvent_empty_of_arity_lt_three
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.BadFirst
