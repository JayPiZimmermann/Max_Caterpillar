import MaxCaterpillar.Frontier.RandomRestriction.SelectedSetProbability

/-! # The actual first exceptional event for a finite row-support family

The input permutation maps labels to positions. The selected set consists
of labels in its first five positions. All row indices remain present;
only the support-cardinality condition selects the rows in the union bound.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BadFirst
open BigOperators
open SelectedSetProbability
variable {N : ℕ} {κ : Type*} [Fintype κ]

noncomputable def largeSupportRows (T : κ → Finset (Fin N)) : Finset κ := by
  classical
  exact Finset.univ.filter (fun j => 3 ≤ (T j).card)

noncomputable def largeSupportCount (T : κ → Finset (Fin N)) : ℕ :=
  (largeSupportRows T).card

/-- Literal uniform input permutations retaining at least one large row. -/
noncomputable def badFirstEvent (T : κ → Finset (Fin N)) :
    Finset (Equiv.Perm (Fin N)) := by
  classical
  exact Finset.univ.filter (fun σ =>
    ∃ j, 3 ≤ (T j).card ∧ T j ⊆ selectedLabels σ)

@[simp] theorem mem_largeSupportRows (T : κ → Finset (Fin N)) (j : κ) :
    j ∈ largeSupportRows T ↔ 3 ≤ (T j).card := by
  classical
  simp only [largeSupportRows,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_badFirstEvent (T : κ → Finset (Fin N))
    (σ : Equiv.Perm (Fin N)) :
    σ ∈ badFirstEvent T ↔ ∃ j, 3 ≤ (T j).card ∧ T j ⊆ selectedLabels σ := by
  classical
  simp only [badFirstEvent,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Each eligible row contributes its actual selected-set containment event. -/
theorem badFirstEvent_eq_biUnion (T : κ → Finset (Fin N)) :
    badFirstEvent T = (largeSupportRows T).biUnion (fun j => containsEvent (T j)) := by
  classical
  ext σ
  simp [badFirstEvent,largeSupportRows,containsEvent,selectedLabels]

/-- Three fixed support labels suffice; supports larger than five cause no
problem and no maximum support size is assumed. -/
theorem badFirstEvent_card_mul_le (hN : 5 ≤ N) (T : κ → Finset (Fin N)) :
    (badFirstEvent T).card * N.descFactorial 3 ≤
      60 * largeSupportCount T * Fintype.card (Equiv.Perm (Fin N)) := by
  classical
  have hc : (badFirstEvent T).card ≤
      ∑ j in largeSupportRows T, (containsEvent (T j)).card := by
    rw [badFirstEvent_eq_biUnion]
    exact Finset.card_biUnion_le
  calc
    _ ≤ (∑ j in largeSupportRows T, (containsEvent (T j)).card) * N.descFactorial 3 :=
      Nat.mul_le_mul_right _ hc
    _ = ∑ j in largeSupportRows T, (containsEvent (T j)).card * N.descFactorial 3 :=
      Finset.sum_mul
    _ ≤ ∑ _j in largeSupportRows T, 60 * Fintype.card (Equiv.Perm (Fin N)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact support_containsEvent_card_mul_le hN (T j) ((mem_largeSupportRows T j).mp hj)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,largeSupportCount]
      ring

private lemma descFactorial_three_pos (hN : 5 ≤ N) : 0 < N.descFactorial 3 := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hh := Nat.descFactorial_eq_zero_iff_lt.mp hz
  linarith only [hN,hh]

/-- Finite uniform fraction of the literal first exceptional event. -/
theorem badFirstEvent_fraction_le (hN : 5 ≤ N) (T : κ → Finset (Fin N)) :
    ((badFirstEvent T).card : ℝ) / Fintype.card (Equiv.Perm (Fin N)) ≤
      60 * (largeSupportCount T : ℝ) / (N.descFactorial 3 : ℝ) := by
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin N)⟩
  have hD : (0 : ℝ) < N.descFactorial 3 := by exact_mod_cast descFactorial_three_pos hN
  apply (div_le_div_iff hP hD).mpr
  exact_mod_cast badFirstEvent_card_mul_le hN T

/-- The small non-braid-row budget leaves at most one quarter of permutations
in the first exceptional event. This is an integer cardinal inequality. -/
theorem badFirstEvent_card_four_mul_le (hN : 5 ≤ N) (T : κ → Finset (Fin N))
    (hbudget : 240 * largeSupportCount T ≤ N.descFactorial 3) :
    4 * (badFirstEvent T).card ≤ Fintype.card (Equiv.Perm (Fin N)) := by
  apply (mul_le_mul_right (descFactorial_three_pos hN)).mp
  calc
    (4 * (badFirstEvent T).card) * N.descFactorial 3 =
        4 * ((badFirstEvent T).card * N.descFactorial 3) := by ring
    _ ≤ 4 * (60 * largeSupportCount T * Fintype.card (Equiv.Perm (Fin N))) :=
      Nat.mul_le_mul_left 4 (badFirstEvent_card_mul_le hN T)
    _ = (240 * largeSupportCount T) * Fintype.card (Equiv.Perm (Fin N)) := by ring
    _ ≤ N.descFactorial 3 * Fintype.card (Equiv.Perm (Fin N)) :=
      Nat.mul_le_mul_right _ hbudget
    _ = Fintype.card (Equiv.Perm (Fin N)) * N.descFactorial 3 := Nat.mul_comm _ _

#print axioms badFirstEvent_card_mul_le
#print axioms badFirstEvent_fraction_le
#print axioms badFirstEvent_card_four_mul_le
end MaxCaterpillar.Frontier.RandomRestriction.BadFirst
