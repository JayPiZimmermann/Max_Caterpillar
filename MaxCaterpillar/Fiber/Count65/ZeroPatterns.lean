import MaxCaterpillar.Definitions
import MaxCaterpillar.Fiber.First65.TwoRootGeometry

/-! # Zero patterns of four feature covectors

These finite support arguments turn triple-tie coverage and large supports
into the column nondegeneracy used in the circuit obstruction. No network
classification or circuit is assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65

/-- A four-vector with at least three nonzero coordinates can vanish at only
one coordinate. -/
theorem large_support_at_most_one_zero (a : Point 4)
    (hcard : 3 ≤ (nonzeroCoordinates a).card) {i k : Fin 4}
    (hi : a i = 0) (hk : a k = 0) : i = k := by
  classical
  by_contra hik
  have hki : k ∈ (Finset.univ : Finset (Fin 4)).erase i := by simp [Ne.symm hik]
  have hsize : (((Finset.univ : Finset (Fin 4)).erase i).erase k).card = 2 := by
    rw [Finset.card_erase_of_mem hki, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  have hsub : nonzeroCoordinates a ⊆ ((Finset.univ : Finset (Fin 4)).erase i).erase k := by
    intro j hj
    have haj : a j ≠ 0 := (mem_nonzeroCoordinates a j).mp hj
    exact Finset.mem_erase.mpr ⟨(fun he => haj (he ▸ hk)),
      Finset.mem_erase.mpr ⟨(fun he => haj (he ▸ hi)), Finset.mem_univ j⟩⟩
  have hle := Finset.card_le_of_subset hsub
  rw [hsize] at hle
  linarith

/-- Four large-support rows covering all four omissions have exactly one
omission each; in particular every input coordinate is read by two rows. -/
theorem four_large_rows_columns_used (A : Fin 4 → Point 4)
    (hlarge : ∀ j, 3 ≤ (nonzeroCoordinates (A j)).card)
    (hcover : ∀ i, ∃ j, A j i = 0) :
    ∀ i, ∃ j k, j ≠ k ∧ A j i ≠ 0 ∧ A k i ≠ 0 := by
  classical
  choose missing hmissing using hcover
  have hinj : Function.Injective missing := by
    intro i k he
    apply large_support_at_most_one_zero (A (missing i)) (hlarge (missing i)) (hmissing i)
    rw [he]
    exact hmissing k
  have hsurj : Function.Surjective missing := Finite.surjective_of_injective hinj
  have hread : ∀ i j, j ≠ missing i → A j i ≠ 0 := by
    intro i j hji hzero
    obtain ⟨k, hk⟩ := hsurj j
    have hik : i = k := large_support_at_most_one_zero (A j) (hlarge j) hzero
      (by rw [← hk]; exact hmissing k)
    exact hji (by rw [← hk, hik])
  intro i
  let S : Finset (Fin 4) := Finset.univ.erase (missing i)
  have hs : 1 < S.card := by
    simp only [S, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_trans (by norm_num : 0 < 1) hs)
  obtain ⟨k, hk, hkj⟩ := Finset.exists_ne_of_one_lt_card hs j
  exact ⟨j, k, hkj.symm, hread i j (Finset.ne_of_mem_erase hj),
    hread i k (Finset.ne_of_mem_erase hk)⟩

/-- One row with two live coordinates and three large-support rows also
forces every column to be read twice, as soon as triple-tie coverage holds. -/
theorem three_large_rows_columns_used (A : Fin 4 → Point 4)
    (r : Fin 4) (u v : Fin 4) (huv : u ≠ v)
    (hu : A r u ≠ 0) (hv : A r v ≠ 0)
    (hlarge : ∀ j, j ≠ r → 3 ≤ (nonzeroCoordinates (A j)).card)
    (hcover : ∀ i, ∃ j, A j i = 0) :
    ∀ i, ∃ j k, j ≠ k ∧ A j i ≠ 0 ∧ A k i ≠ 0 := by
  classical
  obtain ⟨j, hju⟩ := hcover u
  obtain ⟨k, hkv⟩ := hcover v
  have hjr : j ≠ r := by intro he; subst j; exact hu hju
  have hkr : k ≠ r := by intro he; subst k; exact hv hkv
  have hjk : j ≠ k := by
    intro he
    exact huv (large_support_at_most_one_zero (A j) (hlarge j hjr) hju (he ▸ hkv))
  have hjread : ∀ i, i ≠ u → A j i ≠ 0 := by
    intro i hi hzero
    exact hi (large_support_at_most_one_zero (A j) (hlarge j hjr) hzero hju)
  have hkread : ∀ i, i ≠ v → A k i ≠ 0 := by
    intro i hi hzero
    exact hi (large_support_at_most_one_zero (A k) (hlarge k hkr) hzero hkv)
  intro i
  by_cases hiu : i = u
  · subst i
    exact ⟨r, k, hkr.symm, hu, hkread u huv⟩
  · by_cases hiv : i = v
    · subst i
      exact ⟨r, j, hjr.symm, hv, hjread v huv.symm⟩
    · exact ⟨j, k, hjk, hjread i hiu, hkread i hiv⟩

/-- A large-support row is not any signed coordinate difference. This is the
unoriented nonroot predicate used by the active-facet classification. -/
theorem large_support_not_coordinate_difference (a : Point 4)
    (hcard : 3 ≤ (nonzeroCoordinates a).card) :
    ∀ i j : Fin 4, i ≠ j → ¬ ∃ c : ℝ, ∀ k,
      a k = c * ((if k = i then 1 else 0) - (if k = j then 1 else 0)) := by
  classical
  intro i j hij h
  obtain ⟨c, hc⟩ := h
  have hsub : nonzeroCoordinates a ⊆ ({i,j} : Finset (Fin 4)) := by
    intro k hk
    have hkn : a k ≠ 0 := (mem_nonzeroCoordinates a k).mp hk
    by_contra hn
    have hki : k ≠ i := by intro he; exact hn (by simp [he])
    have hkj : k ≠ j := by intro he; exact hn (by simp [he])
    apply hkn
    rw [hc k, if_neg hki, if_neg hkj]
    ring
  have hle := Finset.card_le_of_subset hsub
  have hp : ({i,j} : Finset (Fin 4)).card = 2 := by simp [hij]
  rw [hp] at hle
  linarith

#print axioms four_large_rows_columns_used
#print axioms three_large_rows_columns_used
end MaxCaterpillar.Fiber.Count65
