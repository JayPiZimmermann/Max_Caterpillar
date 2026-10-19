import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Weights

/-! # Exact cut-set reindexing for coordinate insertion

The three structured positions of the distinguished coordinate vertex have
explicit lower-word fibres.  Pendant insertion preserves a nonempty cut set;
endpoint insertion supplies the new boundary cut and therefore permits an
empty lower cut set.
-/

namespace MaxNN.Caterpillar

variable {s : ℕ}

def deletePendantCuts (i : Fin (s + 1)) (U : Finset (Fin (s + 1 + 1))) :
    Finset (Fin (s + 1)) :=
  Finset.univ.filter fun q => (pendantPos i).succAbove q ∈ U

@[simp] theorem mem_deletePendantCuts (i : Fin (s + 1))
    (U : Finset (Fin (s + 1 + 1))) (q : Fin (s + 1)) :
    q ∈ deletePendantCuts i U ↔ (pendantPos i).succAbove q ∈ U := by
  simp [deletePendantCuts]

theorem deletePendantCuts_insertPendantCuts (i : Fin (s + 1))
    (S : Finset (Fin (s + 1))) :
    deletePendantCuts i (insertPendantCuts i S) = S := by
  ext q
  simp only [mem_deletePendantCuts, insertPendantCuts, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (Fin.succAbove_right_injective he).symm ▸ ha
  · intro hq
    exact ⟨q, hq, rfl⟩

theorem insertPendantCuts_deletePendantCuts (i : Fin (s + 1))
    (U : Finset (Fin (s + 1 + 1))) (hi : pendantPos i ∉ U) :
    insertPendantCuts i (deletePendantCuts i U) = U := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact (mem_deletePendantCuts i U a).mp ha
  · intro hq
    have hne : q ≠ pendantPos i := fun he => hi (he ▸ hq)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hne
    apply Finset.mem_image.mpr
    refine ⟨a, (mem_deletePendantCuts i U a).mpr ?_, ha⟩
    rwa [ha]

theorem deletePendantCuts_mem_admissible (i : Fin (s + 1))
    (U : Finset (Fin (s + 1 + 1))) (hU : U ∈ admissibleCuts (s + 1))
    (hi : pendantPos i ∉ U) : deletePendantCuts i U ∈ admissibleCuts s := by
  have hU' : U ∈ (cutPositions (s + 1)).powerset.erase ∅ := by
    simpa only [admissibleCuts] using hU
  have hUne : U.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hU').1
  have hUsub : U ⊆ cutPositions (s + 1) :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU')
  have hSsub : deletePendantCuts i U ⊆ cutPositions s := by
    intro q hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hq0
    subst q
    have hmem := (mem_deletePendantCuts i U 0).mp hq
    rw [pendant_succAbove_zero] at hmem
    exact (Finset.mem_erase.mp (hUsub hmem)).1 rfl
  have hSne : (deletePendantCuts i U).Nonempty := by
    obtain ⟨q, hq⟩ := hUne
    have hqne : q ≠ pendantPos i := fun he => hi (he ▸ hq)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hqne
    exact ⟨a, (mem_deletePendantCuts i U a).mpr (by rwa [ha])⟩
  apply Finset.mem_erase.mpr
  exact ⟨hSne.ne_empty, Finset.mem_powerset.mpr hSsub⟩

/-- Cut sets with the distinguished base position pendant are exactly the
images of lower admissible cut sets. -/
noncomputable def pendantCutsEquiv (i : Fin (s + 1)) :
    {S : Finset (Fin (s + 1)) // S ∈ admissibleCuts s} ≃
      {U : Finset (Fin (s + 1 + 1)) //
        U ∈ admissibleCuts (s + 1) ∧ pendantPos i ∉ U} where
  toFun S := ⟨insertPendantCuts i S.1,
    insertPendantCuts_mem_admissible i S.1 S.2, insertPendantCuts_not_mem i S.1⟩
  invFun U := ⟨deletePendantCuts i U.1,
    deletePendantCuts_mem_admissible i U.1 U.2.1 U.2.2⟩
  left_inv S := Subtype.ext (deletePendantCuts_insertPendantCuts i S.1)
  right_inv U := Subtype.ext (insertPendantCuts_deletePendantCuts i U.1 U.2.2)

@[simp] theorem pendantCutsEquiv_apply (i : Fin (s + 1))
    (S : {S : Finset (Fin (s + 1)) // S ∈ admissibleCuts s}) :
    (pendantCutsEquiv i S).1 = insertPendantCuts i S.1 := rfl

def firstInsertCuts (S : Finset (Fin (s + 1))) : Finset (Fin (s + 1 + 1)) :=
  insert 1 (S.image Fin.succ)

def firstDeleteCuts (U : Finset (Fin (s + 1 + 1))) : Finset (Fin (s + 1)) :=
  Finset.univ.filter fun q => q ≠ 0 ∧ q.succ ∈ U

theorem one_eq_zero_succ :
    (1 : Fin (s + 1 + 1)) = (0 : Fin (s + 1)).succ := by
  apply Fin.ext
  change 1 % (s + 2) = 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem mem_firstDeleteCuts (U : Finset (Fin (s + 1 + 1)))
    (q : Fin (s + 1)) : q ∈ firstDeleteCuts U ↔ q ≠ 0 ∧ q.succ ∈ U := by
  simp [firstDeleteCuts]

theorem firstInsertCuts_mem_admissible (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) : firstInsertCuts S ∈ admissibleCuts (s + 1) := by
  have hsub : firstInsertCuts S ⊆ cutPositions (s + 1) := by
    intro q hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_insert.mp hq with hq | hq
    · rw [hq]
      rw [one_eq_zero_succ]
      exact Fin.succ_ne_zero 0
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
      exact Fin.succ_ne_zero a
  apply Finset.mem_erase.mpr
  exact ⟨(Finset.insert_nonempty _ _).ne_empty, Finset.mem_powerset.mpr hsub⟩

@[simp] theorem one_mem_firstInsertCuts (S : Finset (Fin (s + 1))) :
    (1 : Fin (s + 1 + 1)) ∈ firstInsertCuts S := Finset.mem_insert_self _ _

theorem firstDeleteCuts_subset_cutPositions (U : Finset (Fin (s + 1 + 1))) :
    firstDeleteCuts U ⊆ cutPositions s := by
  intro q hq
  exact Finset.mem_erase.mpr ⟨(mem_firstDeleteCuts U q).mp hq |>.1, Finset.mem_univ _⟩

theorem firstDeleteCuts_firstInsertCuts (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) : firstDeleteCuts (firstInsertCuts S) = S := by
  ext q
  have hq0 : q ∈ S → q ≠ 0 := fun hq => (Finset.mem_erase.mp (hS hq)).1
  constructor
  · intro hq
    have h := (mem_firstDeleteCuts _ q).mp hq
    rcases Finset.mem_insert.mp h.2 with hsucc | hsucc
    · rw [one_eq_zero_succ] at hsucc
      apply False.elim
      apply h.1
      apply Fin.ext
      have hv := congrArg (fun z : Fin (s + 1 + 1) => z.val) hsucc
      change q.val + 1 = 0 + 1 at hv
      exact Nat.add_right_cancel hv
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hsucc
      have hae : a = q := by
        apply Fin.ext
        have hv := congrArg (fun z : Fin (s + 1 + 1) => z.val) he
        change a.val + 1 = q.val + 1 at hv
        exact Nat.add_right_cancel hv
      exact hae.symm ▸ ha
  · intro hq
    apply (mem_firstDeleteCuts _ q).mpr
    exact ⟨hq0 hq, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, hq, rfl⟩)⟩

theorem firstInsertCuts_firstDeleteCuts (U : Finset (Fin (s + 1 + 1)))
    (hU : U ∈ admissibleCuts (s + 1)) (h1 : (1 : Fin (s + 1 + 1)) ∈ U) :
    firstInsertCuts (firstDeleteCuts U) = U := by
  have hUsub : U ⊆ cutPositions (s + 1) :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU)
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · rwa [hq]
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact (mem_firstDeleteCuts U a).mp ha |>.2
  · intro hq
    rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨a, rfl⟩
    · exact False.elim ((Finset.mem_erase.mp (hUsub hq)).1 rfl)
    · by_cases ha0 : a = 0
      · subst a
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨a, (mem_firstDeleteCuts U a).mpr ⟨ha0, hq⟩, rfl⟩)

noncomputable def firstCutsEquiv :
    {S : Finset (Fin (s + 1)) // S ⊆ cutPositions s} ≃
      {U : Finset (Fin (s + 1 + 1)) //
        U ∈ admissibleCuts (s + 1) ∧ (1 : Fin (s + 1 + 1)) ∈ U} where
  toFun S := ⟨firstInsertCuts S.1,
    firstInsertCuts_mem_admissible S.1 S.2, one_mem_firstInsertCuts S.1⟩
  invFun U := ⟨firstDeleteCuts U.1, firstDeleteCuts_subset_cutPositions U.1⟩
  left_inv S := Subtype.ext (firstDeleteCuts_firstInsertCuts S.1 S.2)
  right_inv U := Subtype.ext (firstInsertCuts_firstDeleteCuts U.1 U.2.1 U.2.2)

@[simp] theorem firstCutsEquiv_apply
    (S : {S : Finset (Fin (s + 1)) // S ⊆ cutPositions s}) :
    (firstCutsEquiv S).1 = firstInsertCuts S.1 := rfl

theorem card_firstInsertCuts (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) : (firstInsertCuts S).card = S.card + 1 := by
  have hnot : (1 : Fin (s + 1 + 1)) ∉ S.image Fin.succ := by
    intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    rw [one_eq_zero_succ] at he
    have ha0 : a = 0 := by
      apply Fin.ext
      have hv := congrArg (fun z : Fin (s + 1 + 1) => z.val) he
      change a.val + 1 = 0 + 1 at hv
      exact Nat.add_right_cancel hv
    exact (Finset.mem_erase.mp (hS (ha0 ▸ ha))).1 rfl
  have hc : (S.image Fin.succ).card = S.card := by
    exact Finset.card_image_of_injective S (Fin.succ_injective (s + 1))
  rw [firstInsertCuts, Finset.card_insert_of_not_mem hnot, hc]

theorem wordWeight_firstInsertCuts (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) :
    wordWeight (s + 1) (firstInsertCuts S) =
      ((s + 3 : ℝ)⁻¹) * wordWeight s S :=
  wordWeight_succ_of_card_eq_add_one S _ (card_firstInsertCuts S hS)

def lastDeleteCuts (U : Finset (Fin (s + 1 + 1))) : Finset (Fin (s + 1)) :=
  Finset.univ.filter fun q => q.castSucc ∈ U

@[simp] theorem mem_lastDeleteCuts (U : Finset (Fin (s + 1 + 1)))
    (q : Fin (s + 1)) : q ∈ lastDeleteCuts U ↔ q.castSucc ∈ U := by
  simp [lastDeleteCuts]

theorem joinCuts_empty_eq_insert_last (S : Finset (Fin (s + 1))) :
    joinCuts (s := 0) S (∅ : Finset (Fin 1)) =
      insert (Fin.last (s + 1)) (S.image Fin.castSucc) := by
  ext q
  simp only [joinCuts, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.not_mem_empty, false_and, exists_false, or_false, leftPos, rightPos]
  constructor
  · rintro (⟨a, ha, rfl⟩ | hlast)
    · exact Or.inr ⟨a, ha, rfl⟩
    · apply Or.inl
      apply Fin.ext
      simpa [rightPos] using congrArg Fin.val hlast
  · rintro (hlast | ⟨a, ha, rfl⟩)
    · apply Or.inr
      apply Fin.ext
      simpa [rightPos] using congrArg Fin.val hlast
    · exact Or.inl ⟨a, ha, rfl⟩

theorem lastDeleteCuts_joinCuts_empty (S : Finset (Fin (s + 1))) :
    lastDeleteCuts (joinCuts (s := 0) S (∅ : Finset (Fin 1))) = S := by
  rw [joinCuts_empty_eq_insert_last]
  ext q
  simp only [mem_lastDeleteCuts, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (he | ⟨a, ha, he⟩)
    · apply False.elim
      have hv := congrArg (fun z : Fin (s + 1 + 1) => z.val) he
      change q.val = s + 1 at hv
      exact (Nat.ne_of_lt q.isLt) hv
    · have hae : a = q := by
        apply Fin.ext
        exact congrArg (fun z : Fin (s + 1 + 1) => z.val) he
      exact hae.symm ▸ ha
  · intro hq
    exact Or.inr ⟨q, hq, rfl⟩

theorem joinCuts_empty_lastDeleteCuts (U : Finset (Fin (s + 1 + 1)))
    (hlast : Fin.last (s + 1) ∈ U) :
    joinCuts (s := 0) (lastDeleteCuts U) (∅ : Finset (Fin 1)) = U := by
  rw [joinCuts_empty_eq_insert_last]
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · exact hq ▸ hlast
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact (mem_lastDeleteCuts U a).mp ha
  · intro hq
    by_cases hqLast : q = Fin.last (s + 1)
    · exact Finset.mem_insert.mpr (Or.inl hqLast)
    · obtain ⟨a, ha⟩ := (Fin.exists_castSucc_eq).mpr hqLast
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨a, (mem_lastDeleteCuts U a).mpr (by rwa [ha]), ha⟩)

theorem lastDeleteCuts_subset_cutPositions (U : Finset (Fin (s + 1 + 1)))
    (hU : U ∈ admissibleCuts (s + 1)) : lastDeleteCuts U ⊆ cutPositions s := by
  have hUsub : U ⊆ cutPositions (s + 1) :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU)
  intro q hq
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro hq0
  subst q
  have hm := (mem_lastDeleteCuts U 0).mp hq
  exact (Finset.mem_erase.mp (hUsub hm)).1 rfl

theorem joinCuts_empty_mem_admissible (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) :
    joinCuts (s := 0) S (∅ : Finset (Fin 1)) ∈ admissibleCuts (s + 1) := by
  rw [joinCuts_empty_eq_insert_last]
  have hsub : insert (Fin.last (s + 1)) (S.image Fin.castSucc) ⊆
      cutPositions (s + 1) := by
    intro q hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_insert.mp hq with hq | hq
    · rw [hq]
      intro h
      have hv := congrArg Fin.val h
      change s + 1 = 0 at hv
      omega
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      intro h
      apply (Finset.mem_erase.mp (hS ha)).1
      apply Fin.ext
      exact congrArg (fun z : Fin (s + 1 + 1) => z.val) h
  apply Finset.mem_erase.mpr
  exact ⟨(Finset.insert_nonempty _ _).ne_empty, Finset.mem_powerset.mpr hsub⟩

@[simp] theorem last_mem_joinCuts_empty (S : Finset (Fin (s + 1))) :
    Fin.last (s + 1) ∈ joinCuts (s := 0) S (∅ : Finset (Fin 1)) := by
  rw [joinCuts_empty_eq_insert_last]
  exact Finset.mem_insert_self _ _

noncomputable def lastCutsEquiv :
    {S : Finset (Fin (s + 1)) // S ⊆ cutPositions s} ≃
      {U : Finset (Fin (s + 1 + 1)) //
        U ∈ admissibleCuts (s + 1) ∧ Fin.last (s + 1) ∈ U} where
  toFun S := ⟨joinCuts (s := 0) S.1 (∅ : Finset (Fin 1)),
    joinCuts_empty_mem_admissible S.1 S.2, last_mem_joinCuts_empty S.1⟩
  invFun U := ⟨lastDeleteCuts U.1, lastDeleteCuts_subset_cutPositions U.1 U.2.1⟩
  left_inv S := Subtype.ext (lastDeleteCuts_joinCuts_empty S.1)
  right_inv U := Subtype.ext (joinCuts_empty_lastDeleteCuts U.1 U.2.2)

@[simp] theorem lastCutsEquiv_apply
    (S : {S : Finset (Fin (s + 1)) // S ⊆ cutPositions s}) :
    (lastCutsEquiv S).1 = joinCuts (s := 0) S.1 (∅ : Finset (Fin 1)) := rfl

theorem card_joinCuts_empty_of_subset (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) :
    (joinCuts (s := 0) S (∅ : Finset (Fin 1))).card = S.card + 1 := by
  exact card_lastEndpointCuts S

theorem wordWeight_joinCuts_empty_of_subset (S : Finset (Fin (s + 1)))
    (hS : S ⊆ cutPositions s) :
    wordWeight (s + 1) (joinCuts (s := 0) S (∅ : Finset (Fin 1))) =
      ((s + 3 : ℝ)⁻¹) * wordWeight s S :=
  wordWeight_lastEndpointCuts S

/-- Exhaustive, disjoint-by-construction cases for the base position of the
distinguished coordinate vertex and its relation to the upper cut set. -/
theorem coordinateCutCases (U : Finset (Fin (s + 1 + 1))) (k : Fin (s + 1 + 1)) :
    (k = 0 ∧ (1 : Fin (s + 1 + 1)) ∈ U) ∨
    (k = 0 ∧ (1 : Fin (s + 1 + 1)) ∉ U) ∨
    (∃ i : Fin (s + 1), k = i.succ ∧ k ∉ U) ∨
    (k = Fin.last (s + 1) ∧ k ∈ U) ∨
    (∃ i : Fin (s + 1), k = i.succ ∧ k ∈ U ∧ k ≠ Fin.last (s + 1)) := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · by_cases h1 : (1 : Fin (s + 1 + 1)) ∈ U
    · exact Or.inl ⟨rfl, h1⟩
    · exact Or.inr (Or.inl ⟨rfl, h1⟩)
  · by_cases hi : i.succ ∈ U
    · by_cases hilast : i.succ = Fin.last (s + 1)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hilast, hi⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl, hi, hilast⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨i, rfl, hi⟩))

end MaxNN.Caterpillar
