import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Reindex
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Inactive

/-! # The active coordinate insertion fibres

Every term of the reindexed coordinate formula either belongs to one of the
three insertion fibres (first endpoint, a pendant, or the last endpoint), or
is individually lower-dimensional.  Keeping the active terms on the original
index set avoids any counting before the exact cut-set equivalences are used.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

def coordinateActive (p : Fin (s + 3)) (U : Finset (Fin (s + 2))) : Prop :=
  (p = 1 ∧ (1 : Fin (s + 2)) ∈ U) ∨
    ∃ j : Fin (s + 1), p = j.succ.succ ∧
      (j.succ ∉ U ∨ j.succ = Fin.last (s + 1))

noncomputable local instance coordinateActiveDecidable (p : Fin (s + 3))
    (U : Finset (Fin (s + 2))) : Decidable (coordinateActive p U) :=
  Classical.propDecidable _

noncomputable def coordinateUpperTerm (p : Fin (s + 3))
    (π : Equiv.Perm (Fin (s + 2))) (U : Finset (Fin (s + 2))) :
    (Fin (s + 2) → ℝ) → ℝ :=
  wordWeight (s + 1) U •
    germDiff (coordinateOne s) (coordinateUpperUnit p π U)

noncomputable def coordinateRawSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ p : Fin (s + 3), ∑ π : Equiv.Perm (Fin (s + 2)),
    ∑ U in admissibleCuts (s + 1), coordinateUpperTerm p π U

noncomputable def coordinateActiveSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ p : Fin (s + 3), ∑ π : Equiv.Perm (Fin (s + 2)),
    ∑ U in admissibleCuts (s + 1),
      if coordinateActive p U then coordinateUpperTerm p π U else 0

theorem coordinateUpperTerm_sub_active_mem_LSpan (hs : 1 ≤ s)
    (p : Fin (s + 3)) (π : Equiv.Perm (Fin (s + 2)))
    (U : Finset (Fin (s + 2))) :
    coordinateUpperTerm p π U -
        (if coordinateActive p U then coordinateUpperTerm p π U else 0) ∈
      LSpan (s + 2) s := by
  classical
  by_cases ha : coordinateActive p U
  · simp [ha]
  · simp only [ha, if_false, sub_zero]
    rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨k, rfl⟩
    · apply Submodule.smul_mem
      exact DoublingAux.LSpan_mono hs (by
        simpa [coordinateUpperTerm, coordinateUpperUnit, coordinateUpperWord,
          coordinateOne, zeroCoordinateDirection] using
          (germDiff_insertZeroPerm_zero_mem_LSpan_one (r := s + 1) π U))
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · have h1 : (1 : Fin (s + 2)) ∉ U := by
          intro hmem
          apply ha
          exact Or.inl ⟨rfl, hmem⟩
        apply Submodule.smul_mem
        simpa [coordinateUpperTerm, coordinateUpperUnit, coordinateUpperWord,
          coordinateOne, zeroCoordinateDirection] using
          (germDiff_insertZeroPerm_one_mem_LSpan (r := s + 1)
            (by omega) π U h1)
      · have hjU : j.succ ∈ U := by
          by_contra hnot
          apply ha
          exact Or.inr ⟨j, rfl, Or.inl hnot⟩
        have hjlast : j.succ ≠ Fin.last (s + 1) := by
          intro heq
          apply ha
          exact Or.inr ⟨j, rfl, Or.inr heq⟩
        apply Submodule.smul_mem
        simpa [coordinateUpperTerm, coordinateUpperUnit, coordinateUpperWord,
          coordinateOne, zeroCoordinateDirection] using
          (germDiff_insertZeroPerm_interior_head_mem_LSpan
            (r := s + 1) π U j hjU hjlast)

theorem coordinateRawSum_sub_activeSum_mem_LSpan (hs : 1 ≤ s) :
    coordinateRawSum s - coordinateActiveSum s ∈ LSpan (s + 2) s := by
  classical
  unfold coordinateRawSum coordinateActiveSum
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro π hπ
  rw [← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun U hU =>
    coordinateUpperTerm_sub_active_mem_LSpan hs p π U

theorem germDiff_formula_eq_coordinateRawSum :
    germDiff (coordinateOne s) (formula (s + 1)) = coordinateRawSum s := by
  exact germDiff_formula_coordinate_reindex

end MaxNN.Caterpillar
