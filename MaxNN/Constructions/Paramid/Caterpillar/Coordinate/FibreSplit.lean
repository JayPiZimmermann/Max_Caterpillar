import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.ReindexActive

/-! # Separating the two empty-cut endpoint fibres -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

theorem sum_lowerCutSubsets_eq_empty_add_admissible
    {M : Type*} [AddCommMonoid M] (f : Finset (Fin (s + 1)) → M) :
    (∑ S : LowerCutSubsets s, f S.1) =
      f ∅ + ∑ S in admissibleCuts s, f S := by
  classical
  rw [← Finset.sum_subtype ((cutPositions s).powerset)
    (fun S => Finset.mem_powerset)]
  unfold admissibleCuts
  calc
    (∑ S in (cutPositions s).powerset, f S) =
        (∑ S in (cutPositions s).powerset.erase ∅, f S) + f ∅ :=
      (Finset.sum_erase_add ((cutPositions s).powerset) f (by simp)).symm
    _ = f ∅ + ∑ S in (cutPositions s).powerset.erase ∅, f S := add_comm _ _

noncomputable def coordinateFirstNonemptySum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
    coordinateUpperTerm 1 π (firstInsertCuts S)

noncomputable def coordinateLastNonemptySum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
    coordinateUpperTerm (Fin.last (s + 2)) π
      (joinCuts (s := 0) S (∅ : Finset (Fin 1)))

noncomputable def coordinateEndpointStarSum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)),
    (coordinateUpperTerm 1 π (firstInsertCuts (∅ : Finset (Fin (s + 1)))) +
      coordinateUpperTerm (Fin.last (s + 2)) π
        (joinCuts (s := 0) (∅ : Finset (Fin (s + 1)))
          (∅ : Finset (Fin 1))))

theorem coordinateFirstFibreSum_eq_empty_add_nonempty :
    coordinateFirstFibreSum s =
      (∑ π : Equiv.Perm (Fin (s + 2)),
        coordinateUpperTerm 1 π (firstInsertCuts (∅ : Finset (Fin (s + 1))))) +
      coordinateFirstNonemptySum s := by
  classical
  unfold coordinateFirstFibreSum coordinateFirstNonemptySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro π hπ
  exact sum_lowerCutSubsets_eq_empty_add_admissible
    (fun S => coordinateUpperTerm 1 π (firstInsertCuts S))

theorem coordinateLastFibreSum_eq_empty_add_nonempty :
    coordinateLastFibreSum s =
      (∑ π : Equiv.Perm (Fin (s + 2)),
        coordinateUpperTerm (Fin.last (s + 2)) π
          (joinCuts (s := 0) (∅ : Finset (Fin (s + 1)))
            (∅ : Finset (Fin 1)))) +
      coordinateLastNonemptySum s := by
  classical
  unfold coordinateLastFibreSum coordinateLastNonemptySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro π hπ
  exact sum_lowerCutSubsets_eq_empty_add_admissible
    (fun S => coordinateUpperTerm (Fin.last (s + 2)) π
      (joinCuts (s := 0) S (∅ : Finset (Fin 1))))

theorem coordinateActiveSum_eq_nonempty_add_star :
    coordinateActiveSum s =
      coordinatePendantFibreSum s + coordinateFirstNonemptySum s +
        coordinateLastNonemptySum s + coordinateEndpointStarSum s := by
  rw [coordinateActiveSum_eq_fibreSums,
    coordinateFirstFibreSum_eq_empty_add_nonempty,
    coordinateLastFibreSum_eq_empty_add_nonempty]
  unfold coordinateEndpointStarSum
  rw [Finset.sum_add_distrib]
  abel

end MaxNN.Caterpillar
