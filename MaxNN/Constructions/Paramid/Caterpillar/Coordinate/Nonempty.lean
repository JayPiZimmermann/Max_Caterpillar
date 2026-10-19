import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.FibreSplit
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.EndpointCanonical

/-! # The nonempty active fibres and the structured deletion sum -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

noncomputable def coordinatePendantNonemptySum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
    ∑ i : Fin (s + 1),
      wordWeight (s + 1) (insertPendantCuts i S) •
        germDiff (coordinateOne s) (coordinatePendantUnit π S i)

noncomputable def coordinateFirstStructuredSum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
    wordWeight (1 + s) (joinCuts (∅ : Finset (Fin 1)) S) •
      germDiff (coordinateOne s) (coordinateFirstUnit π S)

noncomputable def coordinateLastStructuredSum (s : ℕ) :
    (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
    wordWeight (s + 1) (joinCuts S (∅ : Finset (Fin 1))) •
      germDiff (coordinateOne s) (coordinateLastUnit π S)

theorem coordinatePendantFibreSum_eq_nonempty :
    coordinatePendantFibreSum s = coordinatePendantNonemptySum s := by
  classical
  unfold coordinatePendantFibreSum coordinatePendantNonemptySum
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Finset.sum_comm]
  rw [Finset.sum_subtype (admissibleCuts s) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro i hi
  unfold coordinateUpperTerm
  rw [coordinateUpperUnit_pendant]

theorem coordinateLastNonemptySum_eq_structured :
    coordinateLastNonemptySum s = coordinateLastStructuredSum s := by
  classical
  unfold coordinateLastNonemptySum coordinateLastStructuredSum
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro S hS
  unfold coordinateUpperTerm
  rw [coordinateUpperUnit_last]

theorem coordinateFirstNonemptySum_eq_structured :
    coordinateFirstNonemptySum s = coordinateFirstStructuredSum s := by
  classical
  unfold coordinateFirstNonemptySum coordinateFirstStructuredSum
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ cutPositions s :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
  have h0 : (0 : Fin (s + 1)) ∉ S := zero_not_mem_of_admissible hS
  unfold coordinateUpperTerm
  rw [coordinateUpperUnit_first,
    wordWeight_firstInsertCuts S hsub,
    wordWeight_firstEndpointCuts S h0]

theorem coordinateStructuredSum_eq_three_nonempty :
    coordinateStructuredSum s = coordinatePendantNonemptySum s +
      coordinateFirstStructuredSum s + coordinateLastStructuredSum s := by
  classical
  unfold coordinateStructuredSum coordinateStructuredBlock
  unfold coordinatePendantNonemptySum coordinateFirstStructuredSum
    coordinateLastStructuredSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

theorem coordinateActiveSum_eq_structured_add_star :
    coordinateActiveSum s = coordinateStructuredSum s + coordinateEndpointStarSum s := by
  rw [coordinateActiveSum_eq_nonempty_add_star,
    coordinatePendantFibreSum_eq_nonempty,
    coordinateFirstNonemptySum_eq_structured,
    coordinateLastNonemptySum_eq_structured,
    coordinateStructuredSum_eq_three_nonempty]

end MaxNN.Caterpillar
