import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Structured
import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex

/-! # Reindexing actual simplex words by the position of vertex zero -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {s : ℕ}

noncomputable def coordinateUpperWord (p : Fin (s + 3))
    (π : Equiv.Perm (Fin (s + 2))) : Fin (s + 3) → Fin (s + 2) → ℝ :=
  fun a => toR (vtx (insertZeroPerm p π a))

noncomputable def coordinateUpperUnit (p : Fin (s + 3))
    (π : Equiv.Perm (Fin (s + 2))) (U : Finset (Fin (s + 2))) :
    (Fin (s + 2) → ℝ) → ℝ :=
  caterpillarUnit (coordinateUpperWord p π 0)
    (fun i : Fin (s + 2) => coordinateUpperWord p π i.succ) U

@[simp] theorem toR_vtx_zero_coordinate :
    toR (vtx (0 : Fin (s + 3))) = (0 : Fin (s + 2) → ℝ) := by
  funext i
  simp [toR, vtx_zero]

@[simp] theorem toR_vtx_succ_coordinate (a : Fin (s + 2)) :
    toR (vtx a.succ) = coordinateVertex a := by
  funext i
  by_cases h : i = a
  · subst i
    simp [toR, vtx_succ, coordinateVertex]
  · simp [toR, vtx_succ, coordinateVertex, Pi.single_apply, h, Ne.symm h]

theorem coordinateUpperWord_eq_insertNth (p : Fin (s + 3))
    (π : Equiv.Perm (Fin (s + 2))) :
    coordinateUpperWord p π =
      Fin.insertNth p 0 (fun q => coordinateVertex (π q)) := by
  funext a
  refine Fin.succAboveCases p ?_ (fun q => ?_) a
  · change toR (vtx (insertZeroPerm p π p)) = _
    rw [insertZeroPerm_at, toR_vtx_zero_coordinate, Fin.insertNth_apply_same]
  · change toR (vtx (insertZeroPerm p π (p.succAbove q))) = _
    rw [insertZeroPerm_lift, toR_vtx_succ_coordinate,
      Fin.insertNth_apply_succAbove]

theorem coordinateUpperWord_succ_apex (k : Fin (s + 2))
    (π : Equiv.Perm (Fin (s + 2))) :
    coordinateUpperWord k.succ π 0 = coordinateVertex (π 0) := by
  rw [coordinateUpperWord_eq_insertNth]
  rw [← Fin.succ_succAbove_zero k]
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem coordinateUpperWord_succ_tail (k : Fin (s + 2))
    (π : Equiv.Perm (Fin (s + 2))) :
    (fun q : Fin (s + 2) => coordinateUpperWord k.succ π q.succ) =
      Fin.insertNth k 0 (fun q : Fin (s + 1) => coordinateVertex (π q.succ)) := by
  rw [coordinateUpperWord_eq_insertNth]
  funext a
  refine Fin.succAboveCases k ?_ (fun q => ?_) a
  · simp
  · rw [Fin.insertNth_apply_succAbove]
    rw [← Fin.succ_succAbove_succ]
    exact Fin.insertNth_apply_succAbove _ _ _ _

theorem coordinateUpperUnit_pendant (i : Fin (s + 1))
    (π : Equiv.Perm (Fin (s + 2))) (S : Finset (Fin (s + 1))) :
    coordinateUpperUnit (pendantPos i).succ π (insertPendantCuts i S) =
      coordinatePendantUnit π S i := by
  unfold coordinateUpperUnit coordinatePendantUnit insertPendantWord coordinateA
  rw [coordinateUpperWord_succ_apex, coordinateUpperWord_succ_tail]

theorem insertNth_last_eq_append (A : Fin (s + 1) → Fin (s + 2) → ℝ) :
    Fin.insertNth (Fin.last (s + 1)) 0 A =
      Fin.append (m := s + 1) (n := 1) A (fun _ => 0) := by
  rw [Fin.insertNth_last, Fin.append_right_eq_snoc]
  congr 1

theorem coordinateUpperUnit_last (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) :
    coordinateUpperUnit (Fin.last (s + 2)) π
        (joinCuts S (∅ : Finset (Fin 1))) = coordinateLastUnit π S := by
  unfold coordinateUpperUnit coordinateLastUnit coordinateA
  rw [show (Fin.last (s + 2) : Fin (s + 3)) = (Fin.last (s + 1) : Fin (s + 2)).succ by
      apply Fin.ext; rfl,
    coordinateUpperWord_succ_apex, coordinateUpperWord_succ_tail,
    insertNth_last_eq_append]

theorem germDiff_formula_coordinate_reindex :
    germDiff (coordinateOne s) (formula (s + 1)) =
      (∑ p : Fin (s + 3), ∑ π : Equiv.Perm (Fin (s + 2)),
        ∑ U in admissibleCuts (s + 1), wordWeight (s + 1) U •
          germDiff (coordinateOne s) (coordinateUpperUnit p π U)) := by
  rw [germDiff_formula_eq_sum]
  change (∑ q : Equiv.Perm (Fin (s + 3)), ∑ U in admissibleCuts (s + 1),
    wordWeight (s + 1) U • germDiff (coordinateOne s)
      (caterpillarUnit (toR (vtx (q 0)))
        (fun i : Fin (s + 2) => toR (vtx (q i.succ))) U)) = _
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (insertZeroEquiv (s + 2))
  intro q
  rcases q with ⟨p, π⟩
  rfl

end MaxNN.Caterpillar
