import MaxCaterpillar.Fiber.First65.LocalMixed

/-! # Explicit finite witnesses for the mixed local certificate

All inequalities are checked for the actual first-row matrix.  These
witnesses show that the open certificate is nonvacuous at every positive
mixed parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators Frontier

theorem localCertificate_firstRows (t : ℝ) (ht : 0 < t) :
    LocalCertificate t (firstRows t) := by
  constructor
  · norm_num [firstRows]
  · norm_num [firstRows]
  · norm_num [firstRows]
  · simpa [firstRows] using ht
  · change (0 : ℝ) < 1
    norm_num
  · change (0 : ℝ) < 1
    norm_num
  · change (-1 : ℝ) < 0
    norm_num
  all_goals
    intro j hj
    fin_cases j <;> try { exact False.elim (hj (by decide)) }
    all_goals
      norm_num [firstRows, lin, Fin.sum_univ_succ, carrierPlusPoint,
        carrierMinusPoint, bPoint, cPoint, qPoint, tPoint, bTiePlus,
        bTieMinus, cTiePlus, cTieMinus] at hj ⊢ <;>
      nlinarith only [ht]

theorem carrierPlusPoint_winner (t : ℝ) (ht : 0 < t) :
    carrierPlusPoint t 2 = Maximum 4 (carrierPlusPoint t) := by
  symm
  apply Maximum_eq_of _ _ 2 rfl
  intro i
  fin_cases i <;> norm_num [carrierPlusPoint] <;> linarith only [ht]

theorem carrierMinusPoint_winner (t : ℝ) (ht : 0 < t) :
    carrierMinusPoint t 2 = Maximum 4 (carrierMinusPoint t) := by
  symm
  apply Maximum_eq_of _ _ 2 rfl
  intro i
  fin_cases i <;> norm_num [carrierMinusPoint] <;> linarith only [ht]

theorem bPoint_winner : bPoint 1 = Maximum 4 bPoint := by
  symm
  apply Maximum_eq_of _ _ 1 rfl
  intro i
  fin_cases i <;> norm_num [bPoint]

theorem cPoint_winner (t : ℝ) (ht : 0 < t) :
    cPoint t 3 = Maximum 4 (cPoint t) := by
  symm
  apply Maximum_eq_of _ _ 3 rfl
  intro i
  fin_cases i <;> norm_num [cPoint] <;> linarith only [ht]

theorem qPoint_winner (t : ℝ) (ht : 0 < t) :
    qPoint t 0 = Maximum 4 (qPoint t) := by
  symm
  apply Maximum_eq_of _ _ 0 rfl
  intro i
  fin_cases i <;> norm_num [qPoint] <;> linarith only [ht]

theorem tPoint_winner : tPoint 0 = Maximum 4 tPoint := by
  symm
  apply Maximum_eq_of _ _ 0 rfl
  intro i
  fin_cases i <;> norm_num [tPoint]

theorem bTiePlus_winner : bTiePlus 1 = Maximum 4 bTiePlus := by
  symm
  apply Maximum_eq_of _ _ 1 rfl
  intro i
  fin_cases i <;> norm_num [bTiePlus]

theorem bTieMinus_winner : bTieMinus 1 = Maximum 4 bTieMinus := by
  symm
  apply Maximum_eq_of _ _ 1 rfl
  intro i
  fin_cases i <;> norm_num [bTieMinus]

theorem cTiePlus_winner (t : ℝ) (ht : 0 < t) :
    cTiePlus t 3 = Maximum 4 (cTiePlus t) := by
  symm
  apply Maximum_eq_of _ _ 3 rfl
  intro i
  fin_cases i <;> norm_num [cTiePlus] <;> linarith only [ht]

theorem cTieMinus_winner (t : ℝ) (ht : 0 < t) :
    cTieMinus t 3 = Maximum 4 (cTieMinus t) := by
  symm
  apply Maximum_eq_of _ _ 3 rfl
  intro i
  fin_cases i <;> norm_num [cTieMinus] <;> linarith only [ht]

end MaxCaterpillar.Fiber.Mixed65
