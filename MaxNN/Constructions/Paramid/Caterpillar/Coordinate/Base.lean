import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Permutations
import MaxNN.Constructions.Paramid.Geom.SimplexMod

/-! # The three-vertex base case -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

theorem admissibleCuts_one : admissibleCuts 1 = {{1}} := by
  ext S
  constructor
  · intro hS
    have hne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hsub : S ⊆ cutPositions 1 := Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    have hzero : (0 : Fin 2) ∉ S := by
      intro h0
      exact (Finset.mem_erase.mp (hsub h0)).1 rfl
    have hone : (1 : Fin 2) ∈ S := by
      by_contra h1
      apply hne
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i
      fin_cases i
      · exact hzero
      · exact h1
    exact Finset.mem_singleton.mpr (Finset.Subset.antisymm
      (fun i hi => by fin_cases i <;> simp_all) (Finset.singleton_subset_iff.mpr hone))
  · intro hS
    rw [Finset.mem_singleton.mp hS]
    simp [admissibleCuts, cutPositions]

theorem baseMax_fin_two_singleton (w : Fin 2 → ℝ) :
    baseMax w ({1} : Finset (Fin 2)) = max (w 0) (w 1) := by
  have hlast : lastHead ({1} : Finset (Fin 2)) = 1 := by
    apply le_antisymm
    · exact Fin.le_last _
    · exact Finset.le_max' _ 1 (by simp)
  unfold baseMax pointedMax treeMax
  rw [Fin.sum_univ_one, Fin.sum_univ_two, hlast]
  have hparent : parent ({1} : Finset (Fin 2)) (0 : Fin 1).succ = 0 := by
    have hp := parent_lt (S := ({1} : Finset (Fin 2)))
      (show (0 : Fin 2) < (0 : Fin 1).succ from Fin.succ_pos 0)
    apply Fin.ext
    change (parent ({1} : Finset (Fin 2)) (0 : Fin 1).succ).val = 0
    change (parent ({1} : Finset (Fin 2)) (0 : Fin 1).succ).val < 1 at hp
    omega
  have hsucc : (0 : Fin 1).succ = (1 : Fin 2) := rfl
  rw [hparent, hsucc]
  ring

theorem wordWeight_one_singleton :
    wordWeight 1 ({1} : Finset (Fin 2)) = (6 : ℝ)⁻¹ := by
  unfold wordWeight
  rw [show Nat.factorial 3 = 6 by decide]
  rw [Finset.card_singleton]
  norm_num

theorem max_three_comp_perm (x : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3)) :
    max (x (π 0)) (max (x (π 1)) (x (π 2))) =
      max (x 0) (max (x 1) (x 2)) := by
  have hperm : MaxNN.MAX 3 (fun i => x (π i)) = MaxNN.MAX 3 x := by
    apply le_antisymm
    · exact MaxNN.MAX_le fun i => MaxNN.le_MAX 3 x (π i)
    · exact MaxNN.MAX_le fun i => by
        have h := MaxNN.le_MAX 3 (fun j => x (π j)) (π.symm i)
        simpa using h
  have hexpand (z : Fin 3 → ℝ) :
      MaxNN.MAX 3 z = max (z 0) (max (z 1) (z 2)) := by
    rw [MaxNN.MAX_succ 2, MaxNN.MAX_two]
    change max (max (z 0) (z 1)) (z 2) = _
    exact max_assoc _ _ _
  rw [hexpand, hexpand] at hperm
  exact hperm

theorem valueUnit_one (x : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3)) :
    valueUnit x π ({1} : Finset (Fin 2)) = max (x 0) (max (x 1) (x 2)) := by
  unfold valueUnit
  rw [baseMax_fin_two_singleton]
  exact max_three_comp_perm x π

theorem valueFormula_one (x : Fin 3 → ℝ) :
    valueFormula 1 x = max (x 0) (max (x 1) (x 2)) := by
  unfold valueFormula
  change (∑ π : Equiv.Perm (Fin 3), ∑ S in admissibleCuts 1,
    wordWeight 1 S * valueUnit x π S) = _
  rw [admissibleCuts_one]
  simp only [Finset.sum_singleton]
  let M := max (x 0) (max (x 1) (x 2))
  have hsum : (∑ π : Equiv.Perm (Fin 3),
      wordWeight 1 ({1} : Finset (Fin 2)) * valueUnit x π ({1} : Finset (Fin 2))) =
      ∑ _π : Equiv.Perm (Fin 3), (6 : ℝ)⁻¹ * M := by
    apply Finset.sum_congr rfl
    intro π _
    rw [wordWeight_one_singleton, valueUnit_one]
  rw [hsum]
  change (∑ _π in (Finset.univ : Finset (Equiv.Perm (Fin 3))), (6 : ℝ)⁻¹ * M) = M
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [show Nat.factorial 3 = 6 by decide]
  ring

theorem formula_one_eq_simplex : formula 1 = hS (simplexVerts 2) := by
  funext y
  rw [formula, valueFormula_one, simplexValues_zero]
  have h1 : simplexValues y (1 : Fin 3) = y 0 := simplexValues_succ y 0
  have h2 : simplexValues y (2 : Fin 3) = y 1 := simplexValues_succ y 1
  rw [h1, h2]
  exact (ParamidGeom.KuhnRhoAux.hS_simplexVerts_two y).symm

end MaxNN.Caterpillar
