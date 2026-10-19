import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Base
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.LinearCombination

/-! # The structured part of the coordinate-facet sum -/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom

variable {s : ℕ}

def coordinateOne (s : ℕ) : Fin (s + 2) → ℝ := fun _ => 1

def coordinateVertex {s : ℕ} (a : Fin (s + 2)) : Fin (s + 2) → ℝ :=
  Pi.single a 1

noncomputable def coordinateA (π : Equiv.Perm (Fin (s + 2))) :
    Fin (s + 1) → Fin (s + 2) → ℝ :=
  fun i => coordinateVertex (π i.succ)

noncomputable def coordinateLowerUnit (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) : (Fin (s + 2) → ℝ) → ℝ :=
  caterpillarUnit (coordinateVertex (π 0)) (coordinateA π) S

noncomputable def coordinatePendantUnit (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) (i : Fin (s + 1)) : (Fin (s + 2) → ℝ) → ℝ :=
  caterpillarUnit (coordinateVertex (π 0))
    (insertPendantWord i 0 (coordinateA π)) (insertPendantCuts i S)

noncomputable def coordinateFirstUnit (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) : (Fin (s + 2) → ℝ) → ℝ :=
  caterpillarUnit (r := 1 + s) (coordinateVertex (π 0))
    (Fin.append (m := 1) (n := s + 1) (fun _ => 0) (coordinateA π))
    (joinCuts (∅ : Finset (Fin 1)) S)

noncomputable def coordinateLastUnit (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) : (Fin (s + 2) → ℝ) → ℝ :=
  caterpillarUnit (r := s + 1) (coordinateVertex (π 0))
    (Fin.append (m := s + 1) (n := 1) (coordinateA π) (fun _ => 0))
    (joinCuts S (∅ : Finset (Fin 1)))

@[simp] theorem dot_coordinateVertex_one (a : Fin (s + 2)) :
    dot (coordinateVertex a) (coordinateOne s) = 1 := by
  simp [coordinateVertex, coordinateOne, dot]

@[simp] theorem dot_zero_coordinateOne :
    dot (0 : Fin (s + 2) → ℝ) (coordinateOne s) = 0 := by
  simp [dot]

theorem zero_not_mem_of_admissible {S : Finset (Fin (s + 1))}
    (hS : S ∈ admissibleCuts s) : (0 : Fin (s + 1)) ∉ S := by
  have hsub : S ⊆ cutPositions s :=
    Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
  intro h0
  exact (Finset.mem_erase.mp (hsub h0)).1 rfl

theorem coordinateLowerUnit_eq_valueUnit (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) (y : Fin (s + 2) → ℝ) :
    coordinateLowerUnit π S y = valueUnit y π S := by
  unfold coordinateLowerUnit coordinateA coordinateVertex valueUnit caterpillarUnit values
  simp only [ParamidGeom.CompleteAux.dot_single_left]

/-- The `s+3` deletion terms belonging to one lower decorated word have total
coefficient one, modulo segment support functions. -/
theorem coordinateStructuredBlock_sub_lower_mem_LSpan_one
    (π : Equiv.Perm (Fin (s + 2))) (S : Finset (Fin (s + 1)))
    (hS : S ∈ admissibleCuts s) :
    ((∑ i : Fin (s + 1), wordWeight (s + 1) (insertPendantCuts i S) •
          germDiff (coordinateOne s) (coordinatePendantUnit π S i)) +
        wordWeight (1 + s) (joinCuts (∅ : Finset (Fin 1)) S) •
          germDiff (coordinateOne s) (coordinateFirstUnit π S) +
        wordWeight (s + 1) (joinCuts S (∅ : Finset (Fin 1))) •
          germDiff (coordinateOne s) (coordinateLastUnit π S)) -
      wordWeight s S • coordinateLowerUnit π S ∈ LSpan (s + 2) 1 := by
  let c : ℝ := (s + 3 : ℝ)⁻¹
  let w : ℝ := wordWeight s S
  have ha : dot (coordinateVertex (π 0)) (coordinateOne s) = 1 :=
    dot_coordinateVertex_one _
  have hA : ∀ q, dot (coordinateA π q) (coordinateOne s) = 1 := by
    intro q
    exact dot_coordinateVertex_one _
  have hb : dot (0 : Fin (s + 2) → ℝ) (coordinateOne s) = 0 :=
    dot_zero_coordinateOne
  have hp (i : Fin (s + 1)) :
      germDiff (coordinateOne s) (coordinatePendantUnit π S i) +
        coordinateLowerUnit π S ∈ LSpan (s + 2) 1 := by
    exact germDiff_insertPendant_add_lower_mem_LSpan_one i
      (coordinateVertex (π 0)) 0 (coordinateA π) S (coordinateOne s) ha hb hA
  have hf : germDiff (coordinateOne s) (coordinateFirstUnit π S) -
      coordinateLowerUnit π S ∈ LSpan (s + 2) 1 := by
    exact germDiff_firstEndpoint_sub_lower_mem_LSpan_one
      (coordinateVertex (π 0)) 0 (coordinateA π) S (coordinateOne s) ha hb hA
  have hl : germDiff (coordinateOne s) (coordinateLastUnit π S) -
      coordinateLowerUnit π S ∈ LSpan (s + 2) 1 := by
    exact germDiff_lastEndpoint_sub_lower_mem_LSpan_one
      (coordinateVertex (π 0)) (coordinateA π) 0 S (coordinateOne s) ha hA hb
  have hsum : (∑ i : Fin (s + 1),
      (wordWeight (s + 1) (insertPendantCuts i S) •
          germDiff (coordinateOne s) (coordinatePendantUnit π S i) -
        (c * w) • coordinateLowerUnit π S)) +
      (wordWeight (1 + s) (joinCuts (∅ : Finset (Fin 1)) S) •
          germDiff (coordinateOne s) (coordinateFirstUnit π S) -
        (c * w) • coordinateLowerUnit π S) +
      (wordWeight (s + 1) (joinCuts S (∅ : Finset (Fin 1))) •
          germDiff (coordinateOne s) (coordinateLastUnit π S) -
        (c * w) • coordinateLowerUnit π S) ∈ LSpan (s + 2) 1 := by
    apply Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ ?_) ?_) ?_
    · intro i _
      apply smul_sub_smul_mem_of_eq_neg _ (hp i)
      rw [wordWeight_insertPendantCuts]
      simp only [c, w]
      ring
    · apply smul_sub_smul_mem_of_eq _ hf
      rw [wordWeight_firstEndpointCuts S (zero_not_mem_of_admissible hS)]
    · apply smul_sub_smul_mem_of_eq _ hl
      rw [wordWeight_lastEndpointCuts]
  convert hsum using 1
  funext y
  simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  field_simp
  ring

noncomputable def coordinateStructuredBlock (π : Equiv.Perm (Fin (s + 2)))
    (S : Finset (Fin (s + 1))) : (Fin (s + 2) → ℝ) → ℝ :=
  (∑ i : Fin (s + 1), wordWeight (s + 1) (insertPendantCuts i S) •
      germDiff (coordinateOne s) (coordinatePendantUnit π S i)) +
    wordWeight (1 + s) (joinCuts (∅ : Finset (Fin 1)) S) •
      germDiff (coordinateOne s) (coordinateFirstUnit π S) +
    wordWeight (s + 1) (joinCuts S (∅ : Finset (Fin 1))) •
      germDiff (coordinateOne s) (coordinateLastUnit π S)

noncomputable def coordinateStructuredSum (s : ℕ) : (Fin (s + 2) → ℝ) → ℝ :=
  ∑ π : Equiv.Perm (Fin (s + 2)),
    ∑ S in admissibleCuts s, coordinateStructuredBlock π S

theorem coordinateStructuredBlock_sub_lower_mem_LSpan_one'
    (π : Equiv.Perm (Fin (s + 2))) (S : Finset (Fin (s + 1)))
    (hS : S ∈ admissibleCuts s) :
    coordinateStructuredBlock π S - wordWeight s S • coordinateLowerUnit π S ∈
      LSpan (s + 2) 1 := by
  exact coordinateStructuredBlock_sub_lower_mem_LSpan_one π S hS

theorem coordinateLowerSum_eq_valueFormula :
    (∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
      wordWeight s S • coordinateLowerUnit π S) = valueFormula s := by
  funext y
  unfold valueFormula
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro S _
  rw [coordinateLowerUnit_eq_valueUnit]

/-- Once the upper coordinate facet has been reduced to the structured
deletion family, all `s+3` copies combine to the actual lower formula. -/
theorem coordinateStructuredSum_sub_valueFormula_mem_LSpan (hs : 1 ≤ s) :
    coordinateStructuredSum s - valueFormula s ∈ LSpan (s + 2) s := by
  have hsmall : (∑ π : Equiv.Perm (Fin (s + 2)), ∑ S in admissibleCuts s,
      (coordinateStructuredBlock π S - wordWeight s S • coordinateLowerUnit π S)) ∈
      LSpan (s + 2) 1 :=
    Submodule.sum_mem _ fun π _ => Submodule.sum_mem _ fun S hS =>
      coordinateStructuredBlock_sub_lower_mem_LSpan_one' π S hS
  have hmono := DoublingAux.LSpan_mono hs hsmall
  rw [← coordinateLowerSum_eq_valueFormula]
  unfold coordinateStructuredSum
  simpa only [Finset.sum_sub_distrib] using hmono

end MaxNN.Caterpillar
