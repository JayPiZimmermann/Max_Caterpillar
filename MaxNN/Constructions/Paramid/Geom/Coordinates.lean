import MaxNN.Constructions.Paramid.Geom.Complete.Chart

/-! # Coordinates relating the standard simplex to `MAX` -/

namespace MaxNN.ParamidGeom.CoordAux

open BigOperators
open scoped Matrix

noncomputable section

/-- The coordinate change `(coordT n y)_i = y_{i+1} - y_0`. -/
def coordT (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℝ :=
  Matrix.of fun i => Pi.single i.succ 1 - Pi.single 0 1

theorem coordT_mulVec {n : ℕ} (y : Fin (n + 1) → ℝ) :
    (coordT n).mulVec y = fun i => y i.succ - y 0 := by
  funext i
  show MaxNN.dot (Pi.single i.succ 1 - Pi.single 0 1) y = y i.succ - y 0
  rw [SupportCut.dot_sub_left, CompleteAux.dot_single_left, CompleteAux.dot_single_left]

theorem dot_zero_left {m : ℕ} (y : Fin m → ℝ) : MaxNN.dot (0 : Fin m → ℝ) y = 0 := by
  show Matrix.dotProduct 0 y = 0
  exact Matrix.zero_dotProduct y

/-- `MAX` through the standard simplex. -/
theorem MAX_succ_eq_add_hS_simplexVerts {n : ℕ} (y : Fin (n + 1) → ℝ) :
    MaxNN.MAX (n + 1) y = y 0 + hS (simplexVerts n) ((coordT n).mulVec y) := by
  rw [coordT_mulVec]
  have hmem0 : (0 : Fin n → ℝ) ∈ simplexVerts n := Finset.mem_insert_self _ _
  have hmemk : ∀ k : Fin n, (Pi.single k 1 : Fin n → ℝ) ∈ simplexVerts n := fun k =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  apply le_antisymm
  · refine MaxNN.MAX_le fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · have h0 : (0 : ℝ) ≤ hS (simplexVerts n) (fun i : Fin n => y i.succ - y 0) := by
        have h := GermAux.dot_le_hS hmem0 (fun i : Fin n => y i.succ - y 0)
        rwa [dot_zero_left] at h
      linarith
    · have hk : y k.succ - y 0 ≤ hS (simplexVerts n) (fun i : Fin n => y i.succ - y 0) := by
        have h := GermAux.dot_le_hS (hmemk k) (fun i : Fin n => y i.succ - y 0)
        rwa [CompleteAux.dot_single_left] at h
      linarith
  · obtain ⟨p, hp, hpe⟩ :=
      GermAux.exists_mem_hS_eq ⟨0, hmem0⟩ (fun i : Fin n => y i.succ - y 0)
    rw [hpe]
    rcases Finset.mem_insert.mp hp with hp0 | hp'
    · have h : MaxNN.dot p (fun i : Fin n => y i.succ - y 0) = 0 := by
        rw [hp0]
        exact dot_zero_left _
      rw [h]
      linarith [MaxNN.le_MAX (n + 1) y 0]
    · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hp'
      have h : MaxNN.dot p (fun i : Fin n => y i.succ - y 0) = y k.succ - y 0 := by
        rw [← hk]
        exact CompleteAux.dot_single_left k _
      rw [h]
      linarith [MaxNN.le_MAX (n + 1) y k.succ]

/-- Reindex a sum over a finset by `Fin s.card`. -/
theorem sum_equivFin_symm {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∑ j : Fin s.card, f (s.equivFin.symm j).1 = ∑ p in s, f p :=
  (Equiv.sum_comp s.equivFin.symm (fun p : s => f p.1)).trans
    (Finset.sum_coe_sort (s := s) (f := f))

end

end MaxNN.ParamidGeom.CoordAux
