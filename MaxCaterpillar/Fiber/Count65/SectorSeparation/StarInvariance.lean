import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Separation
import MaxCaterpillar.Fiber.SymmetryHomeomorph

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

theorem starFirstMatrixForm_scaleFirst_forward (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) (h : StarFirstMatrixForm net) :
    StarFirstMatrixForm (scaleFirst net s) := by
  obtain ⟨t, ht, ht1, c, hc, p, q, hrows⟩ := h
  refine ⟨t, ht, ht1, (fun j => s j * c j), (fun j => mul_pos (hs j) (hc j)), p, q, ?_⟩
  intro j i
  change s j * net.W₁ j i = _
  rw [hrows, mul_assoc]

theorem starFirstMatrixForm_scaleFirst (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) :
    StarFirstMatrixForm (scaleFirst net s) ↔ StarFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := starFirstMatrixForm_scaleFirst_forward (scaleFirst net s)
      (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j)) h
    rwa [scaleFirst_inv_scaleFirst net s hs] at hinv
  · exact starFirstMatrixForm_scaleFirst_forward net s hs

theorem starFirstMatrixForm_scaleSecond (net : Network 4 6 5) (s : Fin 5 → ℝ) :
    StarFirstMatrixForm (scaleSecond net s) ↔ StarFirstMatrixForm net := Iff.rfl

theorem starFirstMatrixForm_permuteHidden_forward (net : Network 4 6 5)
    (p₀ : Equiv.Perm (Fin 6)) (q₀ : Equiv.Perm (Fin 5)) (h : StarFirstMatrixForm net) :
    StarFirstMatrixForm (permuteHidden net p₀ q₀) := by
  obtain ⟨t, ht, ht1, c, hc, p, q, hrows⟩ := h
  exact ⟨t, ht, ht1, (fun j => c (p₀ j)), (fun j => hc (p₀ j)), p₀.trans p, q,
    fun j i => hrows (p₀ j) i⟩

theorem starFirstMatrixForm_permuteHidden (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 5)) :
    StarFirstMatrixForm (permuteHidden net p q) ↔ StarFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := starFirstMatrixForm_permuteHidden_forward (permuteHidden net p q) p.symm q.symm h
    rwa [permuteHidden_inv_permuteHidden net p q] at hinv
  · exact starFirstMatrixForm_permuteHidden_forward net p q

theorem starFirstMatrixForm_permuteInputs_forward (net : Network 4 6 5)
    (q₀ : Equiv.Perm (Fin 4)) (h : StarFirstMatrixForm net) :
    StarFirstMatrixForm (permuteInputs net q₀) := by
  obtain ⟨t, ht, ht1, c, hc, p, q, hrows⟩ := h
  exact ⟨t, ht, ht1, c, hc, p, q₀.trans q, fun j i => hrows j (q₀ i)⟩

theorem starFirstMatrixForm_permuteInputs (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 4)) :
    StarFirstMatrixForm (permuteInputs net p) ↔ StarFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := starFirstMatrixForm_permuteInputs_forward (permuteInputs net p) p.symm h
    rwa [permuteInputs_inv_permuteInputs net p] at hinv
  · exact starFirstMatrixForm_permuteInputs_forward net p

theorem starFirstMatrixForm_of_symmetryStep {a b : ExactFiber 4 6 5}
    (h : SymmetryStep a b) : StarFirstMatrixForm a.val ↔ StarFirstMatrixForm b.val := by
  cases h with
  | first s hs => exact (starFirstMatrixForm_scaleFirst a.val s hs).symm
  | second s hs => exact (starFirstMatrixForm_scaleSecond a.val s).symm
  | hidden p q => exact (starFirstMatrixForm_permuteHidden a.val p q).symm
  | input p => exact (starFirstMatrixForm_permuteInputs a.val p).symm

theorem starFirstMatrixForm_of_symmetry {a b : ExactFiber 4 6 5}
    (h : EqvGen SymmetryStep a b) : StarFirstMatrixForm a.val ↔ StarFirstMatrixForm b.val := by
  induction h with
  | rel a b h => exact starFirstMatrixForm_of_symmetryStep h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc


end MaxCaterpillar.Fiber.Count65.SectorSeparation
