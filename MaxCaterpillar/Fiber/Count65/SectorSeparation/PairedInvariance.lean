import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Separation
import MaxCaterpillar.Fiber.SymmetryHomeomorph

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

theorem pairedFirstMatrixForm_scaleFirst_forward (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) (h : PairedFirstMatrixForm net) :
    PairedFirstMatrixForm (scaleFirst net s) := by
  obtain ⟨a,b,d,e,hd,c,hc,p,q,hrows⟩ := h
  refine ⟨a,b,d,e,hd, (fun j => s j * c j), (fun j => mul_pos (hs j) (hc j)), p, q, ?_⟩
  intro j i
  change s j * net.W₁ j i = _
  rw [hrows, mul_assoc]

theorem pairedFirstMatrixForm_scaleFirst (net : Network 4 6 5)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j) :
    PairedFirstMatrixForm (scaleFirst net s) ↔ PairedFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := pairedFirstMatrixForm_scaleFirst_forward (scaleFirst net s)
      (fun j => (s j)⁻¹) (fun j => inv_pos.mpr (hs j)) h
    rwa [scaleFirst_inv_scaleFirst net s hs] at hinv
  · exact pairedFirstMatrixForm_scaleFirst_forward net s hs

theorem pairedFirstMatrixForm_scaleSecond (net : Network 4 6 5) (s : Fin 5 → ℝ) :
    PairedFirstMatrixForm (scaleSecond net s) ↔ PairedFirstMatrixForm net := Iff.rfl

theorem pairedFirstMatrixForm_permuteHidden_forward (net : Network 4 6 5)
    (p₀ : Equiv.Perm (Fin 6)) (q₀ : Equiv.Perm (Fin 5)) (h : PairedFirstMatrixForm net) :
    PairedFirstMatrixForm (permuteHidden net p₀ q₀) := by
  obtain ⟨a,b,d,e,hd,c,hc,p,q,hrows⟩ := h
  exact ⟨a,b,d,e,hd, (fun j => c (p₀ j)), (fun j => hc (p₀ j)), p₀.trans p, q,
    fun j i => hrows (p₀ j) i⟩

theorem pairedFirstMatrixForm_permuteHidden (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 5)) :
    PairedFirstMatrixForm (permuteHidden net p q) ↔ PairedFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := pairedFirstMatrixForm_permuteHidden_forward (permuteHidden net p q) p.symm q.symm h
    rwa [permuteHidden_inv_permuteHidden net p q] at hinv
  · exact pairedFirstMatrixForm_permuteHidden_forward net p q

theorem pairedFirstMatrixForm_permuteInputs_forward (net : Network 4 6 5)
    (q₀ : Equiv.Perm (Fin 4)) (h : PairedFirstMatrixForm net) :
    PairedFirstMatrixForm (permuteInputs net q₀) := by
  obtain ⟨a,b,d,e,hd,c,hc,p,q,hrows⟩ := h
  exact ⟨a,b,d,e,hd, c, hc, p, q₀.trans q, fun j i => hrows j (q₀ i)⟩

theorem pairedFirstMatrixForm_permuteInputs (net : Network 4 6 5)
    (p : Equiv.Perm (Fin 4)) :
    PairedFirstMatrixForm (permuteInputs net p) ↔ PairedFirstMatrixForm net := by
  constructor
  · intro h
    have hinv := pairedFirstMatrixForm_permuteInputs_forward (permuteInputs net p) p.symm h
    rwa [permuteInputs_inv_permuteInputs net p] at hinv
  · exact pairedFirstMatrixForm_permuteInputs_forward net p

theorem pairedFirstMatrixForm_of_symmetryStep {a b : ExactFiber 4 6 5}
    (h : SymmetryStep a b) : PairedFirstMatrixForm a.val ↔ PairedFirstMatrixForm b.val := by
  cases h with
  | first s hs => exact (pairedFirstMatrixForm_scaleFirst a.val s hs).symm
  | second s hs => exact (pairedFirstMatrixForm_scaleSecond a.val s).symm
  | hidden p q => exact (pairedFirstMatrixForm_permuteHidden a.val p q).symm
  | input p => exact (pairedFirstMatrixForm_permuteInputs a.val p).symm

theorem pairedFirstMatrixForm_of_symmetry {a b : ExactFiber 4 6 5}
    (h : EqvGen SymmetryStep a b) : PairedFirstMatrixForm a.val ↔ PairedFirstMatrixForm b.val := by
  induction h with
  | rel a b h => exact pairedFirstMatrixForm_of_symmetryStep h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc


end MaxCaterpillar.Fiber.Count65.SectorSeparation
