import MaxCaterpillar.Fiber.Mixed65.BoundaryRows
import MaxCaterpillar.Fiber.Mixed65.BoundaryCoefficients
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! # Finite-boundary closure of the actual mixed sector

The row equations and first-width-six irredundancy exclude every limiting
boundary except `mixedA = 0`. A quantitative physical coefficient bound excludes
that boundary by continuity. The coefficient bound is kept as an explicit
mathematical hypothesis; no residual classification or divergence theorem is
silently assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Fiber.Mixed65

variable {h₂ : ℕ}

/-- A continuously read size bound in original, unnormalized parameters. -/
noncomputable def physicalCoefficientSize (net : Network 4 6 h₂) : ℝ :=
  scaledCoefficientSize net (rowScale net)

theorem continuous_physicalCoefficientSize :
    Continuous (physicalCoefficientSize (h₂ := h₂)) :=
  continuous_scaledCoefficientSize continuous_id continuous_rowScale

/-- Every positively scaled mixed first matrix belongs to the closed coordinate wedge. -/
theorem closedRows_of_scaled_firstRows (net : Network 4 6 h₂) {t : ℝ} (ht : 0 < t)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (hrows : net.W₁ = fun j i => s j * firstRows t j i) : ClosedRows net := by
  have hscale := rowScale_of_scaled_firstRows net t s hrows
  have ha : mixedA net = s 3 * t := by
    change net.W₁ 3 0 = s 3 * t
    rw [hrows]
    rfl
  have hb : mixedB net = s 3 := by
    change net.W₁ 3 2 = s 3
    rw [hrows]
    change s 3 * 1 = s 3
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hscale]
    exact (hs j).le
  · change 0 ≤ net.W₁ 3 0
    rw [hrows]
    change 0 ≤ s 3 * t
    exact (mul_pos (hs 3) ht).le
  · funext j i
    rw [hrows]
    fin_cases j <;> fin_cases i <;>
      norm_num [closedRowsTemplate, ha, hb, hscale, hrows, firstRows,
        Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals try rfl
    all_goals try exact Or.inl rfl
    all_goals change s 3 * (-1 + -t) = -(s 3 * t) - s 3
    all_goals ring

theorem labeledScaledSector_subset_closedRows :
    labeledScaledSector ⊆ {net : ExactFiber 4 6 5 | ClosedRows net.val} := by
  rintro net ⟨t, ht, s, hs, hrows⟩
  exact closedRows_of_scaled_firstRows net.val ht s hs hrows

/-- The divergence bound in normalized coordinates implies a closed inequality
in the actual finite parameter coordinates. -/
theorem labeledScaledSector_coefficient_bound (hbound : NormalizedCoefficientBound)
    (net : ExactFiber 4 6 5) (hn : net ∈ labeledScaledSector) :
    mixedB net.val ≤ mixedA net.val * physicalCoefficientSize net.val := by
  obtain ⟨t, ht, s, hs, hrows⟩ := hn
  have h := normalizedCoefficientBound_cleared hbound net ht s hs hrows
  change net.val.W₁ 3 2 ≤ net.val.W₁ 3 0 *
    scaledCoefficientSize net.val (rowScale net.val)
  rw [rowScale_of_scaled_firstRows net.val t s hrows]
  exact h

/-- The finite-parameter inequality is closed, so it persists at every point
in the closure, without choosing subsequences or fixing a suffix normal form. -/
theorem closure_labeledScaledSector_coefficient_bound (hbound : NormalizedCoefficientBound)
    (net : ExactFiber 4 6 5) (hn : net ∈ closure labeledScaledSector) :
    mixedB net.val ≤ mixedA net.val * physicalCoefficientSize net.val := by
  have hclosed : IsClosed {net : ExactFiber 4 6 5 |
      mixedB net.val ≤ mixedA net.val * physicalCoefficientSize net.val} :=
    isClosed_le (continuous_mixedB.comp continuous_subtype_val)
      ((continuous_mixedA.comp continuous_subtype_val).mul
        (continuous_physicalCoefficientSize.comp continuous_subtype_val))
  exact closure_minimal (fun n hn => labeledScaledSector_coefficient_bound hbound n hn)
    hclosed hn

/-- Quantitative divergence and first-layer irredundancy exclude all finite
boundary points of the labeled scaled mixed family. -/
theorem isClosed_labeledScaledSector_of_coefficient_bound (hbound : NormalizedCoefficientBound) :
    IsClosed labeledScaledSector := by
  apply isClosed_of_closure_subset
  intro net hn
  have hrows : ClosedRows net.val :=
    closure_minimal labeledScaledSector_subset_closedRows isClosed_closedRows_exactFiber hn
  have hb : 0 < mixedB net.val := closedRows_b_pos net.val net.property hrows
  have hineq := closure_labeledScaledSector_coefficient_bound hbound net hn
  have ha : 0 < mixedA net.val := by
    by_contra hna
    have ha0 : mixedA net.val = 0 :=
      le_antisymm (le_of_not_gt hna) (closedRows_a_nonneg net.val hrows)
    rw [ha0, zero_mul] at hineq
    exact (not_le_of_gt hb) hineq
  obtain ⟨ht, hs, hw⟩ := closedRows_pos_scaled net.val net.property hrows ha
  exact ⟨mixedA net.val / mixedB net.val, ht, rowScale net.val, hs, hw⟩

/-- The same closure theorem holds after restoring every permitted symmetry,
because only finitely many input and first-neuron permutations remain. -/
theorem isClosed_sector_of_coefficient_bound (hbound : NormalizedCoefficientBound) :
    IsClosed sector :=
  isClosed_sector_of_labeledScaledSector
    (isClosed_labeledScaledSector_of_coefficient_bound hbound)

end MaxCaterpillar.Fiber.Mixed65
