import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Class

/-!
# Coefficient-complete correction tables

`CorrectionTable` contains the actual output coefficients and the actual
pair-feature remainder.  Supplying such a table yields the network theorem
without extracting correction coefficients from a span proof.  The separate
existence theorem below records exactly what Theorem F currently provides; it
is intentionally not named or advertised as a closed coefficient formula.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open MaxNN.Width

variable {r : ℕ}

/-- Concrete coefficients for the fixed finite correction dictionary. -/
structure CorrectionTable (r : ℕ) where
  coeff : RealKey (r + 1) → ℝ
  remainder : (Fin (r + 1 + 1) → ℝ) → ℝ
  remainder_pairLin : remainder ∈ PairLin (r + 1 + 1)
  computes : ∀ y, MAX (r + 1 + 1) y =
    ∑ k in correctionKeys r, coeff k * realUnitY k y + remainder y

/-- The function written by a concrete table. -/
noncomputable def CorrectionTable.eval (T : CorrectionTable r) :
    (Fin (r + 1 + 1) → ℝ) → ℝ :=
  fun y => ∑ k in correctionKeys r, T.coeff k * realUnitY k y + T.remainder y

theorem CorrectionTable.eval_eq_MAX (T : CorrectionTable r) :
    T.eval = MAX (r + 1 + 1) := by
  funext y
  exact (T.computes y).symm

/-- A supplied coefficient table gives the ordinary network with the exact
deduplicated second width.  No correction coefficient is selected in this
theorem. -/
theorem CorrectionTable.twoLayerWidth (T : CorrectionTable r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) ((correctionKeys r).card + 2)
      (MAX (r + 1 + 1)) := by
  have hmem : MAX (r + 1 + 1) ∈ RealUnitSpan (r + 1) (correctionKeys r) :=
    ⟨T.coeff, T.remainder, T.remainder_pairLin, T.computes⟩
  exact twoLayerWidth_of_mem_realUnitSpan correctionKeys_simplexDifference hmem

/-- What the present Theorem-F route proves about coefficients: a concrete
finite table exists.  This is a logical existence theorem, not a closed table
definition. -/
theorem exists_correctionTable_of_formulaClassIdentity (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) : Nonempty (CorrectionTable r) := by
  have hΔ := simplex_mem_correctionSpan hr (fullDimensionalWords r)
    (coneClassIdentity_of_formulaClassIdentity hclass)
  have hmax : MAX (r + 1 + 1) ∈ RealUnitSpan (r + 1) (correctionKeys r) := by
    have he : MAX (r + 1 + 1) = (fun y => y 0) +
        MaxNN.Width.coordPull (r + 1) (ParamidGeom.hS (ParamidGeom.simplexVerts (r + 1))) := by
      funext y
      exact ParamidGeom.CoordAux.MAX_succ_eq_add_hS_simplexVerts y
    rw [he]
    exact Submodule.add_mem _ (pairLin_mem_realUnitSpan (coord_mem_pairLin 0))
      (Submodule.mem_comap.mp hΔ)
  obtain ⟨c, q, hq, hcompute⟩ := hmax
  exact ⟨⟨c, q, hq, hcompute⟩⟩

end MaxNN.Caterpillar.Corrections
