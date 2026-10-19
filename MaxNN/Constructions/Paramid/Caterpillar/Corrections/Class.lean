import MaxNN.Constructions.Paramid.Caterpillar.Corrections.FullDim

/-!
# From the caterpillar class identity to a finished network

The facet proof naturally concerns the original formula, which includes one
linear apex term per word.  Those terms lie in `LSpan 0`, so the class identity
passes to the cone sum used by the finite correction construction.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom MaxNN.Width

variable {r : ℕ}

/-- Class identity in the exact form produced by the facet calculation. -/
def FormulaClassIdentity (r : ℕ) : Prop :=
  formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r

private theorem formulaLinear_mem_LSpan_zero :
    (fun y => ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S * dot (rawApex π) y) ∈ LSpan (r + 1) 0 := by
  have he : (fun y => ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S * dot (rawApex π) y) =
      ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
        wordWeight r S • dot (rawApex π) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact Submodule.sum_mem _ fun π _ => Submodule.sum_mem _ fun S _ =>
    Submodule.smul_mem _ _ (FlagAux.dot_mem_LSpan (rawApex π) 0)

theorem coneClassIdentity_of_formulaClassIdentity
    (hclass : FormulaClassIdentity r) : CaterpillarClassIdentity r := by
  have hlin : (fun y => ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S * dot (rawApex π) y) ∈ LSpan (r + 1) r :=
    Sweep.LSpan_mono (Nat.zero_le r) formulaLinear_mem_LSpan_zero
  have hsub := Submodule.sub_mem (LSpan (r + 1) r) hclass hlin
  unfold FormulaClassIdentity at hclass
  unfold CaterpillarClassIdentity
  rw [formula_eq_coneFormula_add_linear] at hsub
  convert hsub using 1
  abel

/-- Compiles the formula class identity into an ordinary two-hidden-layer
network. The global facet proof supplies this identity, and full dimensionality
is proved internally. -/
theorem twoLayerWidth_MAX_of_formulaClassIdentity (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1)) ((correctionKeys r).card + 2)
      (MAX (r + 1 + 1)) :=
  twoLayerWidth_MAX_of_classIdentity hr (fullDimensionalWords r)
    (coneClassIdentity_of_formulaClassIdentity hclass)

/-- A closed raw-word upper bound on the second width.  The actual dictionary
is deduplicated and can be strictly smaller. -/
theorem twoLayerWidth_MAX_raw_bound (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      (Fintype.card (WordIndex r) * 3 ^ r + 2) (MAX (r + 1 + 1)) := by
  apply TwoLayerWidth.mono_right (twoLayerWidth_MAX_of_formulaClassIdentity hr hclass)
  exact Nat.add_le_add_right card_correctionKeys_le 2

/-- The sharper count first identifies equal full-dimensional caterpillar
cones and only then expands their faces. -/
theorem twoLayerWidth_MAX_distinctCone_bound (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      ((wordCones r).card * 3 ^ r + 2) (MAX (r + 1 + 1)) := by
  apply TwoLayerWidth.mono_right (twoLayerWidth_MAX_of_formulaClassIdentity hr hclass)
  exact Nat.add_le_add_right card_correctionKeys_le_distinct 2

end MaxNN.Caterpillar.Corrections
