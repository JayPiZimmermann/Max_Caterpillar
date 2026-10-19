import MaxCaterpillar.Construction

/-! # The proof in reusable steps

The order follows the paper: reduce facet data to one coordinate direction,
delete that coordinate, recover the simplex class, expand in the finite
dictionary, and compile any improved cone count into a complete width bound.
Only the first two reduction lemmas have conditional geometric hypotheses.
The class identity, dictionary membership, and expansion have none beyond
`1 ≤ r`. The nonrecursive construction data is in `Construction`.
-/

open BigOperators

namespace MaxCaterpillar

open MaxNN MaxNN.Caterpillar MaxNN.ParamidGeom

-- The dictionary inner product integrates against Haar measure on `Point N`.
attribute [local instance] Corrections.Canonical.functionMeasureSpace
  Corrections.Canonical.functionIsAddHaarMeasure

/-- Noncoordinate cancellation and symmetry reduce all facets to one. -/
theorem facet_reduction {r : ℕ} (hr : 2 ≤ r)
    (h : germDiff (fun _ : Fin (r + 1) => (1 : ℝ))
      (formula r - hS (simplexVerts (r + 1))) ∈ LSpan (r + 1) (r - 1))
    (u : Fin (r + 1) → ℝ) :
    germDiff u (formula r - hS (simplexVerts (r + 1))) ∈
      LSpan (r + 1) (r - 1) :=
  germDiff_coordinateResidual_mem_LSpan_of_canonical hr h u

/-- Matching facet data suffices for this particular finite formula. -/
theorem facet_completeness {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ u, germDiff u (formula r - hS (simplexVerts (r + 1))) ∈
      LSpan (r + 1) (r - 1)) :
    formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r :=
  formula_sub_simplex_mem_LSpan_of_germDiff hr h

/-- Deletion has `N` insertion preimages; the empty-cut star remainder
is already included in this unconditional recurrence. -/
theorem coordinate_deletion {s : ℕ} (hs : 1 ≤ s) :
    germDiff (coordinateOne s) (formula (s + 1)) - valueFormula s ∈
      LSpan (s + 2) s :=
  germDiff_formula_coordinate_sub_valueFormula_mem_LSpan hs

/-- The finite caterpillar sum equals the simplex class, not its function.
The proof of this statement uses induction on `r`. -/
theorem class_identity (r : ℕ) (hr : 1 ≤ r) :
    formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r :=
  formula_sub_simplex_mem_LSpan r hr

/-- Face elimination supplies all corrections; no class identity remains
as a hypothesis of this dictionary statement. -/
theorem maximum_mem_dictionary (r : ℕ) (hr : 1 ≤ r) :
    Maximum (r + 1 + 1) ∈ Submodule.span ℝ
      (↑(dictionary r) : Set (Point (r + 1 + 1) → ℝ)) :=
  Corrections.Canonical.MAX_mem_atomSpan r hr (class_identity r hr)

/-- The literal coefficient rule reconstructs MAX pointwise. -/
theorem canonical_expansion (r : ℕ) (hr : 1 ≤ r) (x : Point (r + 1 + 1)) :
    ∑ i : Atom r, coefficient r i * atom r i x = Maximum (r + 1 + 1) x :=
  Corrections.Canonical.sum_taggedCoeff_eq (atom r)
    (Corrections.Canonical.atomFunction_posHomContinuous r) (maximum_mem_dictionary r hr) x

/-- Forget leaf order and identify a spine with its reversal. -/
theorem normalized_cone_count (r : ℕ) :
    (Corrections.normalizedWordCones r).card ≤ coneCount (r + 1 + 1) :=
  Internal.coneCount_eq_spineConeBound _ ▸ Corrections.card_normalizedWordCones_le_spine r

/-- A reusable compiler bound: improve only the cone count `b` to improve
the complete second width. Face corrections and remainder units are included. -/
theorem width_of_cone_count (r b : ℕ) (hr : 1 ≤ r)
    (hb : (Corrections.normalizedWordCones r).card ≤ b) :
    ∃ net : Network (r + 1 + 1) (firstWidth (r + 1 + 1))
      (b * 3 ^ r - (r + 1 + 1) * (r + 1) + 2),
      ∀ x, net.eval x = Maximum (r + 1 + 1) x :=
  Internal.twoLayerWidth_iff.mp (compactEssential_twoLayerWidth_of_cone_bound r b hr hb)

/-- `secondWidth (r + 1 + 1)` is the compiler bound at the spine cone count. -/
theorem construction_width (r : ℕ) (hr : 1 ≤ r) :
    ∃ net : Network (r + 1 + 1) (firstWidth (r + 1 + 1))
      (secondWidth (r + 1 + 1)), ∀ x, net.eval x = Maximum (r + 1 + 1) x :=
  width_of_cone_count r _ hr (normalized_cone_count r)

end MaxCaterpillar
