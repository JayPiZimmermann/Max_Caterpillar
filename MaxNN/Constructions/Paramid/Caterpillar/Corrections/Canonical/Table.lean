import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Canonical.Coefficients
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Network
import MaxNN.Core.Max
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# A canonical caterpillar correction table

The atom family is the disjoint union of the finite correction keys and the
pair-feature coordinates.  The coefficient of every tagged atom is the
symmetric inverse-Gram coefficient from `Canonical.Coefficients`; hence this
table does not select a spanning basis or a representing coefficient witness.
-/

open BigOperators MeasureTheory

namespace MaxNN.Caterpillar.Corrections.Canonical

open MaxNN.Width

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable local instance functionMeasureSpace (N : ℕ) :
    MeasureSpace (Fin N → ℝ) := ⟨Measure.addHaar⟩

local instance functionIsAddHaarMeasure (N : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (Fin N → ℝ)) :=
  Measure.isAddHaarMeasure_addHaarMeasure _

theorem IsPosHomContinuous.relu {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : IsPosHomContinuous f) :
    IsPosHomContinuous (fun x ↦ MaxNN.relu (f x)) := by
  refine ⟨continuous_const.max hf.1, fun c hc x ↦ ?_⟩
  change MaxNN.relu (f (c • x)) = c * MaxNN.relu (f x)
  rw [hf.2 c hc x, mul_comm c (f x), MaxNN.relu_mul_of_nonneg hc]

theorem feat_posHomContinuous (N : ℕ) (i : Fin (W N)) :
    IsPosHomContinuous (fun x : Fin N → ℝ ↦ feat N x i) := by
  refine Fin.addCases (motive := fun i : Fin (N + (N + N.choose 2)) ↦
      IsPosHomContinuous (fun x : Fin N → ℝ ↦ feat N x i)) ?_ ?_ i
  · intro j
    rw [show (fun x : Fin N → ℝ ↦ feat N x (Fin.castAdd (N + N.choose 2) j)) =
        fun x ↦ MaxNN.relu (x j) from funext fun x ↦ feat_pos x j]
    exact IsPosHomContinuous.relu (show IsPosHomContinuous (fun x : Fin N → ℝ ↦ x j) from
      ⟨continuous_apply j, fun c _ x ↦ rfl⟩)
  · intro j
    refine Fin.addCases (motive := fun j : Fin (N + N.choose 2) ↦
        IsPosHomContinuous
          (fun x : Fin N → ℝ ↦ feat N x (Fin.natAdd N j))) ?_ ?_ j
    · intro k
      rw [show (fun x : Fin N → ℝ ↦
          feat N x (Fin.natAdd N (Fin.castAdd (N.choose 2) k))) =
          fun x ↦ MaxNN.relu (-(x k)) from funext fun x ↦ feat_neg x k]
      exact IsPosHomContinuous.relu (show IsPosHomContinuous (fun x : Fin N → ℝ ↦ -(x k)) from
        ⟨(continuous_apply k).neg, fun c _ x ↦ by
          change -(c * x k) = c * (-(x k)); ring⟩)
    · intro q
      rw [show (fun x : Fin N → ℝ ↦
          feat N x (Fin.natAdd N (Fin.natAdd N q))) =
          fun x ↦ MaxNN.relu (x (prFst q) - x (prSnd q)) from
        funext fun x ↦ feat_pr x q]
      exact IsPosHomContinuous.relu (show IsPosHomContinuous
          (fun x : Fin N → ℝ ↦ x (prFst q) - x (prSnd q)) from
        ⟨(continuous_apply (prFst q)).sub (continuous_apply (prSnd q)),
          fun c _ x ↦ by change c * x (prFst q) - c * x (prSnd q) =
            c * (x (prFst q) - x (prSnd q)); ring⟩)

theorem pairLin_posHomContinuous {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : f ∈ PairLin N) : IsPosHomContinuous f := by
  obtain ⟨a, ha⟩ := hf
  have he : f = lincomb (fun i : Fin (W N) ↦ fun x ↦ feat N x i) a := by
    funext x
    rw [ha x]
    rfl
  rw [he]
  exact lincomb_posHomContinuous (feat_posHomContinuous N) a

theorem realUnitY_posHomContinuous {n : ℕ} (k : RealKey n)
    (hk : ∀ v ∈ k.2, IsSimplexDifference v) :
    IsPosHomContinuous (realUnitY k) := by
  rw [show realUnitY k = fun y ↦ MaxNN.relu (realUnitArg k y) from
    funext (realUnitY_eq_relu k)]
  exact IsPosHomContinuous.relu
    (pairLin_posHomContinuous (realUnitArg_mem_pairLin k hk))

variable (r : ℕ)

abbrev AtomIndex := (↑(correctionKeys r) : Type) ⊕ Fin (W (r + 1 + 1))

/-- Correction units followed by the shared pair-feature coordinates. -/
def atomFunction : AtomIndex r → (Fin (r + 1 + 1) → ℝ) → ℝ
  | Sum.inl k => realUnitY k.1
  | Sum.inr i => fun y ↦ feat (r + 1 + 1) y i

theorem atomFunction_posHomContinuous (i : AtomIndex r) :
    IsPosHomContinuous (atomFunction r i) := by
  cases i with
  | inl k =>
      exact realUnitY_posHomContinuous k.1
        (correctionKeys_simplexDifference k.1 k.2)
  | inr i => exact feat_posHomContinuous _ i

theorem atomFunction_mem_atomSpan (i : AtomIndex r) :
    atomFunction r i ∈ Submodule.span ℝ
      (↑(taggedDictionary (atomFunction r)) :
        Set ((Fin (r + 1 + 1) → ℝ) → ℝ)) := by
  apply Submodule.subset_span
  apply Finset.mem_coe.mpr
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Every function represented by `RealUnitSpan` lies in the ordinary span of
the tagged atom dictionary. -/
theorem realUnitSpan_le_atomSpan :
    RealUnitSpan (r + 1) (correctionKeys r) ≤
      Submodule.span ℝ (↑(taggedDictionary (atomFunction r)) :
        Set ((Fin (r + 1 + 1) → ℝ) → ℝ)) := by
  intro f hf
  obtain ⟨c, q, hq, hcompute⟩ := hf
  obtain ⟨a, ha⟩ := hq
  rw [show f = (fun y ↦ ∑ k in correctionKeys r, c k * realUnitY k y) + q from by
    funext y
    exact hcompute y]
  apply Submodule.add_mem
  · rw [show (fun y ↦ ∑ k in correctionKeys r, c k * realUnitY k y) =
        ∑ k in correctionKeys r, c k • realUnitY k from by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _
      (atomFunction_mem_atomSpan r (Sum.inl ⟨k, hk⟩))
  · rw [show q = ∑ i, a i • (fun y ↦ feat (r + 1 + 1) y i) from by
      funext y
      rw [ha y]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _
      (atomFunction_mem_atomSpan r (Sum.inr i))

theorem MAX_mem_atomSpan (hr : 1 ≤ r) (hclass : FormulaClassIdentity r) :
    MAX (r + 1 + 1) ∈ Submodule.span ℝ
      (↑(taggedDictionary (atomFunction r)) :
        Set ((Fin (r + 1 + 1) → ℝ) → ℝ)) := by
  apply realUnitSpan_le_atomSpan r
  have hΔ := simplex_mem_correctionSpan hr (fullDimensionalWords r)
    (coneClassIdentity_of_formulaClassIdentity hclass)
  have he : MAX (r + 1 + 1) = (fun y ↦ y 0) +
      MaxNN.Width.coordPull (r + 1)
        (ParamidGeom.hS (ParamidGeom.simplexVerts (r + 1))) := by
    funext y
    exact ParamidGeom.CoordAux.MAX_succ_eq_add_hS_simplexVerts y
  rw [he]
  exact Submodule.add_mem _ (pairLin_mem_realUnitSpan (coord_mem_pairLin 0))
    (Submodule.mem_comap.mp hΔ)

/-- The literal coefficient attached to a raw correction key. -/
def canonicalRawCoeff (k : RealKey (r + 1)) : ℝ :=
  if hk : k ∈ correctionKeys r then
    taggedCoeff (atomFunction r) (MAX (r + 1 + 1)) (Sum.inl ⟨k, hk⟩)
  else 0

/-- Sum the raw canonical coefficients over one normalized-key fiber. -/
def canonicalNormalizedCoeff (k : RealKey (r + 1)) : ℝ :=
  ∑ q in (correctionKeys r).filter (fun q ↦ normalizedKey q = k),
    canonicalRawCoeff r q

/-- Normalized keys whose canonical fiber coefficient is nonzero. -/
def canonicalActiveKeys : Finset (RealKey (r + 1)) :=
  (normalizedKeys r).filter fun k ↦ canonicalNormalizedCoeff r k ≠ 0

/-- The literal feature coefficient vector for the linear remainder. -/
def canonicalRemainderCoeff (i : Fin (W (r + 1 + 1))) : ℝ :=
  taggedCoeff (atomFunction r) (MAX (r + 1 + 1)) (Sum.inr i)

/-- The network data are defined for every `r`, independently of the proof
that the caterpillar formula is correct. -/
def canonicalNetworkCandidate : ReLUNet (r + 1 + 1) 1 2 :=
  dictionaryNetwork (canonicalActiveKeys r) (canonicalNormalizedCoeff r)
    (canonicalRemainderCoeff r)

/-- The finite inverse-Gram formula, specialized to every caterpillar
correction key and every pair-feature coordinate. -/
def canonicalCorrectionTable (hr : 1 ≤ r) (hclass : FormulaClassIdentity r) :
    CorrectionTable r where
  coeff := canonicalRawCoeff r
  remainder := fun y ↦ ∑ i, canonicalRemainderCoeff r i *
    feat (r + 1 + 1) y i
  remainder_pairLin := ⟨canonicalRemainderCoeff r, fun _ ↦ rfl⟩
  computes := fun y ↦ by
    have hall := sum_taggedCoeff_eq (atomFunction r)
      (atomFunction_posHomContinuous r) (MAX_mem_atomSpan r hr hclass) y
    rw [Fintype.sum_sum_type] at hall
    rw [← hall]
    congr 1
    rw [← Finset.sum_coe_sort (correctionKeys r)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [canonicalRawCoeff, dif_pos k.2, atomFunction]

theorem canonicalCorrectionTable_remainder (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) (y : Fin (r + 1 + 1) → ℝ) :
    (canonicalCorrectionTable r hr hclass).remainder y =
      ∑ i, canonicalRemainderCoeff r i * feat (r + 1 + 1) y i := rfl

theorem canonicalCorrectionTable_normalizedCoeff (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (canonicalCorrectionTable r hr hclass).normalizedCoeff =
      canonicalNormalizedCoeff r := rfl

theorem canonicalCorrectionTable_normalizedActiveKeys (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (canonicalCorrectionTable r hr hclass).normalizedActiveKeys =
      canonicalActiveKeys r := rfl

/-- The literal normalized two-hidden-layer network obtained from the
canonical table. -/
def canonicalNetwork (hr : 1 ≤ r) (hclass : FormulaClassIdentity r) :
    ReLUNet (r + 1 + 1) 1 2 :=
  (canonicalCorrectionTable r hr hclass).normalizedNetwork
    (canonicalRemainderCoeff r)

theorem canonicalNetwork_computes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (canonicalNetwork r hr hclass).Computes (MAX (r + 1 + 1)) := by
  apply CorrectionTable.normalizedNetwork_computes
  exact canonicalCorrectionTable_remainder r hr hclass

/-- Correctness of the assumption-free network data. -/
theorem canonicalNetworkCandidate_computes (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    (canonicalNetworkCandidate r).Computes (MAX (r + 1 + 1)) := by
  change ((canonicalCorrectionTable r hr hclass).normalizedNetwork
    (canonicalRemainderCoeff r)).Computes (MAX (r + 1 + 1))
  exact canonicalNetwork_computes r hr hclass

theorem canonicalActiveKeys_card_le_normalizedKeys :
    (canonicalActiveKeys r).card ≤ (normalizedKeys r).card :=
  Finset.card_le_of_subset (Finset.filter_subset _ _)

theorem canonical_twoLayerWidth_normalizedActive (hr : 1 ≤ r)
    (hclass : FormulaClassIdentity r) :
    TwoLayerWidth (r + 1 + 1) (W (r + 1 + 1))
      ((canonicalCorrectionTable r hr hclass).normalizedActiveKeys.card + 2)
      (MAX (r + 1 + 1)) :=
  (canonicalCorrectionTable r hr hclass).twoLayerWidth_normalizedActive

end

end MaxNN.Caterpillar.Corrections.Canonical
