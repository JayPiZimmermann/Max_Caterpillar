import MaxCaterpillar.Fiber.Count65.HeadTopology
import MaxCaterpillar.Fiber.Count65.Mixed.FeatureTopology

/-! # Continuous nonnegative sections from actual readout coefficients -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.CoefficientSplit
open Mixed65 MixedFeatureTopology MaxCaterpillar.Frontier

noncomputable def positive (a : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => relu (a i)
noncomputable def negative (a : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => relu (-a i)

lemma continuous_positive : Continuous positive := by
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_apply i)

lemma continuous_negative : Continuous negative := by
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_apply i).neg

lemma positive_sub_negative (a : Fin 4 → ℝ) : positive a-negative a=a := by
  funext i
  exact relu_sub_relu_neg (a i)

noncomputable def positiveReadout (t : ℝ) (a : Fin 4 → ℝ) : featureSpace t :=
  coefficientReadout t (positive a)

noncomputable def negativeReadout (t : ℝ) (a : Fin 4 → ℝ) : featureSpace t :=
  coefficientReadout t (negative a)

lemma continuous_positiveReadout (t : ℝ) : Continuous (positiveReadout t) :=
  (continuous_coefficientReadout t).comp continuous_positive

lemma continuous_negativeReadout (t : ℝ) : Continuous (negativeReadout t) :=
  (continuous_coefficientReadout t).comp continuous_negative

lemma positiveReadout_nonnegative (t : ℝ) (a : Fin 4 → ℝ) :
    ∀ x, 0 ≤ (positiveReadout t a : InvariantState → ℝ) x :=
  readoutPos_nonneg t (a 0) (a 1) (a 2) (a 3)

lemma negativeReadout_nonnegative (t : ℝ) (a : Fin 4 → ℝ) :
    ∀ x, 0 ≤ (negativeReadout t a : InvariantState → ℝ) x :=
  readoutNeg_nonneg t (a 0) (a 1) (a 2) (a 3)

lemma positiveReadout_sub_negativeReadout (t : ℝ) (a : Fin 4 → ℝ) :
    positiveReadout t a-negativeReadout t a=coefficientReadout t a := by
  apply Subtype.ext
  exact readoutPos_sub_readoutNeg t (a 0) (a 1) (a 2) (a 3)

/-- The complete family count follows from continuous actual remainder
coefficients alone. The nonnegative sections are constructed, not assumed. -/
theorem mixed_family_has_two_components {β : Type*} [TopologicalSpace β]
    [PathConnectedSpace β] {t : ℝ} (ht : 0<t) (a : β → Fin 4 → ℝ)
    (ha : Continuous a)
    (hnz : ∀ b, ∃ x, (coefficientReadout t (a b) : InvariantState → ℝ) x ≠ 0) :
    Nonempty (ConnectedComponents (HeadTopology.BundleFiber (featureSpace t)
      (fun b => coefficientReadout t (a b))) ≃ Fin 2) :=
  HeadTopology.has_two_head_bundle_components (featureSpace t)
    (featureSpace_clipping_rigid ht) _
    (fun b => positiveReadout t (a b)) (fun b => negativeReadout t (a b))
    ((continuous_positiveReadout t).comp ha) ((continuous_negativeReadout t).comp ha)
    (fun b => positiveReadout_nonnegative t (a b))
    (fun b => negativeReadout_nonnegative t (a b))
    (fun b => positiveReadout_sub_negativeReadout t (a b)) hnz

#print axioms mixed_family_has_two_components
end MaxCaterpillar.Fiber.Count65.CoefficientSplit
