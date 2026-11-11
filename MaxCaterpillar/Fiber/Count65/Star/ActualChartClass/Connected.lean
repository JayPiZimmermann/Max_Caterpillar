import MaxCaterpillar.Fiber.Count65.Star.ActualChartClass.Base

/-! # Complete endpoint-inclusive star head sectors are path connected -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualStarLabels
open Set Function Star Star.PhysicalChart MaxCaterpillar.Frontier

private noncomputable def positiveReadout (a : Fin 4 → ℝ) : featureSpace 1 :=
  coefficientReadout 1 (fun i => relu (a i))
private noncomputable def negativeReadout (a : Fin 4 → ℝ) : featureSpace 1 :=
  coefficientReadout 1 (fun i => relu (-a i))
private lemma continuous_positiveReadout : Continuous positiveReadout := by
  apply (continuous_coefficientReadout 1).comp
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_apply i)
private lemma continuous_negativeReadout : Continuous negativeReadout := by
  apply (continuous_coefficientReadout 1).comp
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_apply i).neg
private lemma positiveReadout_nonnegative (a : Fin 4 → ℝ) :
    ∀ x,0 ≤ (positiveReadout a : InvariantState → ℝ) x := by
  intro x
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (relu_nonneg _) (le_max_left _ _))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _))
private lemma negativeReadout_nonnegative (a : Fin 4 → ℝ) :
    ∀ x,0 ≤ (negativeReadout a : InvariantState → ℝ) x := by
  intro x
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (relu_nonneg _) (le_max_left _ _))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _)))
    (mul_nonneg (relu_nonneg _) (le_max_left _ _))
private lemma readout_split (a : Fin 4 → ℝ) :
    positiveReadout a-negativeReadout a=coefficientReadout 1 a := by
  apply Subtype.ext
  funext x
  change (relu (a 0)*max 0 x.1+relu (a 1)*max 0 x.2.1+
      relu (a 2)*max 0 x.2.2+relu (a 3)*max 0 (x.1+1*x.2.1))-
    (relu (-a 0)*max 0 x.1+relu (-a 1)*max 0 x.2.1+
      relu (-a 2)*max 0 x.2.2+relu (-a 3)*max 0 (x.1+1*x.2.1))=
    a 0*max 0 x.1+a 1*max 0 x.2.1+a 2*max 0 x.2.2+a 3*max 0 (x.1+1*x.2.1)
  linear_combination (relu_sub_relu_neg (a 0))*max 0 x.1+
    (relu_sub_relu_neg (a 1))*max 0 x.2.1+
    (relu_sub_relu_neg (a 2))*max 0 x.2.2+
    (relu_sub_relu_neg (a 3))*max 0 (x.1+1*x.2.1)

private theorem isPathConnected_headSector {β : Type*} [TopologicalSpace β]
    [PathConnectedSpace β] (c : β → Fin 4 → ℝ) (hc : Continuous c)
    (hnz : ∀ b,∃ x,(coefficientReadout 1 (c b) : InvariantState → ℝ) x ≠ 0)
    (kind : Bool) :
    IsPathConnected (if kind then HeadTopology.bundleSignedSector (featureSpace 1)
      (fun b => coefficientReadout 1 (c b)) else
      (HeadTopology.bundleSignedSector (featureSpace 1) (fun b => coefficientReadout 1 (c b)))ᶜ) := by
  cases kind
  · exact HeadTopology.bundleComplement_isPathConnected (featureSpace 1)
      (clippingRigid_featureSpace (by norm_num)) _
      (fun b => positiveReadout (c b)) (fun b => negativeReadout (c b))
      (continuous_positiveReadout.comp hc) (continuous_negativeReadout.comp hc)
      (fun b => positiveReadout_nonnegative (c b)) (fun b => negativeReadout_nonnegative (c b))
      (fun b => readout_split (c b)) hnz
  · exact HeadTopology.bundleSignedSector_isPathConnected (featureSpace 1) _
      ((continuous_coefficientReadout 1).comp hc)

theorem isPathConnected_headSectorI (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (headSectorI bits kind) :=
  isPathConnected_headSector _ (continuous_branchICoefficients _ _ _)
    (branchI_remainder_nonzero _ _ _) kind

theorem isPathConnected_headSectorII (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (headSectorII bits kind) :=
  isPathConnected_headSector _ (continuous_branchIICoefficients _ _ _)
    (branchII_remainder_nonzero _ _ _) kind

theorem isPathConnected_chartI_image (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartI bits '' headSectorI bits kind) :=
  (isPathConnected_headSectorI bits kind).image (continuous_chartI bits)
theorem isPathConnected_chartII_image (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartII bits '' headSectorII bits kind) :=
  (isPathConnected_headSectorII bits kind).image (continuous_chartII bits)

#print axioms isPathConnected_headSectorI
#print axioms isPathConnected_headSectorII
end MaxCaterpillar.Fiber.Count65.ActualStarLabels
