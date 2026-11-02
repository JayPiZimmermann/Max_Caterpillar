import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabelsSymmetry
import MaxCaterpillar.Fiber.Count65.Mixed.PhysicalChart

/-! # Connected actual mixed network chart sectors

These are continuous images in the real physical network parameter space.
The separate exact coefficient coverage theorem identifies them with all
members of each actual finite-label class.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.MixedSectorComponents
open Set Mixed65 ActualMixedLabels

noncomputable def chartA (bits : Fin 3 → Bool) (p : ResidualHeadChartA bits) : Slice :=
  ⟨(p.val.1.1.val,chartNetA bits p),p.val.1.1.property,rfl,chartNetA_exact bits p,by
    intro i
    fin_cases i <;> norm_num [chartNetA,residualLift,chartResidualA,ResidualSystem.flip,canonicalResidualA]⟩
noncomputable def chartB (bits : Fin 3 → Bool) (p : ResidualHeadChartB bits) : Slice :=
  ⟨(p.val.1.1.val,chartNetB bits p),p.val.1.1.property,rfl,chartNetB_exact bits p,by
    intro i
    fin_cases i <;> norm_num [chartNetB,residualLift,chartResidualB,ResidualSystem.flip,canonicalResidualB]⟩

lemma continuous_chartA (bits : Fin 3 → Bool) : Continuous (chartA bits) :=
  (((continuous_subtype_val.comp continuous_fst).comp
    (continuous_fst.comp continuous_subtype_val)).prod_mk
      (continuous_chartNetA bits)).subtype_mk _
lemma continuous_chartB (bits : Fin 3 → Bool) : Continuous (chartB bits) :=
  (((continuous_subtype_val.comp continuous_fst).comp
    (continuous_fst.comp continuous_subtype_val)).prod_mk
      (continuous_chartNetB bits)).subtype_mk _

def headSectorA (bits : Fin 3 → Bool) (kind : Bool) : Set (ResidualHeadChartA bits) :=
  if kind then HeadTopology.bundleSignedSector (featureSpace 1)
    (fun b => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderA bits b))
  else (HeadTopology.bundleSignedSector (featureSpace 1)
    (fun b => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderA bits b)))ᶜ

def headSectorB (bits : Fin 3 → Bool) (kind : Bool) : Set (ResidualHeadChartB bits) :=
  if kind then HeadTopology.bundleSignedSector (featureSpace 1)
    (fun b => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderB bits b))
  else (HeadTopology.bundleSignedSector (featureSpace 1)
    (fun b => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderB bits b)))ᶜ

lemma isPathConnected_headSectorA (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (headSectorA bits kind) := by
  letI : PathConnectedSpace ResidualChartBase := residualChartBase_pathConnected
  cases kind
  · exact HeadTopology.bundleComplement_isPathConnected (featureSpace 1)
      (featureSpace_clipping_rigid (by norm_num : 0 < (1 : ℝ))) _
      (fun b => CoefficientSplit.positiveReadout 1 (fixedRemainderA bits b))
      (fun b => CoefficientSplit.negativeReadout 1 (fixedRemainderA bits b))
      ((CoefficientSplit.continuous_positiveReadout 1).comp (continuous_fixedRemainderA bits))
      ((CoefficientSplit.continuous_negativeReadout 1).comp (continuous_fixedRemainderA bits))
      (fun b => CoefficientSplit.positiveReadout_nonnegative 1 (fixedRemainderA bits b))
      (fun b => CoefficientSplit.negativeReadout_nonnegative 1 (fixedRemainderA bits b))
      (fun b => CoefficientSplit.positiveReadout_sub_negativeReadout 1 (fixedRemainderA bits b))
      (fixedRemainderA_nonzero bits)
  · exact HeadTopology.bundleSignedSector_isPathConnected (featureSpace 1) _
      ((MixedFeatureTopology.continuous_coefficientReadout 1).comp (continuous_fixedRemainderA bits))

lemma isPathConnected_headSectorB (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (headSectorB bits kind) := by
  letI : PathConnectedSpace ResidualChartBase := residualChartBase_pathConnected
  cases kind
  · exact HeadTopology.bundleComplement_isPathConnected (featureSpace 1)
      (featureSpace_clipping_rigid (by norm_num : 0 < (1 : ℝ))) _
      (fun b => CoefficientSplit.positiveReadout 1 (fixedRemainderB bits b))
      (fun b => CoefficientSplit.negativeReadout 1 (fixedRemainderB bits b))
      ((CoefficientSplit.continuous_positiveReadout 1).comp (continuous_fixedRemainderB bits))
      ((CoefficientSplit.continuous_negativeReadout 1).comp (continuous_fixedRemainderB bits))
      (fun b => CoefficientSplit.positiveReadout_nonnegative 1 (fixedRemainderB bits b))
      (fun b => CoefficientSplit.negativeReadout_nonnegative 1 (fixedRemainderB bits b))
      (fun b => CoefficientSplit.positiveReadout_sub_negativeReadout 1 (fixedRemainderB bits b))
      (fixedRemainderB_nonzero bits)
  · exact HeadTopology.bundleSignedSector_isPathConnected (featureSpace 1) _
      ((MixedFeatureTopology.continuous_coefficientReadout 1).comp (continuous_fixedRemainderB bits))

/-- Each complete mixed A chart/head-kind sector is path connected as a set of
actual exact physical networks, not just as a formal coefficient family. -/
theorem isPathConnected_actualChartA (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartA bits '' headSectorA bits kind) :=
  (isPathConnected_headSectorA bits kind).image (continuous_chartA bits)

theorem isPathConnected_actualChartB (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartB bits '' headSectorB bits kind) :=
  (isPathConnected_headSectorB bits kind).image (continuous_chartB bits)

#print axioms isPathConnected_actualChartA
#print axioms isPathConnected_actualChartB
end MaxCaterpillar.Fiber.Count65.MixedSectorComponents
