import MaxCaterpillar.Fiber.Count65.Mixed.ChartCoordinates
import MaxCaterpillar.Fiber.Count65.CoefficientSplit

/-! # Two head components throughout each complete mixed residual chart

These spaces include all t>0 and the full closed parameter ray, for a fixed
residual branch and orientation. Identifying their images with sectors of the
actual network symmetry quotient is a separate topology bridge.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Fiber.Count65

abbrev ResidualHeadChartA (bits : Fin 3 → Bool) :=
  HeadTopology.BundleFiber (featureSpace 1)
    (fun p : ResidualChartBase => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderA bits p))
abbrev ResidualHeadChartB (bits : Fin 3 → Bool) :=
  HeadTopology.BundleFiber (featureSpace 1)
    (fun p : ResidualChartBase => MixedFeatureTopology.coefficientReadout 1 (fixedRemainderB bits p))

theorem chartA_has_two_head_components (bits : Fin 3 → Bool) :
    Nonempty (ConnectedComponents (ResidualHeadChartA bits) ≃ Fin 2) := by
  letI : PathConnectedSpace ResidualChartBase := residualChartBase_pathConnected
  exact CoefficientSplit.mixed_family_has_two_components (by norm_num : 0 < (1 : ℝ))
    (fixedRemainderA bits) (continuous_fixedRemainderA bits) (fixedRemainderA_nonzero bits)

theorem chartB_has_two_head_components (bits : Fin 3 → Bool) :
    Nonempty (ConnectedComponents (ResidualHeadChartB bits) ≃ Fin 2) := by
  letI : PathConnectedSpace ResidualChartBase := residualChartBase_pathConnected
  exact CoefficientSplit.mixed_family_has_two_components (by norm_num : 0 < (1 : ℝ))
    (fixedRemainderB bits) (continuous_fixedRemainderB bits) (fixedRemainderB_nonzero bits)

end MaxCaterpillar.Fiber.Mixed65
