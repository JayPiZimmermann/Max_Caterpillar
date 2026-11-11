import MaxCaterpillar.Fiber.Count65.Mixed.QuotientCharts
set_option autoImplicit false
open Set MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Count65
open MixedQuotientCharts MixedSectorComponents ActualMixedLabels Mixed65

example (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartAQuotient bits '' headSectorA bits kind) :=
  isPathConnected_quotientChartA bits kind
example (bits : Fin 3 → Bool) (kind : Bool) :
    IsPathConnected (chartBQuotient bits '' headSectorB bits kind) :=
  isPathConnected_quotientChartB bits kind

example (p : Slice) (hz : p.val.2.HasZeroBiases) :
    ∃ bits : Fin 3 → Bool,
      (∃ q : ResidualHeadChartA bits,
        Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartAQuotient bits q) ∨
      (∃ q : ResidualHeadChartB bits,
        Quotient.mk (zeroBiasSymmetrySetoid 4 6 5) (physicalZeroBias p hz)=chartBQuotient bits q) :=
  zeroBias_quotient_coverage p hz

example (bits : Fin 3 → Bool) (kind : Bool) :
    ∃ z : ZeroBiasSymmetryQuotient 4 6 5,z ∈ chartAQuotient bits '' headSectorA bits kind :=
by
  obtain ⟨z,hz,_⟩ := isPathConnected_quotientChartA bits kind
  exact ⟨z,hz⟩

#print axioms isPathConnected_actualChartA
#print axioms isPathConnected_actualChartB
#print axioms isPathConnected_quotientChartA
#print axioms isPathConnected_quotientChartB
#print axioms classA_quotient_covered
#print axioms classB_quotient_covered
#print axioms zeroBias_quotient_coverage
