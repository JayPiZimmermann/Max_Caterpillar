import research.sN.max5_optimal_20261103.construction.ten_six.Network

set_option autoImplicit false
namespace MaxCaterpillar.MaxFiveTenSix.Check
open BigOperators

/-- Literal two-matrix formula: ten first-layer ReLUs, six second-layer
ReLUs, affine output with zero bias, and no skip term. -/
theorem literal_formula (x : Fin 5 → ℝ) :
    (∑ k : Fin 6, (outputWeights k : ℝ) *
      relu (∑ j : Fin 10, (secondWeights k j : ℝ) *
        relu (∑ i : Fin 5, (firstWeights j i : ℝ) * x i))) = Maximum 5 x := by
  simpa only [Network.eval,net,Pi.zero_apply,add_zero] using net_eval x

theorem exact_type :
    ∃ f : Network 5 10 6,
      (∀ x : Fin 5 → ℝ,f.eval x=Maximum 5 x) ∧
      f.HasRationalWeights ∧ f.HasZeroBiases := exists_network

#check @literal_formula
#check @exact_type
#print axioms literal_formula
#print axioms exact_type
end MaxCaterpillar.MaxFiveTenSix.Check
