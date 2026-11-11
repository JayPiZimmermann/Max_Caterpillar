import research.sN.max5_optimal_20261103.construction.nine_eleven.Identity
import research.sN.max5_optimal_20261103.construction.nine_eleven.Evaluation

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.NineEleven

/-- Every real input is evaluated exactly by the physical nine-by-eleven network. -/
theorem network_correct (x : Point 5) : network.eval x = Maximum 5 x :=
  (eval_eq_rhs x).trans (identity x).symm

/-- The existing no-skip upper bound, including all carrier neurons. -/
theorem exists_network : ∃ net : Network 5 9 11,
    (∀ x,net.eval x=Maximum 5 x) ∧ net.HasRationalWeights ∧ net.HasZeroBiases :=
  ⟨network,network_correct,rational_weights,zero_biases⟩

#print axioms network_correct
#print axioms exists_network
end MaxCaterpillar.Max5Optimal.NineEleven
