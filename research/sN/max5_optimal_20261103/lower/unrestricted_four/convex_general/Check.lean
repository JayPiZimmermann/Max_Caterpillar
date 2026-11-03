import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.ShapeCheck
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Nonvacuity
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.LocalizeCheck
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.TangentCheck
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.SimplexCheck

/-! Final exact-type consumer. Raw arrays are checked in ShapeCheck; this
leaf also checks the arbitrary-index function statement and a real MAX3
boundary witness. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Frontier

example {N : ℕ} [NeZero N] {κ : Type*} [Fintype κ]
    (R : Point N → ℝ) (g : κ → Point N → ℝ) (d : κ → ℝ)
    (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hc : ∀ k, ConvexOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum N x) :
    N ≤ Fintype.card κ + 2 :=
  convex_core_lower_bound R g d hR hg hc heq

#check @ConvexRepresentation.bound
#check @convex_core_lower_bound
#check @shape_bound
#print axioms ConvexRepresentation.bound
#print axioms convex_core_lower_bound
#print axioms shape_bound
end MaxCaterpillar.Max5Optimal.ConvexCores
