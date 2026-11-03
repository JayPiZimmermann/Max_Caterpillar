import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Tangent
import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.ConvexTangent

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores.Check
open BigOperators Filter Topology Frontier
open Frontier.RandomRestriction.NormalizedNetwork

/-- Literal affine-array source, including every first-layer bias. -/
theorem raw_affine_convex_tangent {N m w : ℕ}
    (a : Point N) (b : ℝ) (A : Fin w → Point N) (β c : Fin w → ℝ)
    (hc : ConvexOn ℝ Set.univ
      (fun x => lin a x + b + ∑ j, c j * relu (lin (A j) x + β j)))
    (q : Point N) (e : Fin m ↪ Fin N) :
    ∃ D : Point m → ℝ, IsShallow D ∧ ConvexOn ℝ Set.univ D ∧
      ∀ x, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        lin a (q + ε • lift e x) + b +
            (∑ j, c j * relu (lin (A j) (q + ε • lift e x) + β j)) =
          lin a q + b + (∑ j, c j * relu (lin (A j) q + β j)) + ε * D x := by
  obtain ⟨D, hD, ht⟩ := (IsShallow.raw a b A β c).exists_tangent q e
  exact ⟨D, hD, ht.convex hc, ht⟩

#check @raw_affine_convex_tangent
#print axioms raw_affine_convex_tangent

end MaxCaterpillar.Max5Optimal.ConvexCores.Check
