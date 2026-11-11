import research.sN.max5_optimal_20261103.lower.unrestricted_four.convex_general.Shape

/-! A literal-array consumer of the curvature-sign lower bound.
Every affine bias and signed output coefficient is quantified explicitly. -/

set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.ConvexCores.ShapeCheck
open BigOperators

theorem literal_arrays {N K mR mg : ℕ} [NeZero N]
    (aR : Fin N → ℝ) (bR : ℝ) (AR : Fin mR → Fin N → ℝ)
    (βR cR : Fin mR → ℝ)
    (ag : Fin K → Fin N → ℝ) (bg : Fin K → ℝ)
    (Ag : Fin K → Fin mg → Fin N → ℝ) (βg cg : Fin K → Fin mg → ℝ)
    (d : Fin K → ℝ)
    (hshape : ∀ k,
      ConvexOn ℝ Set.univ (fun x : Fin N → ℝ => (∑ i, ag k i * x i) + bg k +
        ∑ j, cg k j * relu ((∑ i, Ag k j i * x i) + βg k j)) ∨
      ConcaveOn ℝ Set.univ (fun x : Fin N → ℝ => (∑ i, ag k i * x i) + bg k +
        ∑ j, cg k j * relu ((∑ i, Ag k j i * x i) + βg k j)))
    (heq : ∀ x : Fin N → ℝ,
      (∑ i, aR i * x i) + bR + ∑ j, cR j * relu ((∑ i, AR j i * x i) + βR j) +
      ∑ k, d k * relu ((∑ i, ag k i * x i) + bg k +
        ∑ j, cg k j * relu ((∑ i, Ag k j i * x i) + βg k j)) = Maximum N x) :
    N ≤ K + 2 :=
  raw_shape_bound aR bR AR βR cR ag bg Ag βg cg d hshape heq

theorem literal_max5_two_core_exclusion
    (R : (Fin 5 → ℝ) → ℝ) (g : Fin 2 → (Fin 5 → ℝ) → ℝ) (d : Fin 2 → ℝ)
    (hR : IsShallow R) (hg : ∀ k, IsShallow (g k))
    (hshape : ∀ k, ConvexOn ℝ Set.univ (g k) ∨ ConcaveOn ℝ Set.univ (g k))
    (heq : ∀ x, R x + ∑ k, d k * relu (g k x) = Maximum 5 x) : False :=
  max5_two_core_impossible R g d hR hg hshape heq

#check @literal_arrays
#check @literal_max5_two_core_exclusion
#print axioms literal_arrays
#print axioms literal_max5_two_core_exclusion
end MaxCaterpillar.Max5Optimal.ConvexCores.ShapeCheck
