import MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeCertificates
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafCoverage
import MaxCaterpillar.Frontier.StarCertificate.StarCenters
import MaxCaterpillar.Frontier.StarCertificate.StarMobius
import MaxCaterpillar.Frontier.StarCertificate.MobiusQuadratic

/-! # The all-real star obstruction

The fixed integer certificate, its exact numeric checks, geometric coverage,
S4/sign transport, and real semantic bridges are all imported proofs. The
statements below have no certificate, rational-slope, or face-cover premise.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- All eighty anchored identities hold for every real four-slope vector. -/
theorem starAnova_all_real (z : Fin 4 → ℝ) (t : Fin 80) :
    evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0 :=
  XiOrbitLeafCoverage.all_real_of_representatives XiRepresentativeCertificates.sound z t

/-- Every real-slope star, with any centre, has zero total Xi certificate. -/
theorem starAt_permutation_sum_eq_zero (c : Fin 5) (v v' : Fin 5 → ℝ) :
    (∑ e : Equiv.Perm (Fin 5),
      starXi (permutationFunctionChain (starAtSetFunction c v v') e)) = 0 :=
  starAt_permutation_sum_of_coefficients starAnova_all_real c v v'

/-- A finite signed sum of arbitrary-centre real star neurons which is
linear on every braid chamber cannot acquire a fifth Möbius coefficient
by adding a one-hidden-layer braid function. -/
theorem star_network_topMobius_zero {ι : Type*} [Fintype ι]
    (center : ι → Fin 5) (v v' : ι → Fin 5 → ℝ) (weights : ι → ℝ)
    (Q : Finset (Fin 5) → ℝ)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0 < x j) →
        lin l x + β = ∑ i, weights i * relu
          (lin (setFunctionChain (starAtSetFunction (center i) (v i) (v' i)) p) x))
    (hQ : topMobius Q = 0) :
    topMobius (fun B => (∑ i, weights i * relu (starAtSetFunction (center i) (v i) (v' i) B)) + Q B) = 0 :=
  star_network_topMobius_zero_of_coefficients starAnova_all_real center v v' weights Q hchamber hQ

/-- The usual braid first-hidden-layer Boolean model needs no separate
Möbius premise: every real quadratic base function has zero top coefficient. -/
theorem star_network_booleanQuadratic_topMobius_zero {ι : Type*} [Fintype ι]
    (center : ι → Fin 5) (v v' : ι → Fin 5 → ℝ) (weights : ι → ℝ)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0 < x j) →
        lin l x + β = ∑ i, weights i * relu
          (lin (setFunctionChain (starAtSetFunction (center i) (v i) (v' i)) p) x)) :
    topMobius (fun B => (∑ i, weights i * relu (starAtSetFunction (center i) (v i) (v' i) B)) +
      booleanQuadratic a b d B) = 0 :=
  star_network_topMobius_zero center v v' weights (booleanQuadratic a b d) hchamber
    (topMobius_booleanQuadratic a b d)

/-- The actual Boolean values of Max5 cannot be obtained by such a glued
signed star family and any real quadratic braid base function. -/
theorem star_network_booleanQuadratic_not_booleanOR {ι : Type*} [Fintype ι]
    (center : ι → Fin 5) (v v' : ι → Fin 5 → ℝ) (weights : ι → ℝ)
    (a : ℝ) (b : Fin 5 → ℝ) (d : Fin 5 → Fin 5 → ℝ)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0 < x j) →
        lin l x + β = ∑ i, weights i * relu
          (lin (setFunctionChain (starAtSetFunction (center i) (v i) (v' i)) p) x)) :
    ¬ ∀ B, (∑ i, weights i * relu (starAtSetFunction (center i) (v i) (v' i) B)) +
      booleanQuadratic a b d B = booleanOR B :=
  not_booleanOR_of_topMobius_zero _
    (star_network_booleanQuadratic_topMobius_zero center v v' weights a b d hchamber)

end MaxCaterpillar.Frontier.StarCertificate
