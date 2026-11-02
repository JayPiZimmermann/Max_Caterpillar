import MaxCaterpillar.Frontier.StarCertificate.MobiusCertificate
import MaxCaterpillar.Frontier.StarCertificate.StarCenters

/-! # Möbius vanishing for actual arbitrary-centre star families

The finite coefficient certificate remains an explicit hypothesis. Every
set-function endpoint, unrectified top coefficient and chamber Xi identity
is derived from the primitive star formula; the actual positive-gap affine
identities and the remainder's zero top coefficient are supplied separately.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem topMobius_relabel (G : Finset (Fin 5) → ℝ) (e : Equiv.Perm (Fin 5)) :
    topMobius (relabelSetFunction G e) = topMobius G := by
  unfold topMobius relabelSetFunction
  apply Fintype.sum_equiv e.symm.finsetCongr
  intro B
  simp only [Equiv.finsetCongr_apply, topMobiusSign, Finset.card_map]

theorem topMobius_starAtSetFunction (center : Fin 5) (v vp : Fin 5 → ℝ) :
    topMobius (starAtSetFunction center v vp) = 0 := by
  rw [starAtSetFunction_eq_relabel, topMobius_relabel]
  exact topMobius_starSetFunction _ _

@[simp] theorem starAtSetFunction_empty (center : Fin 5) (v vp : Fin 5 → ℝ) :
    starAtSetFunction center v vp ∅ = 0 := by
  simp [starAtSetFunction]

@[simp] theorem starAtSetFunction_full (center : Fin 5) (v vp : Fin 5 → ℝ) :
    starAtSetFunction center v vp Finset.univ = 0 := by
  simp [starAtSetFunction]

theorem starAt_table_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0)
    (center : Fin 5) (v vp : Fin 5 → ℝ) :
    (∑ p : Fin 120, starXi (setFunctionChain (starAtSetFunction center v vp) p)) = 0 := by
  change (∑ p : Fin 120, starXi (permutationFunctionChain
    (starAtSetFunction center v vp) (permutationEquiv p))) = 0
  exact (sum_permutationTable (fun pi => starXi
    (permutationFunctionChain (starAtSetFunction center v vp) pi))).trans
      (starAt_permutation_sum_of_coefficients hcoeff center v vp)

/-- An arbitrary finite signed family of primitive stars obeys the exact
top-Möbius obstruction once the concrete coefficient certificate is attached
and its actual positive-gap affine identities are known. No rectified top
coefficient is assumed to vanish. -/
theorem star_network_topMobius_zero_of_coefficients {ι : Type*} [Fintype ι]
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0)
    (center : ι → Fin 5) (v vp : ι → Fin 5 → ℝ) (weights : ι → ℝ)
    (Q : Finset (Fin 5) → ℝ)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ r, 0 < x r) →
        lin l x + β = ∑ i, weights i * relu
          (lin (setFunctionChain (starAtSetFunction (center i) (v i) (vp i)) p) x))
    (hQ : topMobius Q = 0) :
    topMobius (fun B => (∑ i, weights i * relu
      (starAtSetFunction (center i) (v i) (vp i) B)) + Q B) = 0 := by
  apply certificate_topMobius_zero
    (fun i => starAtSetFunction (center i) (v i) (vp i)) weights Q starXi
    starXi_even starXi_homogeneous starXi_zero starXi_nonmixed_abs
    (fun i => starAtSetFunction_empty (center i) (v i) (vp i))
    (fun i => starAtSetFunction_full (center i) (v i) (vp i))
    (fun i => topMobius_starAtSetFunction (center i) (v i) (vp i))
    (fun i => starAt_table_sum_of_coefficients hcoeff (center i) (v i) (vp i))
    hchamber hQ

end MaxCaterpillar.Frontier.StarCertificate
