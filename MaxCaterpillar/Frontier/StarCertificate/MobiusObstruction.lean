import MaxCaterpillar.Frontier.StarCertificate.MobiusCertificate
import MaxCaterpillar.Frontier.StarCertificate.MobiusQuadratic

/-! # Canonical Xi specialization and the actual Max5 conclusion

The finite checker must still discharge the explicitly named per-neuron Xi
identity. A network model bridge must supply the actual chamber identities
and Boolean evaluations. These are separate, visible mathematical stages.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem star_certificate_topMobius_zero {ι : Type*} [Fintype ι]
    (G : ι→Finset (Fin 5)→ℝ) (c : ι→ℝ) (Q : Finset (Fin 5)→ℝ)
    (hG0 : ∀ i, G i ∅=0) (hG1 : ∀ i, G i Finset.univ=0)
    (hGμ : ∀ i, topMobius (G i)=0)
    (hcertificate : ∀ i, (∑ p : Fin 120, starXi (setFunctionChain (G i) p))=0)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0<x j) →
        lin l x+β=∑ i, c i*relu (lin (setFunctionChain (G i) p) x))
    (hQ : topMobius Q=0) :
    topMobius (fun B => (∑ i, c i*relu (G i B))+Q B)=0 :=
  certificate_topMobius_zero G c Q starXi starXi_even starXi_homogeneous
    starXi_zero starXi_nonmixed_abs hG0 hG1 hGμ hcertificate hchamber hQ

theorem not_exact_maximum_of_zero_boolean_mobius (f : Point 5→ℝ)
    (hμ : topMobius (fun B => f (fun i => booleanCoordinate i B))=0) :
    ¬ (∀ x, f x=Maximum 5 x) := by
  intro h
  apply not_booleanOR_of_topMobius_zero _ hμ
  intro B
  rw [h,maximum_boolean_input]

/-- The complete certificate implication with an actual function as output.
The linear/quadratic remainder is explicit and automatically annihilated.
No hypothesis asserts a top coefficient of the rectified network sum. -/
theorem star_certificate_not_exact_maximum {ι : Type*} [Fintype ι]
    (f : Point 5→ℝ) (G : ι→Finset (Fin 5)→ℝ) (c : ι→ℝ)
    (a : ℝ) (b : Fin 5→ℝ) (d : Fin 5→Fin 5→ℝ)
    (hvertices : ∀ B, f (fun i => booleanCoordinate i B)=
      (∑ i, c i*relu (G i B))+booleanQuadratic a b d B)
    (hG0 : ∀ i, G i ∅=0) (hG1 : ∀ i, G i Finset.univ=0)
    (hGμ : ∀ i, topMobius (G i)=0)
    (hcertificate : ∀ i, (∑ p : Fin 120, starXi (setFunctionChain (G i) p))=0)
    (hchamber : ∀ p : Fin 120, ∃ l : Point 4, ∃ β : ℝ,
      ∀ x : Point 4, (∀ j, 0<x j) →
        lin l x+β=∑ i, c i*relu (lin (setFunctionChain (G i) p) x)) :
    ¬ (∀ x, f x=Maximum 5 x) := by
  apply not_exact_maximum_of_zero_boolean_mobius
  have he : (fun B => f (fun i => booleanCoordinate i B))=
      fun B => (∑ i, c i*relu (G i B))+booleanQuadratic a b d B := funext hvertices
  rw [he]
  exact star_certificate_topMobius_zero G c _ hG0 hG1 hGμ
    hcertificate hchamber (topMobius_booleanQuadratic a b d)

#print axioms star_certificate_topMobius_zero
#print axioms not_exact_maximum_of_zero_boolean_mobius
#print axioms star_certificate_not_exact_maximum
end MaxCaterpillar.Frontier.StarCertificate
