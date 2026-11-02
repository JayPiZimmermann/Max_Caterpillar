import MaxCaterpillar.Frontier.StarCertificate.StarLeafEquivarianceCore

/-! # Exact global-sign symmetry of the actual star components -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem maskedGamma_neg (T : Fin 16) (p : Fin 120) (z : Fin 4→ℝ) :
    maskedGamma T p (-z)=-maskedGamma T p z := by
  funext i
  exact evalForm_neg_input _ _

theorem starPsi_neg (P : Finset (Fin 4)) (z : Fin 4→ℝ) :
    starPsi P (-z)=starPsi P z := by
  unfold starPsi
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : centerBeforeMask p=setMask P
  · simp only [if_pos hp,maskedGamma_neg]
    exact xi_neg _ _ _ _
  · simp only [if_neg hp]

theorem zeroOutside_neg {L : Type*} [DecidableEq L] (T : Finset L) (z : L→ℝ) :
    zeroOutside T (-z)=-zeroOutside T z := by
  funext i
  by_cases hi : i∈T <;> simp [zeroOutside,hi]

theorem component_neg_of_even {L : Type*} [DecidableEq L] [Fintype L]
    (Ψ : Finset L→(L→ℝ)→ℝ)
    (hΨ : ∀ P z, Ψ P (-z)=Ψ P z) (S A : Finset L) (z : L→ℝ) :
    component Ψ S A (-z)=component Ψ S A z := by
  unfold component
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  rw [zeroOutside_neg,hΨ]

theorem component_starPsi_neg (S A : Finset (Fin 4)) (z : Fin 4→ℝ) :
    component starPsi S A (-z)=component starPsi S A z :=
  component_neg_of_even starPsi starPsi_neg S A z

#print axioms component_starPsi_neg
end MaxCaterpillar.Frontier.StarCertificate
