import MaxCaterpillar.Frontier.StarCertificate.XiStar

/-! # The real anchored expressions and their rational coefficients -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

theorem evalForm_finset_sum {ι : Type*} {n : ℕ} (s : Finset ι)
    (a : ι → RationalForm n) (x : Fin n → ℝ) :
    evalForm (fun i => ∑ j in s, a j i) x = ∑ j in s, evalForm (a j) x := by
  simp only [evalForm, Rat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem evalForm_rat_scale {n : ℕ} (q : ℚ) (a : RationalForm n) (x : Fin n → ℝ) :
    evalForm (fun i => q*a i) x = (q:ℝ)*evalForm a x := by
  simp only [evalForm, Rat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem maskedPsi_linearization (T : Fin 16) (P : Finset (Fin 4)) (z : Fin 4 → ℝ) :
    starPsi P (zeroOutside (maskSet T) z) =
      evalForm (maskedPsiCoefficients T (setMask P) (actualSigns subsetForms z)) z := by
  unfold starPsi maskedPsiCoefficients
  rw [evalForm_finset_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : centerBeforeMask p = setMask P
  · simp only [if_pos hp, maskedGamma_zeroOutside]
    exact maskedXi_linearization T p z
  · simp only [if_neg hp]
    simp [evalForm]

theorem starPsi_zeroOutside_linearization (T P : Finset (Fin 4)) (z : Fin 4 → ℝ) :
    starPsi P (zeroOutside T z) =
      evalForm (maskedPsiCoefficients (setMask T) (setMask P) (actualSigns subsetForms z)) z := by
  simpa only [maskSet_setMask] using maskedPsi_linearization (setMask T) P z

/-- The exact rational coefficients of Jensen's actual anchored expression.
Both subset sums have exactly the same domains as `component`. -/
def componentCoefficients (S A : Finset (Fin 4)) (s : Fin 15 → Sign) : RationalForm 4 :=
  fun i => ∑ T in S.powerset, (-1 : ℚ) ^ (S \ T).card *
    ∑ P in (Finset.univ : Finset (Fin 4)).powerset.filter (fun P => P ∩ S = A),
      maskedPsiCoefficients (setMask T) (setMask P) s i

/-- The formal coefficient function is connected to the real Xi expression,
including irrational inputs and resonance boundaries. -/
theorem component_linearization (S A : Finset (Fin 4)) (z : Fin 4 → ℝ) :
    component starPsi S A z =
      evalForm (componentCoefficients S A (actualSigns subsetForms z)) z := by
  unfold component componentCoefficients
  rw [evalForm_finset_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [evalForm_rat_scale, evalForm_finset_sum]
  have hc : (((-1 : ℚ) ^ (S \ T).card : ℚ) : ℝ) = (-1 : ℝ) ^ (S \ T).card := by
    norm_cast
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  exact starPsi_zeroOutside_linearization T P z

theorem starPsi_zero (P : Finset (Fin 4)) : starPsi P 0 = 0 := by
  unfold starPsi
  apply Finset.sum_eq_zero
  intro p _
  split_ifs
  · have hz : maskedGamma 15 p 0 = 0 := by
      funext j
      simp [maskedGamma, evalForm]
    rw [hz]
    exact xi_zero coarseForms starOmega starKappa
  · rfl

end MaxCaterpillar.Frontier.StarCertificate
