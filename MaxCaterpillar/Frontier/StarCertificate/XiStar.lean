import MaxCaterpillar.Frontier.StarCertificate.XiSelectorProofs
import MaxCaterpillar.Frontier.StarCertificate.Anova

/-! # From the signed-subset certificate to real star-neuron identities -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- The actual chain vector of the masked modular gradient. -/
def maskedGamma (T : Fin 16) (p : Fin 120) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun j => evalForm ((maskedChain T p j).form subsetForms) z

noncomputable def starXi (gamma : Fin 4 → ℝ) : ℝ :=
  xi coarseForms starOmega starKappa gamma

def maskedXiCoefficients (T : Fin 16) (p : Fin 120) (s : Fin 15 → Sign) :
    RationalForm 4 :=
  xiCoefficients subsetForms starOmega starKappa (maskedChain T p) (maskedCoarse T p) s

theorem maskedXi_linearization (T : Fin 16) (p : Fin 120) (z : Fin 4 → ℝ) :
    starXi (maskedGamma T p z) =
      evalForm (maskedXiCoefficients T p (actualSigns subsetForms z)) z :=
  xi_eq_evalForm_coefficients subsetForms coarseForms starOmega starKappa
    (maskedChain T p) (maskedCoarse T p) (masked_compatible T p) z

theorem maskedGamma_zeroOutside (T : Fin 16) (p : Fin 120) (z : Fin 4 → ℝ) :
    maskedGamma 15 p (zeroOutside (maskSet T) z) = maskedGamma T p z := by
  funext j
  simp only [maskedGamma, evalForm, zeroOutside]
  apply Finset.sum_congr rfl
  intro i _
  rw [chain_masked_projection T p j i]
  split_ifs <;> simp_all

noncomputable def starPsi (P : Finset (Fin 4)) (z : Fin 4 → ℝ) : ℝ :=
  ∑ p : Fin 120, if centerBeforeMask p = setMask P then starXi (maskedGamma 15 p z) else 0

def maskedPsiCoefficients (T P : Fin 16) (s : Fin 15 → Sign) : RationalForm 4 :=
  fun i => ∑ p : Fin 120,
    if centerBeforeMask p = P then maskedXiCoefficients T p s i else 0

end MaxCaterpillar.Frontier.StarCertificate
