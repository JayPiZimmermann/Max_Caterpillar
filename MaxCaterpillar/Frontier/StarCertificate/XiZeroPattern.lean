import MaxCaterpillar.Frontier.StarCertificate.XiTargets
import MaxCaterpillar.Frontier.StarCertificate.XiProfiles
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def zeroResonancePattern : Fin 15 → Sign := fun _ => .zero

theorem FormRef.sign_zeroPattern {m : ℕ} (r : FormRef m) :
    r.sign (fun _ => .zero) = .zero := by
  cases r <;> rfl

theorem maskedXiIntegerCoefficients_zeroPattern (T : Fin 16) (p : Fin 120) (i : Fin 4) :
    maskedXiIntegerCoefficients T p zeroResonancePattern i = 0 := by
  unfold maskedXiIntegerCoefficients zeroResonancePattern
  simp [FormRef.sign_zeroPattern,headSign,Sign.integerDirection]

theorem maskedPsiIntegerCoefficients_zeroPattern (T P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients T P zeroResonancePattern i = 0 := by
  simp only [maskedPsiIntegerCoefficients,maskedXiIntegerCoefficients_zeroPattern,
    ite_self,Finset.sum_const_zero]

theorem componentIntegerCoefficients_zeroPattern (S A : Finset (Fin 4)) (i : Fin 4) :
    componentIntegerCoefficients S A zeroResonancePattern i = 0 := by
  simp only [componentIntegerCoefficients,maskedPsiIntegerCoefficients_zeroPattern,
    Finset.sum_const_zero,mul_zero]

theorem starAnovaIntegerCoefficients_zeroPattern :
    starAnovaIntegerCoefficients zeroResonancePattern = 0 := by
  funext t i
  exact componentIntegerCoefficients_zeroPattern _ _ i

end MaxCaterpillar.Frontier.StarCertificate
