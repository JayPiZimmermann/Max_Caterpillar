import MaxCaterpillar.Frontier.StarCertificate.XiZeroPattern
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0149
def pattern : Fin 15 → Sign := ![.zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero]
def psi : Fin 16 → IntegerForm 4 := fun _ => 0
theorem pattern_zero : pattern = zeroResonancePattern := by decide
theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients 8 P pattern i = psi P i := by
  rw [pattern_zero]
  exact maskedPsiIntegerCoefficients_zeroPattern 8 P i
end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0149
