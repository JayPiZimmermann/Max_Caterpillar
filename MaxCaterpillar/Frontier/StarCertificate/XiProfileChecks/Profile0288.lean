import MaxCaterpillar.Frontier.StarCertificate.XiProfiles
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0276
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0288
def pattern : Fin 15 → Sign := ![.zero, .zero, .zero, .pos, .zero, .zero, .zero, .pos, .zero, .zero, .zero, .pos, .zero, .zero, .zero]
def psi (P : Fin 16) (i : Fin 4) : ℤ := -XiProfileChecks.Profile0276.psi P i
theorem pattern_opposite : pattern = fun j => (XiProfileChecks.Profile0276.pattern j).opposite := by decide
theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients 12 P pattern i = psi P i := by
  rw [pattern_opposite, maskedPsiIntegerCoefficients_opposite, XiProfileChecks.Profile0276.actual_profile]
  rfl
end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile0288
