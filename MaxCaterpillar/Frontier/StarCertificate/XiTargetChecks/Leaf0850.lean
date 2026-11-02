import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Chunk0293
import MaxCaterpillar.Frontier.StarCertificate.XiZeroPattern
import MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeSound
namespace MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf0850
def pattern : Fin 15 → Sign := MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0293.pattern850
def coefficients : Fin 80 → IntegerForm 4 := MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0293.coeff850
theorem pattern_zero : pattern = zeroResonancePattern := by decide
theorem coefficients_zero : coefficients = 0 := rfl
theorem actual_match : starAnovaIntegerCoefficients pattern = coefficients := by
  rw [pattern_zero,starAnovaIntegerCoefficients_zeroPattern]
  exact coefficients_zero.symm
theorem stratum_sound (z : Fin 4 → ℝ) (hz : actualSigns subsetForms z = pattern) : AllStarAnovaZero z :=
  starAnova_stratum_sound pattern coefficients MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0293.den850 MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0293.lambda850
    MaxCaterpillar.Frontier.StarCertificate.Generated.Chunk0293.solvedNumeric850.2 actual_match z hz
end MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf0850
