import MaxCaterpillar.Frontier.StarCertificate.Checker.Functional
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

theorem integerSubsetForms_eq : integerForms starIntegerSubsetForms = subsetForms := by
  funext j i
  exact starIntegerSubsetForms_cast j i

/-- A checked actual coefficient table plus checked zero-span multipliers
certifies the actual real anchored expressions throughout this sign stratum. -/
theorem starAnova_stratum_sound (pattern : Fin 15 → Sign)
    (a : Fin 80 → IntegerForm 4) (den : Fin 80 → ℤ) (w : Fin 80 → Fin 15 → ℤ)
    (hspan : ∀ t, IntegerZeroSpanValid starIntegerSubsetForms
      (fun j => some (pattern j)) (a t) (den t) (w t))
    (hmatch : starAnovaIntegerCoefficients pattern = a)
    (z : Fin 4 → ℝ) (hz : actualSigns subsetForms z = pattern) : AllStarAnovaZero z := by
  have hh := integer_representative_sound starIntegerSubsetForms starAnovaIntegerCoefficients
    pattern a den w hspan hmatch z (by simpa only [integerSubsetForms_eq] using hz)
  intro t
  simpa only [integerSubsetForms_eq,starAnovaIntegerCoefficients_cast] using hh t

end MaxCaterpillar.Frontier.StarCertificate
