import MaxCaterpillar.Frontier.StarCertificate.XiAnova
import MaxCaterpillar.Frontier.StarCertificate.XiPairs
import MaxCaterpillar.Frontier.StarCertificate.XiInteger

/-! # The concrete eighty targets consumed by the finite checker -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

def starAnovaCoefficients (s : Fin 15 → Sign) (t : Fin 80) : RationalForm 4 :=
  componentCoefficients (maskSet (pairS t)) (maskSet (pairA t)) s

def starAnovaIntegerCoefficients (s : Fin 15 → Sign) (t : Fin 80) : IntegerForm 4 :=
  componentIntegerCoefficients (maskSet (pairS t)) (maskSet (pairA t)) s

theorem maskedPsiIntegerCoefficients_cast (T P : Fin 16) (s : Fin 15 → Sign) (i : Fin 4) :
    (maskedPsiIntegerCoefficients T P s i : ℚ) = maskedPsiCoefficients T P s i := by
  unfold maskedPsiIntegerCoefficients maskedPsiCoefficients
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : centerBeforeMask p = P
  · simp only [if_pos hp]
    exact maskedXiIntegerCoefficients_cast T p s i
  · simp only [if_neg hp, Int.cast_zero]

theorem componentIntegerCoefficients_cast (S A : Finset (Fin 4)) (s : Fin 15 → Sign) (i : Fin 4) :
    (componentIntegerCoefficients S A s i : ℚ) = componentCoefficients S A s i := by
  simp only [componentIntegerCoefficients, componentCoefficients, Int.cast_sum,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, maskedPsiIntegerCoefficients_cast]

theorem starAnovaIntegerCoefficients_cast (s : Fin 15 → Sign) (t : Fin 80) (i : Fin 4) :
    (starAnovaIntegerCoefficients s t i : ℚ) = starAnovaCoefficients s t i :=
  componentIntegerCoefficients_cast _ _ s i

/-- Assembly helper: the checked coefficient identities imply the actual
all-real eight-slope star identity. The certificate checker discharges the
explicit coefficient premise; it is not part of the final obstruction. -/
theorem star_anova_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0)
    (v v' : Fin 4 → ℝ) :
    (∑ P in (Finset.univ : Finset (Fin 4)).powerset, starPsi P (mixed P v v')) = 0 := by
  apply anchored_sum_eq_zero starPsi starPsi_zero
  intro S A hS hA z
  obtain ⟨t, hs, ha⟩ := pair_cover S A hS hA
  rw [component_linearization]
  simpa only [starAnovaCoefficients, hs, ha] using hcoeff z t

end MaxCaterpillar.Frontier.StarCertificate
