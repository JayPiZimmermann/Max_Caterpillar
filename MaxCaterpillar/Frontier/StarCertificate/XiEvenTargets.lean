import MaxCaterpillar.Frontier.StarCertificate.XiTargets
import MaxCaterpillar.Frontier.StarCertificate.XiProfiles
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate

/-- Coefficient vectors reverse sign when all resonance signs reverse. -/
theorem starAnovaIntegerCoefficients_opposite (s : Fin 15 → Sign) (t : Fin 80) (i : Fin 4) :
    starAnovaIntegerCoefficients (fun j => (s j).opposite) t i =
      -starAnovaIntegerCoefficients s t i :=
  componentIntegerCoefficients_opposite _ _ s i

theorem starAnovaCoefficients_opposite (s : Fin 15 → Sign) (t : Fin 80) :
    starAnovaCoefficients (fun j => (s j).opposite) t =
      fun i => -(starAnovaCoefficients s t i) := by
  funext i
  rw [← starAnovaIntegerCoefficients_cast, starAnovaIntegerCoefficients_opposite,
    Int.cast_neg, starAnovaIntegerCoefficients_cast]

/-- The actual anchored target is even on all real inputs. Thus a checked
nonpositive half-space suffices, including every equality boundary. -/
theorem starAnova_eval_neg (z : Fin 4 → ℝ) (t : Fin 80) :
    evalForm (starAnovaCoefficients (actualSigns subsetForms (fun i => -z i)) t) (fun i => -z i) =
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z := by
  rw [actualSigns_neg, starAnovaCoefficients_opposite, evalForm_neg, evalForm_neg_input, neg_neg]

theorem starAnova_all_real_of_nonpositive
    (hhalf : ∀ (z : Fin 4 → ℝ), z 0 ≤ 0 → ∀ (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0) :
    ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z = 0 := by
  intro z t
  by_cases hz : z 0 ≤ 0
  · exact hhalf z hz t
  · rw [← starAnova_eval_neg z t]
    apply hhalf (fun i => -z i) _ t
    change -z 0 ≤ 0
    exact neg_nonpos.mpr (lt_of_not_ge hz).le

end MaxCaterpillar.Frontier.StarCertificate
