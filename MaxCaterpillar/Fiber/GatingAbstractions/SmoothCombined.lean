import MaxCaterpillar.Fiber.GatingAbstractions.SmoothEvaluation
import MaxCaterpillar.Fiber.GatingAbstractions.RegularityJacobianData

/-! # Smoothness of the actual finite observation/free-coordinate map -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace MaxCaterpillar.Fiber.GatingAbstractions

lemma combinedMap_head (p : Raw) (i : Fin 28) :
    combinedMap p (Fin.castAdd 17 i) = observations p i := by
  fin_cases i <;> rfl

lemma combinedMap_tail (p : Raw) (i : Fin 17) :
    combinedMap p (Fin.natAdd 28 i) = freeCoordinates p i := by
  fin_cases i <;> rfl

lemma smooth_observation (c : ℝ) (hc : 0 < c) (i : Fin 28) :
    ContDiffAt ℝ ⊤ (fun p => observations p i) (toRaw (family c)) := by
  have h := Empirical.contDiffAt_eval (familyParams c) (samples i)
    (first_samples_strict c i) (second_samples_strict c hc i)
  have hcomp := h.comp (toRaw (family c)) rawParamsCLM.contDiff.contDiffAt
  simpa only [ofParams_rawParams] using hcomp

/-- The combined map is infinitely differentiable at every positive member of
our physical family, before invoking any inverse certificate. -/
theorem smooth_combined (c : ℝ) (hc : 0 < c) :
    ContDiffAt ℝ ⊤ combinedMap (toRaw (family c)) := by
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.addCases (m := 28) (n := 17)
    (motive := fun j => ContDiffAt ℝ ⊤ (fun p => combinedMap p j)
      (toRaw (family c))) ?_ ?_ i
  · intro j
    simpa only [combinedMap_head] using smooth_observation c hc j
  · intro j
    simpa only [combinedMap_tail, freeCoordinates] using
      (ContinuousLinearMap.proj (freeIndices j) : Raw →L[ℝ] ℝ).contDiff.contDiffAt

#print axioms smooth_combined
end MaxCaterpillar.Fiber.GatingAbstractions
