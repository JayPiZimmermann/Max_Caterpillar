import MaxCaterpillar.Fiber.GatingAbstractions.RegularityJacobianData

/-! The strict derivative of actual finite observations equals the certified
invertible map. This is the model bridge from the inverse certificate to the
ordinary bias-free network parameters. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace MaxCaterpillar.Fiber.GatingAbstractions
open BigOperators

noncomputable def observationD (c : ℝ) (i : Fin 28) : Raw →L[ℝ] ℝ :=
  (Empirical.evalD (familyParams c) (samples i)).comp rawParamsCLM

lemma strict_observation (c : ℝ) (hc : 0 < c) (i : Fin 28) :
    HasStrictFDerivAt (fun p => observations p i) (observationD c i)
      (toRaw (family c)) := by
  have h := Empirical.hasStrictFDerivAt_eval (familyParams c) (samples i)
    (first_samples_strict c i) (second_samples_strict c hc i)
  have hcomp := h.comp (toRaw (family c)) rawParamsCLM.hasStrictFDerivAt
  simpa only [ofParams_rawParams] using hcomp

noncomputable def combinedD (c : ℝ) : Raw →L[ℝ] Raw :=
  ContinuousLinearMap.pi ![observationD c 0, observationD c 1, observationD c 2, observationD c 3, observationD c 4, observationD c 5, observationD c 6, observationD c 7, observationD c 8, observationD c 9, observationD c 10, observationD c 11, observationD c 12, observationD c 13, observationD c 14, observationD c 15, observationD c 16, observationD c 17, observationD c 18, observationD c 19, observationD c 20, observationD c 21, observationD c 22, observationD c 23, observationD c 24, observationD c 25, observationD c 26, observationD c 27, ContinuousLinearMap.proj (freeIndices 0), ContinuousLinearMap.proj (freeIndices 1), ContinuousLinearMap.proj (freeIndices 2), ContinuousLinearMap.proj (freeIndices 3), ContinuousLinearMap.proj (freeIndices 4), ContinuousLinearMap.proj (freeIndices 5), ContinuousLinearMap.proj (freeIndices 6), ContinuousLinearMap.proj (freeIndices 7), ContinuousLinearMap.proj (freeIndices 8), ContinuousLinearMap.proj (freeIndices 9), ContinuousLinearMap.proj (freeIndices 10), ContinuousLinearMap.proj (freeIndices 11), ContinuousLinearMap.proj (freeIndices 12), ContinuousLinearMap.proj (freeIndices 13), ContinuousLinearMap.proj (freeIndices 14), ContinuousLinearMap.proj (freeIndices 15), ContinuousLinearMap.proj (freeIndices 16)]

lemma strict_combined (c : ℝ) (hc : 0 < c) :
    HasStrictFDerivAt combinedMap (combinedD c) (toRaw (family c)) := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i <;> first
    | exact strict_observation c hc _
    | exact (ContinuousLinearMap.proj (_ : Fin 45) : Raw →L[ℝ] ℝ).hasStrictFDerivAt

@[simp] lemma pointOfParams (c : ℝ) : Empirical.ofParams (familyParams c) = family c := by
  rw [familyParams, ofParams_rawParams, fromRaw_family]

@[simp] lemma family_output (c : ℝ) : (family c).w₃ = ![1,-1,1] := rfl
@[simp] lemma fromRaw_b1 (v : Raw) (j : Fin 6) : (fromRaw v).b₁ j = 0 := rfl
@[simp] lemma fromRaw_b2 (v : Raw) (k : Fin 3) : (fromRaw v).b₂ k = 0 := rfl
@[simp] lemma fromRaw_b3 (v : Raw) : (fromRaw v).b₃ = 0 := rfl

lemma fromRaw_W1 (v : Raw) (j : Fin 6) (i : Fin 4) :
    (fromRaw v).W₁ j i = v (aIndices j i) := by
  fin_cases j <;> fin_cases i <;> rfl
lemma fromRaw_W2 (v : Raw) (k : Fin 3) (j : Fin 6) :
    (fromRaw v).W₂ k j = v (wIndices k j) := by
  fin_cases k <;> fin_cases j <;> rfl
lemma fromRaw_out (v : Raw) (k : Fin 3) : (fromRaw v).w₃ k = v (dIndices k) := by
  fin_cases k <;> rfl

noncomputable def firstDirection (x : Point 4) (j : Fin 6) (v : Raw) : ℝ :=
  ∑ i, x i * (fromRaw v).W₁ j i

noncomputable def secondDirection (c : ℝ) (x : Point 4) (k : Fin 3) (v : Raw) : ℝ :=
  ∑ j, ((family c).W₂ k j *
      (if 0 < firstFormula x j then firstDirection x j v else 0) +
    relu (firstFormula x j) * (fromRaw v).W₂ k j)

noncomputable def directionFormula (c : ℝ) (x : Point 4) (v : Raw) : ℝ :=
  ∑ k, ((family c).w₃ k *
      (if 0 < secondFormula c x k then secondDirection c x k v else 0) +
    relu (secondFormula c x k) * (fromRaw v).w₃ k)

lemma firstD_on_raw (c : ℝ) (x : Point 4) (j : Fin 6) (v : Raw) :
    Empirical.firstD (familyParams c) x j (rawParamsCLM v) =
      if 0 < firstFormula x j then firstDirection x j v else 0 := by
  unfold Empirical.firstD
  rw [rawFirst_family_apply]
  split_ifs
  · simp only [Empirical.rawFirstD, firstDirection,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      Empirical.w1coord_apply, Empirical.b1coord_apply,
      ofParams_rawParams, fromRaw_b1, add_zero]
  · rfl

lemma secondD_on_raw (c : ℝ) (x : Point 4) (k : Fin 3) (v : Raw) :
    Empirical.secondD (familyParams c) x k (rawParamsCLM v) =
      if 0 < secondFormula c x k then secondDirection c x k v else 0 := by
  unfold Empirical.secondD
  rw [rawSecond_family_apply]
  split_ifs
  · simp only [Empirical.rawSecondD, secondDirection,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      Empirical.w2coord_apply, Empirical.b2coord_apply,
      firstD_on_raw, rawFirst_family_apply, pointOfParams,
      ofParams_rawParams, fromRaw_b2, add_zero]
  · rfl

lemma observationD_formula (c : ℝ) (i : Fin 28) (v : Raw) :
    observationD c i v = directionFormula c (samples i) v := by
  simp only [observationD, ContinuousLinearMap.comp_apply, Empirical.evalD,
    directionFormula, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    Empirical.w3coord_apply, Empirical.b3coord_apply,
    secondD_on_raw, rawSecond_family_apply, pointOfParams,
    ofParams_rawParams, fromRaw_b3, add_zero]


#print axioms strict_combined
#print axioms observationD_formula
end MaxCaterpillar.Fiber.GatingAbstractions
