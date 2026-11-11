import MaxCaterpillar.Fiber.GatingAbstractions.RegularityCoordinates
import MaxCaterpillar.Fiber.GatingAbstractions
import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.GatingAbstractions.StrictEvaluation

/-! Actual finite network evaluations associated with the exact Jacobian certificate.
Generated data: research/sN/zulip_three/jacobian_base_emit.py.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace MaxCaterpillar.Fiber.GatingAbstractions
open BigOperators

abbrev Observed := Fin 28 → ℝ

def aIndices : Fin 6 → Fin 4 → Fin 45 := ![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15], ![16, 17, 18, 19], ![20, 21, 22, 23]]
def wIndices : Fin 3 → Fin 6 → Fin 45 := ![![24, 25, 26, 27, 28, 29], ![30, 31, 32, 33, 34, 35], ![36, 37, 38, 39, 40, 41]]
def dIndices : Fin 3 → Fin 45 := ![42,43,44]

noncomputable def rawW1CLM : Raw →L[ℝ] (Fin 6 → Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (aIndices j i)
noncomputable def rawW2CLM : Raw →L[ℝ] (Fin 3 → Fin 6 → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (wIndices k j)
noncomputable def rawDCLM : Raw →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (dIndices k)

noncomputable def rawParamsCLM : Raw →L[ℝ] ParameterSpace 4 6 3 :=
  rawW1CLM.prod ((0 : Raw →L[ℝ] (Fin 6 → ℝ)).prod
    (rawW2CLM.prod ((0 : Raw →L[ℝ] (Fin 3 → ℝ)).prod
      (rawDCLM.prod (0 : Raw →L[ℝ] ℝ)))))

@[simp] theorem rawW1CLM_apply (p : Raw) : rawW1CLM p = (fromRaw p).W₁ := by
  funext j i
  fin_cases j <;> fin_cases i <;> rfl
@[simp] theorem rawW2CLM_apply (p : Raw) : rawW2CLM p = (fromRaw p).W₂ := by
  funext k j
  fin_cases k <;> fin_cases j <;> rfl
@[simp] theorem rawDCLM_apply (p : Raw) : rawDCLM p = (fromRaw p).w₃ := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem rawParamsCLM_apply (p : Raw) :
    rawParamsCLM p = networkEquivParameters 4 6 3 (fromRaw p) := by
  simp only [rawParamsCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    rawW1CLM_apply, rawW2CLM_apply, rawDCLM_apply]
  rfl

noncomputable def samples : Fin 28 → Point 4 := ![![-1, 1, -1, -2], ![-1, 1, -1, 2], ![-1, 1, -1, -3], ![-1, 1, -1, 3], ![-1, 1, 1, 2], ![-1, 1, 0, -1], ![-1, 1, -2, -1], ![-1, 1, 2, -1], ![-1, 1, 2, 1], ![-1, 1, 2, -2], ![-1, 1, 3, -1], ![-1, 1, 3, 1], ![-1, 1, 3, 2], ![-1, -2, -1, 1], ![-1, -2, 1, -1], ![-1, -2, -2, -3], ![-1, -2, -2, -4], ![-1, -2, 2, 1], ![-1, -2, -3, -2], ![-1, 2, -1, 1], ![-1, 2, -1, -2], ![-1, 2, -1, 3], ![-1, -3, -1, 1], ![-1, -3, -2, -3], ![-2, -1, -2, -3], ![-2, -1, -2, -4], ![-2, -1, -3, -2], ![-3, -1, -2, -3]]

noncomputable def observations (p : Raw) : Observed :=
  fun i => (fromRaw p).eval (samples i)

noncomputable def combinedMap (p : Raw) : Raw := ![observations p 0, observations p 1, observations p 2, observations p 3, observations p 4, observations p 5, observations p 6, observations p 7, observations p 8, observations p 9, observations p 10, observations p 11, observations p 12, observations p 13, observations p 14, observations p 15, observations p 16, observations p 17, observations p 18, observations p 19, observations p 20, observations p 21, observations p 22, observations p 23, observations p 24, observations p 25, observations p 26, observations p 27, freeCoordinates p 0, freeCoordinates p 1, freeCoordinates p 2, freeCoordinates p 3, freeCoordinates p 4, freeCoordinates p 5, freeCoordinates p 6, freeCoordinates p 7, freeCoordinates p 8, freeCoordinates p 9, freeCoordinates p 10, freeCoordinates p 11, freeCoordinates p 12, freeCoordinates p 13, freeCoordinates p 14, freeCoordinates p 15, freeCoordinates p 16]

@[simp] theorem ofParams_rawParams (p : Raw) :
    Empirical.ofParams (rawParamsCLM p) = fromRaw p := by
  rw [rawParamsCLM_apply]
  exact (networkEquivParameters 4 6 3).symm_apply_apply (fromRaw p)

@[simp] theorem fromRaw_family (c : ℝ) : fromRaw (toRaw (family c)) = family c :=
  fromRaw_toRaw (family c) ⟨rfl,rfl,rfl⟩

noncomputable def familyParams (c : ℝ) : Empirical.Params :=
  rawParamsCLM (toRaw (family c))

noncomputable def firstFormula (x : Point 4) : Fin 6 → ℝ :=
  ![x 0-x 1, x 2-x 3, x 1, -x 1, x 3, -x 3]

lemma rawFirst_physical (p : Empirical.Params) (x : Point 4) (j : Fin 6) :
    Empirical.rawFirst x j p = firstPre (Empirical.ofParams p) x j := rfl

lemma rawSecond_physical (p : Empirical.Params) (x : Point 4) (k : Fin 3) :
    Empirical.rawSecond x k p = secondPre (Empirical.ofParams p) x k := rfl

@[simp] lemma rawFirst_family_apply (c : ℝ) (x : Point 4) (j : Fin 6) :
    Empirical.rawFirst x j (familyParams c) = firstFormula x j := by
  change Empirical.rawFirst x j (rawParamsCLM (toRaw (family c))) = _
  rw [rawFirst_physical, ofParams_rawParams, fromRaw_family]
  exact congrFun (family_firstPre c x) j

lemma family_W2 (c : ℝ) : (family c).W₂ =
    ![![c,2,1,1,2,1],![c,1,1,1,1,2],![1,-1,1,-1,-1,1]] := by
  funext k j
  fin_cases k <;> fin_cases j <;>
    norm_num [family, splitNet, pairedNet, pairedOuterCoefficients, offset,
      Matrix.cons_val_zero', Matrix.cons_val_succ']

noncomputable def secondFormula (c : ℝ) (x : Point 4) : Fin 3 → ℝ :=
  ![c*relu (x 0-x 1)+2*relu (x 2-x 3)+relu (x 1)+relu (-x 1)+2*relu (x 3)+relu (-x 3),
    c*relu (x 0-x 1)+relu (x 2-x 3)+relu (x 1)+relu (-x 1)+relu (x 3)+2*relu (-x 3),
    relu (x 0-x 1)-relu (x 2-x 3)+relu (x 1)-relu (-x 1)-relu (x 3)+relu (-x 3)]

@[simp] lemma rawSecond_family_apply (c : ℝ) (x : Point 4) (k : Fin 3) :
    Empirical.rawSecond x k (familyParams c) = secondFormula c x k := by
  change Empirical.rawSecond x k (rawParamsCLM (toRaw (family c))) = _
  rw [rawSecond_physical, ofParams_rawParams, fromRaw_family]
  unfold secondPre
  rw [family_W2, family_firstHidden]
  fin_cases k <;>
    norm_num [family, splitNet, pairedNet, pairedFeatures,
      secondFormula, Fin.sum_univ_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring

@[simp] lemma vec4_last (a b c d : ℝ) : (![a,b,c,d] : Point 4) 3 = d := rfl

lemma relu_pair_positive (t : ℝ) (ht : t ≠ 0) : 0 < relu t + relu (-t) := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Frontier.relu_of_nonpos h.le,
      Frontier.relu_of_nonneg (neg_nonneg.mpr h.le)]
    linarith
  · rw [Frontier.relu_of_nonneg h.le,
      Frontier.relu_of_nonpos (neg_nonpos.mpr h.le)]
    linarith

lemma baseline_positive (c : ℝ) (hc : 0 < c) (x : Point 4) (hx : x 1 ≠ 0) :
    0 < secondFormula c x 0 ∧ 0 < secondFormula c x 1 := by
  have ha := relu_pair_positive (x 1) hx
  have hq := mul_nonneg hc.le (Frontier.relu_nonneg (x 0-x 1))
  have hr := Frontier.relu_nonneg (x 2-x 3)
  have hp := Frontier.relu_nonneg (x 3)
  have hn := Frontier.relu_nonneg (-x 3)
  constructor <;> simp only [secondFormula, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two] <;> linarith only [ha,hq,hr,hp,hn]

lemma samples_anchor_nonzero (s : Fin 28) : samples s 1 ≠ 0 := by
  fin_cases s <;> norm_num [samples, Matrix.cons_val_zero', Matrix.cons_val_succ']

lemma first_samples_strict (c : ℝ) (s : Fin 28) (j : Fin 6) :
    Empirical.rawFirst (samples s) j (familyParams c) ≠ 0 := by
  rw [rawFirst_family_apply]
  fin_cases s <;> fin_cases j <;>
    norm_num [firstFormula, samples, vec4_last, Matrix.cons_val_zero', Matrix.cons_val_succ']

lemma second_samples_strict (c : ℝ) (hc : 0 < c) (s : Fin 28) (k : Fin 3) :
    Empirical.rawSecond (samples s) k (familyParams c) ≠ 0 := by
  rw [rawSecond_family_apply]
  have hpos := baseline_positive c hc (samples s) (samples_anchor_nonzero s)
  fin_cases k
  · exact ne_of_gt hpos.1
  · exact ne_of_gt hpos.2
  · fin_cases s <;>
      norm_num [secondFormula, samples, relu, vec4_last,
        Matrix.cons_val_zero', Matrix.cons_val_succ']

end MaxCaterpillar.Fiber.GatingAbstractions
