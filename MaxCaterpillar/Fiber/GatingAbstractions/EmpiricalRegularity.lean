import MaxCaterpillar.Fiber.GatingAbstractions
import MaxCaterpillar.Fiber.GatingAbstractions.StrictEvaluation
import MaxCaterpillar.Fiber.GatingAbstractions.Regularity
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank

/-! The four observations are strict on every positive common-offset point.
The proof uses the full parameter space, so all biases remain free. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.GatingAbstractions.Empirical
open BigOperators Frontier

noncomputable def samples : Fin 4 → Point 4 := ![inputX,inputY,inputZ,inputW]
noncomputable def familyPoint (c : ℝ) : Params := networkEquivParameters 4 6 3 (family c)

@[simp] lemma ofParams_familyPoint (c : ℝ) : ofParams (familyPoint c) = family c := by
  exact (networkEquivParameters 4 6 3).symm_apply_apply (family c)

lemma rawFirst_eq (x : Point 4) (j : Fin 6) (p : Params) :
    rawFirst x j p = firstPre (ofParams p) x j := rfl
lemma rawSecond_eq (x : Point 4) (k : Fin 3) (p : Params) :
    rawSecond x k p = secondPre (ofParams p) x k := rfl

lemma first_strict (c : ℝ) (i : Fin 4) (j : Fin 6) :
    rawFirst (samples i) j (familyPoint c) ≠ 0 := by
  rw [rawFirst_eq, ofParams_familyPoint]
  fin_cases i
  · change firstPre (family c) inputX j ≠ 0
    rw [show firstPre (family c) inputX j = (![1,2,1,-1,1,-1] : Fin 6 → ℝ) j from
      congrFun (firstPre_inputX c) j]
    fin_cases j <;> norm_num
  · change firstPre (family c) inputY j ≠ 0
    rw [show firstPre (family c) inputY j = (![1/2,2,3/2,-3/2,1,-1] : Fin 6 → ℝ) j from
      congrFun (firstPre_inputY c) j]
    fin_cases j <;> norm_num
  · change firstPre (family c) inputZ j ≠ 0
    rw [show firstPre (family c) inputZ j = (![1/2,2,2,-2,1,-1] : Fin 6 → ℝ) j from
      congrFun (firstPre_inputZ c) j]
    fin_cases j <;> norm_num
  · change firstPre (family c) inputW j ≠ 0
    rw [show firstPre (family c) inputW j = (![4,2,1,-1,1,-1] : Fin 6 → ℝ) j from
      congrFun (firstPre_inputW c) j]
    fin_cases j <;> norm_num

lemma second_strict (c : ℝ) (hc : 0 < c) (i : Fin 4) (k : Fin 3) :
    rawSecond (samples i) k (familyPoint c) ≠ 0 := by
  rw [rawSecond_eq, ofParams_familyPoint]
  fin_cases i
  · change secondPre (family c) inputX k ≠ 0
    rw [show secondPre (family c) inputX k = (![c+7,c+4,-1] : Fin 3 → ℝ) k from
      congrFun (secondPre_inputX c) k]
    fin_cases k <;> norm_num <;> linarith
  · change secondPre (family c) inputY k ≠ 0
    rw [show secondPre (family c) inputY k = (![c/2+15/2,c/2+9/2,-1] : Fin 3 → ℝ) k from
      congrFun (secondPre_inputY c) k]
    fin_cases k <;> norm_num <;> linarith
  · change secondPre (family c) inputZ k ≠ 0
    rw [show secondPre (family c) inputZ k = (![c/2+8,c/2+5,-1/2] : Fin 3 → ℝ) k from
      congrFun (secondPre_inputZ c) k]
    fin_cases k <;> norm_num <;> linarith
  · change secondPre (family c) inputW k ≠ 0
    rw [show secondPre (family c) inputW k = (![4*c+7,4*c+4,2] : Fin 3 → ℝ) k from
      congrFun (secondPre_inputW c) k]
    fin_cases k <;> norm_num <;> linarith

lemma second_zero_pos (c : ℝ) (hc : 0 < c) (i : Fin 4) :
    0 < rawSecond (samples i) 0 (familyPoint c) := by
  rw [rawSecond_eq, ofParams_familyPoint]
  fin_cases i
  · change 0 < secondPre (family c) inputX 0
    rw [show secondPre (family c) inputX 0 = c+7 from congrFun (secondPre_inputX c) 0]
    linarith
  · change 0 < secondPre (family c) inputY 0
    rw [show secondPre (family c) inputY 0 = c/2+15/2 from congrFun (secondPre_inputY c) 0]
    linarith
  · change 0 < secondPre (family c) inputZ 0
    rw [show secondPre (family c) inputZ 0 = c/2+8 from congrFun (secondPre_inputZ c) 0]
    linarith
  · change 0 < secondPre (family c) inputW 0
    rw [show secondPre (family c) inputW 0 = 4*c+7 from congrFun (secondPre_inputW c) 0]
    linarith

/-- The ordinary output evaluation map on the four declared inputs. -/
noncomputable def observations (p : Params) : Fin 4 → ℝ :=
  fun i => (ofParams p).eval (samples i)
noncomputable def observationsD (p : Params) : Params →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun i => evalD p (samples i)

/-- The strict derivative is in the full 55-dimensional ambient space. -/
theorem hasStrictFDerivAt_observations (c : ℝ) (hc : 0 < c) :
    HasStrictFDerivAt observations (observationsD (familyPoint c)) (familyPoint c) := by
  exact hasStrictFDerivAt_pi.mpr fun i =>
    hasStrictFDerivAt_eval (familyPoint c) (samples i) (first_strict c i) (second_strict c hc i)

/-- Four independent physical parameter directions: three weights into the
positive baseline neuron, and the comparison neuron's output weight. -/
noncomputable def lift (v : Fin 4 → ℝ) : Params :=
  (0, 0,
    (fun k j => if k = 0 then
      if j = 0 then v 0 else if j = 2 then v 1 else if j = 1 then v 2 else 0
      else 0),
    0, (fun k => if k = 2 then v 3 else 0), 0)

@[simp] lemma lift_W1 (v : Fin 4 → ℝ) (j : Fin 6) (i : Fin 4) :
    (ofParams (lift v)).W₁ j i = 0 := rfl
@[simp] lemma lift_b1 (v : Fin 4 → ℝ) (j : Fin 6) :
    (ofParams (lift v)).b₁ j = 0 := rfl
@[simp] lemma lift_b2 (v : Fin 4 → ℝ) (k : Fin 3) :
    (ofParams (lift v)).b₂ k = 0 := rfl
@[simp] lemma lift_b3 (v : Fin 4 → ℝ) : (ofParams (lift v)).b₃ = 0 := rfl
@[simp] lemma lift_W2 (v : Fin 4 → ℝ) (k : Fin 3) (j : Fin 6) :
    (ofParams (lift v)).W₂ k j = if k = 0 then
      if j = 0 then v 0 else if j = 2 then v 1 else if j = 1 then v 2 else 0 else 0 := rfl
@[simp] lemma lift_w3 (v : Fin 4 → ℝ) (k : Fin 3) :
    (ofParams (lift v)).w₃ k = if k = 2 then v 3 else 0 := rfl

lemma rawFirstD_lift (x : Point 4) (j : Fin 6) (v : Fin 4 → ℝ) :
    rawFirstD x j (lift v) = 0 := by
  simp [rawFirstD]

lemma firstD_lift (p : Params) (x : Point 4) (j : Fin 6) (v : Fin 4 → ℝ) :
    firstD p x j (lift v) = 0 := by
  unfold firstD
  split_ifs <;> simp [rawFirstD_lift]

lemma rawSecondD_lift (p : Params) (x : Point 4) (k : Fin 3) (v : Fin 4 → ℝ) :
    rawSecondD p x k (lift v) =
      if k = 0 then
        relu (rawFirst x 0 p) * v 0 + relu (rawFirst x 2 p) * v 1 +
          relu (rawFirst x 1 p) * v 2 else 0 := by
  simp only [rawSecondD, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, firstD_lift, mul_zero, zero_add,
    w2coord_apply, b2coord_apply, lift_W2, lift_b2]
  fin_cases k <;> norm_num [Fin.sum_univ_succ, Fin.ext_iff] <;> ring

lemma evalD_lift (p : Params) (x : Point 4) (hp : 0 < rawSecond x 0 p)
    (v : Fin 4 → ℝ) :
    evalD p x (lift v) =
      (ofParams p).w₃ 0 * ((ofParams p).firstHidden x 0 * v 0 +
        (ofParams p).firstHidden x 2 * v 1 + (ofParams p).firstHidden x 1 * v 2) +
        (ofParams p).secondHidden x 2 * v 3 := by
  change evalD p x (lift v) = w3coord 0 p *
    (relu (rawFirst x 0 p)*v 0+relu (rawFirst x 2 p)*v 1+relu (rawFirst x 1 p)*v 2)+
      relu (rawSecond x 2 p)*v 3
  simp only [evalD, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, w3coord_apply, b3coord_apply, lift_b3]
  have hgate : ∀ k, secondD p x k (lift v) =
      if 0 < rawSecond x k p then rawSecondD p x k (lift v) else 0 := by
    intro k
    unfold secondD
    split_ifs <;> rfl
  simp_rw [hgate, rawSecondD_lift]
  norm_num [Fin.sum_univ_succ, Fin.ext_iff, hp, lift_w3]

/-- The four-by-four physical Jacobian minor, independent of c. -/
noncomputable def minor (v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if i.val = 0 then v 0+v 1+2*v 2 else
  if i.val = 1 then v 0/2+3*v 1/2+2*v 2 else
  if i.val = 2 then v 0/2+2*v 1+2*v 2 else
    4*v 0+v 1+2*v 2+2*v ⟨3,by decide⟩

lemma observationsD_lift (c : ℝ) (hc : 0 < c) (v : Fin 4 → ℝ) :
    observationsD (familyPoint c) (lift v) = minor v := by
  funext i
  change evalD (familyPoint c) (samples i) (lift v) = minor v i
  rw [evalD_lift _ _ (second_zero_pos c hc i), ofParams_familyPoint, family_firstHidden]
  have hw : (family c).w₃ 0 = 1 := rfl
  rw [hw, one_mul]
  fin_cases i
  · change pairedFeatures inputX 0*v 0+pairedFeatures inputX 2*v 1+
      pairedFeatures inputX 1*v 2+(family c).secondHidden inputX 2*v 3 = minor v ⟨0,by decide⟩
    rw [pairedFeatures_inputX]
    have hD : (family c).secondHidden inputX 2 = 0 := by
      exact congrFun (secondHidden_inputX c hc.le) 2
    rw [hD]
    change 1*v 0+1*v 1+2*v 2+0*v 3 = v 0+v 1+2*v 2
    ring
  · change pairedFeatures inputY 0*v 0+pairedFeatures inputY 2*v 1+
      pairedFeatures inputY 1*v 2+(family c).secondHidden inputY 2*v 3 = minor v ⟨1,by decide⟩
    rw [pairedFeatures_inputY]
    have hD : (family c).secondHidden inputY 2 = 0 := by
      exact congrFun (secondHidden_inputY c hc.le) 2
    rw [hD]
    change (1/2)*v 0+(3/2)*v 1+2*v 2+0*v 3 = v 0/2+3*v 1/2+2*v 2
    ring
  · change pairedFeatures inputZ 0*v 0+pairedFeatures inputZ 2*v 1+
      pairedFeatures inputZ 1*v 2+(family c).secondHidden inputZ 2*v 3 = minor v ⟨2,by decide⟩
    rw [pairedFeatures_inputZ]
    have hD : (family c).secondHidden inputZ 2 = 0 := by
      exact congrFun (secondHidden_inputZ c hc.le) 2
    rw [hD]
    change (1/2)*v 0+2*v 1+2*v 2+0*v 3 = v 0/2+2*v 1+2*v 2
    ring
  · change pairedFeatures inputW 0*v 0+pairedFeatures inputW 2*v 1+
      pairedFeatures inputW 1*v 2+(family c).secondHidden inputW 2*v 3 = minor v ⟨3,by decide⟩
    rw [pairedFeatures_inputW]
    have hD : (family c).secondHidden inputW 2 = 2 := by
      change relu (secondPre (family c) inputW 2) = 2
      rw [show secondPre (family c) inputW 2 = 2 from congrFun (secondPre_inputW c) 2]
      norm_num [relu]
    rw [hD]
    change 4*v 0+1*v 1+2*v 2+2*v 3 = 4*v 0+v 1+2*v 2+2*v 3
    ring

/-- An explicit inverse avoids any determinant convention. -/
noncomputable def minorInverse (y : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  let a := 2*y 0-4*y 1+2*y 2
  let b := 2*(y 2-y 1)
  let d := (y 0-a-b)/2
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then d else
    (y ⟨3,by decide⟩-4*a-b-2*d)/2

lemma minor_rightInverse (y : Fin 4 → ℝ) : minor (minorInverse y) = y := by
  funext i
  have h3 : (3 : Fin 4).val = 3 := rfl
  fin_cases i <;> norm_num [minor, minorInverse, h3] <;> ring <;> rfl

/-- Surjectivity is proved by actual physical parameter directions. -/
theorem observationsD_surjective (c : ℝ) (hc : 0 < c) :
    Function.Surjective (observationsD (familyPoint c)) := by
  intro y
  refine ⟨lift (minorInverse y), ?_⟩
  rw [observationsD_lift c hc, minor_rightInverse]

/-- The full biased empirical fiber is regular at every positive family point. -/
theorem regular_empirical_fiber (c : ℝ) (hc : 0 < c) :
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint c)))
      {p : Params | observations p = observations (familyPoint c)} (familyPoint c) := by
  apply regular_level_set_chart observations (familyPoint c) (observationsD (familyPoint c))
    (hasStrictFDerivAt_observations c hc)
  exact LinearMap.range_eq_top.mpr (observationsD_surjective c hc)

/-- Empirical exactness on the four fixed observations, in all 55 parameters. -/
def empiricalMaxSet : Set Params :=
  {p | ∀ i, (ofParams p).eval (samples i) = Maximum 4 (samples i)}

lemma empiricalMaxSet_eq_level (c : ℝ) (hc : 0 ≤ c) :
    empiricalMaxSet = {p : Params | observations p = observations (familyPoint c)} := by
  ext p
  constructor
  · intro hp
    funext i
    change (ofParams p).eval (samples i) = (ofParams (familyPoint c)).eval (samples i)
    rw [ofParams_familyPoint, family_eval c hc]
    exact hp i
  · intro hp i
    have h := congrFun hp i
    change (ofParams p).eval (samples i) = (ofParams (familyPoint c)).eval (samples i) at h
    rw [ofParams_familyPoint, family_eval c hc] at h
    exact h

/-- The complete ordinary biased empirical Max4 fiber has a regular ambient
chart at every positive family point; no fixed-first-layer restriction is used. -/
theorem regular_empirical_max_fiber (c : ℝ) (hc : 0 < c) :
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint c))) empiricalMaxSet (familyPoint c) := by
  rw [empiricalMaxSet_eq_level c hc.le]
  exact regular_empirical_fiber c hc

lemma params_finrank : FiniteDimensional.finrank ℝ Params = 55 := by
  norm_num [Params, ParameterSpace, FiniteDimensional.finrank_pi_fintype]

/-- The local regular level set has codimension four and dimension 51. -/
theorem empirical_kernel_finrank (c : ℝ) (hc : 0 < c) :
    FiniteDimensional.finrank ℝ (LinearMap.ker (observationsD (familyPoint c))) = 51 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (observationsD (familyPoint c)).toLinearMap
  have hr : LinearMap.range (observationsD (familyPoint c)).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (observationsD_surjective c hc)
  rw [hr, finrank_top, FiniteDimensional.finrank_fin_fun, params_finrank] at h
  have hdim : 4 + FiniteDimensional.finrank ℝ
      (LinearMap.ker (observationsD (familyPoint c))) = 55 := h
  linarith only [hdim]

/-- The two different merger points lie in a fixed gate cell and are regular
points of the full biased empirical fiber. -/
theorem regular_same_gate_counterexample :
    SameCompleteGates (family 1) (family 2) ∧
    ¬ Refines (family 1).secondHidden (family 2).secondHidden ∧
    ¬ Refines (family 2).secondHidden (family 1).secondHidden ∧
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint 1))) empiricalMaxSet (familyPoint 1) ∧
    HasRegularFiberChartAt (V := Fin 4 → ℝ)
      (W := LinearMap.ker (observationsD (familyPoint 2))) empiricalMaxSet (familyPoint 2) :=
  ⟨family_same_complete_gates 1 2 (by norm_num) (by norm_num),
    family_partitions_incomparable.1, family_partitions_incomparable.2,
    regular_empirical_max_fiber 1 (by norm_num), regular_empirical_max_fiber 2 (by norm_num)⟩

#print axioms hasStrictFDerivAt_observations
#print axioms observationsD_surjective
#print axioms regular_empirical_fiber
#print axioms regular_empirical_max_fiber
#print axioms empirical_kernel_finrank
#print axioms regular_same_gate_counterexample
end MaxCaterpillar.Fiber.GatingAbstractions.Empirical
