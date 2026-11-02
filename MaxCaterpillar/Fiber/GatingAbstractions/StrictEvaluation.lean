import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Frontier.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Strict differentiation in the full ordinary Max4 parameter space

All 55 ordinary real parameters, including biases, may vary. This supplies
the explicit derivative of actual network evaluation away from switching gates.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.GatingAbstractions.Empirical
open BigOperators Filter Topology

abbrev Params := ParameterSpace 4 6 3

noncomputable def ofParams (p : Params) : Network 4 6 3 :=
  (networkEquivParameters 4 6 3).symm p

noncomputable def w1coord (j : Fin 6) (i : Fin 4) : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.proj j : (Fin 6 → Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)).comp
      (ContinuousLinearMap.fst ℝ _ _))
noncomputable def b1coord (j : Fin 6) : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
noncomputable def w2coord (k : Fin 3) (j : Fin 6) : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 6 → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.proj k : (Fin 3 → Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℝ)).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))
noncomputable def b2coord (k : Fin 3) : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp ((ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))
noncomputable def w3coord (k : Fin 3) : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp ((ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))))
noncomputable def b3coord : Params →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      (ContinuousLinearMap.snd ℝ _ _))))

@[simp] lemma w1coord_apply (p : Params) (j : Fin 6) (i : Fin 4) :
    w1coord j i p = (ofParams p).W₁ j i := rfl
@[simp] lemma b1coord_apply (p : Params) (j : Fin 6) :
    b1coord j p = (ofParams p).b₁ j := rfl
@[simp] lemma w2coord_apply (p : Params) (k : Fin 3) (j : Fin 6) :
    w2coord k j p = (ofParams p).W₂ k j := rfl
@[simp] lemma b2coord_apply (p : Params) (k : Fin 3) :
    b2coord k p = (ofParams p).b₂ k := rfl
@[simp] lemma w3coord_apply (p : Params) (k : Fin 3) :
    w3coord k p = (ofParams p).w₃ k := rfl
@[simp] lemma b3coord_apply (p : Params) : b3coord p = (ofParams p).b₃ := rfl

/-- ReLU preserves the strict derivative away from its switching value. -/
private theorem strict_relu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {p : E}
    (hf : HasStrictFDerivAt f f' p) (hp : f p ≠ 0) :
    HasStrictFDerivAt (fun q => relu (f q)) (if 0 < f p then f' else 0) p := by
  by_cases hpos : 0 < f p
  · rw [if_pos hpos]
    apply hf.congr_of_eventuallyEq
    filter_upwards [hf.hasFDerivAt.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
    exact (Frontier.relu_of_nonneg hq.le).symm
  · rw [if_neg hpos]
    apply (hasStrictFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq
    have hneg : f p < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hp
    filter_upwards [hf.hasFDerivAt.continuousAt.eventually (gt_mem_nhds hneg)] with q hq
    exact (Frontier.relu_of_nonpos hq.le).symm

noncomputable def rawFirst (x : Point 4) (j : Fin 6) (p : Params) : ℝ :=
  (∑ i, w1coord j i p * x i) + b1coord j p
noncomputable def rawFirstD (x : Point 4) (j : Fin 6) : Params →L[ℝ] ℝ :=
  (∑ i, x i • w1coord j i) + b1coord j
noncomputable def firstD (p : Params) (x : Point 4) (j : Fin 6) : Params →L[ℝ] ℝ :=
  if 0 < rawFirst x j p then rawFirstD x j else 0
noncomputable def rawSecond (x : Point 4) (k : Fin 3) (p : Params) : ℝ :=
  (∑ j, w2coord k j p * relu (rawFirst x j p)) + b2coord k p
noncomputable def rawSecondD (p : Params) (x : Point 4) (k : Fin 3) : Params →L[ℝ] ℝ :=
  (∑ j, ((w2coord k j p) • firstD p x j +
    relu (rawFirst x j p) • w2coord k j)) + b2coord k
noncomputable def secondD (p : Params) (x : Point 4) (k : Fin 3) : Params →L[ℝ] ℝ :=
  if 0 < rawSecond x k p then rawSecondD p x k else 0
noncomputable def evalD (p : Params) (x : Point 4) : Params →L[ℝ] ℝ :=
  (∑ k, ((w3coord k p) • secondD p x k +
    relu (rawSecond x k p) • w3coord k)) + b3coord

lemma strict_rawFirst (x : Point 4) (j : Fin 6) (p : Params) :
    HasStrictFDerivAt (rawFirst x j) (rawFirstD x j) p := by
  exact (HasStrictFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (w1coord j i).hasStrictFDerivAt.mul_const (x i))).add (b1coord j).hasStrictFDerivAt

/-- Actual network evaluation has the displayed strict derivative whenever all
physical preactivations at the observed input are nonzero. -/
theorem hasStrictFDerivAt_eval (p : Params) (x : Point 4)
    (hfirst : ∀ j, rawFirst x j p ≠ 0) (hsecond : ∀ k, rawSecond x k p ≠ 0) :
    HasStrictFDerivAt (fun q => (ofParams q).eval x) (evalD p x) p := by
  have hf : ∀ j, HasStrictFDerivAt (fun q => relu (rawFirst x j q)) (firstD p x j) p :=
    fun j => strict_relu (strict_rawFirst x j p) (hfirst j)
  have hs : ∀ k, HasStrictFDerivAt (rawSecond x k) (rawSecondD p x k) p := by
    intro k
    exact (HasStrictFDerivAt.sum (u := Finset.univ) (fun j _ => (w2coord k j).hasStrictFDerivAt.mul (hf j))).add
      (b2coord k).hasStrictFDerivAt
  have hr : ∀ k, HasStrictFDerivAt (fun q => relu (rawSecond x k q)) (secondD p x k) p :=
    fun k => strict_relu (hs k) (hsecond k)
  exact (HasStrictFDerivAt.sum (u := Finset.univ) (fun k _ => (w3coord k).hasStrictFDerivAt.mul (hr k))).add
    b3coord.hasStrictFDerivAt

end MaxCaterpillar.Fiber.GatingAbstractions.Empirical
