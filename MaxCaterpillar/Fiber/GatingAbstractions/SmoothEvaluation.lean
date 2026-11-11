import MaxCaterpillar.Fiber.GatingAbstractions.StrictEvaluation
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Smoothness of actual network evaluation at strict physical gates -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.GatingAbstractions.Empirical
open BigOperators Filter Topology

private theorem smooth_relu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ ⊤ f p) (hp : f p ≠ 0) :
    ContDiffAt ℝ ⊤ (fun q => relu (f q)) p := by
  by_cases hpos : 0 < f p
  · apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
    exact Frontier.relu_of_nonneg hq.le
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hneg : f p < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hp
    filter_upwards [hf.continuousAt.eventually (gt_mem_nhds hneg)] with q hq
    exact Frontier.relu_of_nonpos hq.le

/-- Strict observed gates make actual evaluation infinitely differentiable in
all fifty-five physical parameters, including every bias. -/
theorem contDiffAt_eval (p : Params) (x : Point 4)
    (hfirst : ∀ j, rawFirst x j p ≠ 0) (hsecond : ∀ k, rawSecond x k p ≠ 0) :
    ContDiffAt ℝ ⊤ (fun q => (ofParams q).eval x) p := by
  have hraw : ∀ j, ContDiffAt ℝ ⊤ (rawFirst x j) p := by
    intro j
    exact (ContDiffAt.sum (s := Finset.univ) (fun i _ =>
      ((w1coord j i).contDiff.contDiffAt).mul (contDiffAt_const (c := x i)))).add
      (b1coord j).contDiff.contDiffAt
  have hf : ∀ j, ContDiffAt ℝ ⊤ (fun q => relu (rawFirst x j q)) p :=
    fun j => smooth_relu (hraw j) (hfirst j)
  have hs : ∀ k, ContDiffAt ℝ ⊤ (rawSecond x k) p := by
    intro k
    exact (ContDiffAt.sum (s := Finset.univ) (fun j _ =>
      ((w2coord k j).contDiff.contDiffAt).mul (hf j))).add
      (b2coord k).contDiff.contDiffAt
  have hr : ∀ k, ContDiffAt ℝ ⊤ (fun q => relu (rawSecond x k q)) p :=
    fun k => smooth_relu (hs k) (hsecond k)
  exact (ContDiffAt.sum (s := Finset.univ) (fun k _ =>
    ((w3coord k).contDiff.contDiffAt).mul (hr k))).add b3coord.contDiff.contDiffAt

#print axioms contDiffAt_eval
end MaxCaterpillar.Fiber.GatingAbstractions.Empirical
