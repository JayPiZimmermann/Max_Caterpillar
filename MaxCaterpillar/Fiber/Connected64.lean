import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Connected64.UnusedSecond
import MaxCaterpillar.Fiber.Connected64.Quadrant
import MaxCaterpillar.Fiber.Connected64.Knots
import MaxCaterpillar.Fiber.Connected64.Crossing
import MaxCaterpillar.Frontier.Constructions
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.Continuity

/-! # Explicit exact bridges at Max4 widths `(6,4)`

These are paths in the actual six-array parameter space, not paths between
sampled function values. They connect the signed and split implementations and
the two choices of outer comparison. They do not assert that every point of
the full fiber belongs to the constructed family: that requires the separate
first-layer and completion classifications.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber
namespace Connected64

open BigOperators Frontier

/-- The six activations of the fixed paired first hidden layer. -/
noncomputable def feature (x : Point 4) (j : Fin 6) : ℝ :=
  relu (∑ i, maxFourNet.W₁ j i * x i)

theorem feature_eq (x : Point 4) :
    feature x = ![relu (x 0 - x 1), relu (x 2 - x 3),
      relu (x 1), relu (-x 1), relu (x 3), relu (-x 3)] := by
  funext j
  fin_cases j <;>
    simp [feature, maxFourNet, Fin.sum_univ_succ, sub_eq_add_neg] <;> rfl

/-- A second-layer linear preactivation over the fixed first hidden layer. -/
noncomputable def form (a : Fin 6 → ℝ) (x : Point 4) : ℝ :=
  ∑ j, a j * feature x j

theorem form_add (a b : Fin 6 → ℝ) (x : Point 4) :
    form (a + b) x = form a x + form b x := by
  simp [form, add_mul, Finset.sum_add_distrib]

theorem form_sub (a b : Fin 6 → ℝ) (x : Point 4) :
    form (a - b) x = form a x - form b x := by
  simp [form, sub_mul, Finset.sum_sub_distrib]

theorem form_neg (a : Fin 6 → ℝ) (x : Point 4) :
    form (-a) x = -form a x := by
  simp [form, Finset.sum_neg_distrib]

theorem form_smul (t : ℝ) (a : Fin 6 → ℝ) (x : Point 4) :
    form (t • a) x = t * form a x := by
  simp [form, Finset.mul_sum, mul_assoc]

def leftRow : Fin 6 → ℝ := ![1, 0, 1, -1, 0, 0]
def rightRow : Fin 6 → ℝ := ![0, 1, 0, 0, 1, -1]
def negativeAnchorRow : Fin 6 → ℝ := ![0, 0, 0, 0, 0, 1]

theorem form_leftRow (x : Point 4) : form leftRow x = max (x 0) (x 1) := by
  simp only [form, feature_eq, leftRow, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  have h := relu_sub_add (x 1) (x 0)
  rw [max_comm] at h
  linarith [relu_sub_relu_neg (x 1)]

theorem form_rightRow (x : Point 4) : form rightRow x = max (x 2) (x 3) := by
  simp only [form, feature_eq, rightRow, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  have h := relu_sub_add (x 3) (x 2)
  rw [max_comm] at h
  linarith [relu_sub_relu_neg (x 3)]

theorem form_negativeAnchorRow (x : Point 4) :
    form negativeAnchorRow x = relu (-x 3) := by
  simp [form, feature_eq, negativeAnchorRow, Fin.sum_univ_succ]

/-- An ordinary network with the fixed paired first hidden layer. -/
noncomputable def pairedNet (W : Fin 4 → Fin 6 → ℝ) (a : Fin 4 → ℝ) :
    Network 4 6 4 where
  W₁ := maxFourNet.W₁
  b₁ := 0
  W₂ := W
  b₂ := 0
  w₃ := a
  b₃ := 0

theorem pairedNet_eval (W : Fin 4 → Fin 6 → ℝ) (a : Fin 4 → ℝ) (x : Point 4) :
    (pairedNet W a).eval x = ∑ k, a k * relu (form (W k) x) := by
  simp [Network.eval, pairedNet, form, feature]

/-- The spare fourth second-layer neuron bridges signed and split reconstruction. -/
noncomputable def signedSplitNet (t : ℝ) : Network 4 6 4 :=
  pairedNet
    ![rightRow + t • negativeAnchorRow, -(rightRow + t • negativeAnchorRow),
      leftRow - rightRow, negativeAnchorRow]
    ![1, -1, 1, -t]

/-- Every real parameter, in particular the entire unit interval, is exact. -/
theorem signedSplitNet_eval (t : ℝ) (x : Point 4) :
    (signedSplitNet t).eval x = Maximum 4 x := by
  rw [signedSplitNet, pairedNet_eval]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, one_mul, neg_one_mul,
    add_zero, form_add, form_smul, form_neg, form_sub,
    form_leftRow, form_rightRow, form_negativeAnchorRow]
  rw [relu_relu, Maximum_four]
  have hs := relu_sub_relu_neg (max (x 2) (x 3) + t * relu (-x 3))
  have hm := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at hm
  linarith only [hs, hm]

/-- Interpolate the two possible baseline pair maxima with two comparison slots. -/
noncomputable def outerFlipNet (t : ℝ) : Network 4 6 4 :=
  pairedNet
    ![(1-t) • rightRow + t • leftRow, -((1-t) • rightRow + t • leftRow),
      leftRow - rightRow, rightRow - leftRow]
    ![1, -1, 1-t, t]

theorem outerFlipNet_eval (t : ℝ) (x : Point 4) :
    (outerFlipNet t).eval x = Maximum 4 x := by
  rw [outerFlipNet, pairedNet_eval]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, one_mul, neg_one_mul,
    add_zero, form_add, form_smul, form_neg, form_sub, form_leftRow, form_rightRow]
  rw [Maximum_four]
  have hs := relu_sub_relu_neg ((1-t) * max (x 2) (x 3) + t * max (x 0) (x 1))
  have hA := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  have hB := relu_sub_add (max (x 0) (x 1)) (max (x 2) (x 3))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at hA
  have hA' : relu (max (x 0) (x 1) - max (x 2) (x 3)) =
      max (max (x 0) (x 1)) (max (x 2) (x 3)) - max (x 2) (x 3) := by
    linarith only [hA]
  have hB' : relu (max (x 2) (x 3) - max (x 0) (x 1)) =
      max (max (x 0) (x 1)) (max (x 2) (x 3)) - max (x 0) (x 1) := by
    linarith only [hB]
  rw [hA', hB']
  nlinarith only [hs]

/-- The last stage of the bridge deletes the dormant negative reconstruction
gate, ending at a padded three-neuron split implementation. -/
noncomputable def splitPruneNet (t : ℝ) : Network 4 6 4 :=
  pairedNet
    ![rightRow + negativeAnchorRow, -(rightRow + negativeAnchorRow),
      leftRow - rightRow, negativeAnchorRow]
    ![1, t-1, 1, -1]

theorem rightPlusNegative_nonneg (x : Point 4) :
    0 ≤ form (rightRow + negativeAnchorRow) x := by
  rw [form_add, form_rightRow, form_negativeAnchorRow]
  have h := relu_sub_relu_neg (x 3)
  have hb := le_max_right (x 2) (x 3)
  have hn := relu_nonneg (x 3)
  linarith

theorem splitPruneNet_eval (t : ℝ) (x : Point 4) :
    (splitPruneNet t).eval x = Maximum 4 x := by
  rw [splitPruneNet, pairedNet_eval]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, one_mul, neg_one_mul,
    add_zero]
  rw [form_neg, relu_of_nonpos (neg_nonpos.mpr (rightPlusNegative_nonneg x)), mul_zero,
    relu_of_nonneg (rightPlusNegative_nonneg x)]
  rw [form_add, form_sub, form_leftRow, form_rightRow, form_negativeAnchorRow,
    relu_relu, Maximum_four]
  have hm := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at hm
  linarith only [hm]

theorem splitPruneNet_start : splitPruneNet 0 = signedSplitNet 1 := by
  simp [splitPruneNet, signedSplitNet]

/-- The endpoint has an actual zero output coefficient, so its second slot can
be removed without altering any other parameter. -/
theorem splitPruneNet_end_unused : (splitPruneNet 1).w₃ 1 = 0 := by
  norm_num [splitPruneNet, pairedNet]

theorem continuous_signedSplitNet : Continuous signedSplitNet := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, continuous_const, ?_, continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> fin_cases j <;>
      simp [signedSplitNet, pairedNet, leftRow, rightRow, negativeAnchorRow] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp [signedSplitNet, pairedNet] <;> continuity

theorem continuous_outerFlipNet : Continuous outerFlipNet := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, ?_, continuous_const, ?_, continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> fin_cases j <;>
      simp [outerFlipNet, pairedNet, leftRow, rightRow] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp [outerFlipNet, pairedNet] <;> continuity

theorem continuous_splitPruneNet : Continuous splitPruneNet := by
  apply (continuous_network_iff _).2
  refine ⟨continuous_const, continuous_const, continuous_const, continuous_const,
    ?_, continuous_const⟩
  apply continuous_pi
  intro k
  fin_cases k <;> simp [splitPruneNet, pairedNet] <;> continuity

/-- Exact fiber points along the signed-to-split bridge. -/
noncomputable def signedSplitPoint (t : ℝ) : ExactFiber 4 6 4 :=
  ⟨signedSplitNet t, signedSplitNet_eval t⟩

/-- Exact fiber points along the change of the outer comparison. -/
noncomputable def outerFlipPoint (t : ℝ) : ExactFiber 4 6 4 :=
  ⟨outerFlipNet t, outerFlipNet_eval t⟩

noncomputable def splitPrunePoint (t : ℝ) : ExactFiber 4 6 4 :=
  ⟨splitPruneNet t, splitPruneNet_eval t⟩

theorem continuous_signedSplitPoint : Continuous signedSplitPoint :=
  continuous_signedSplitNet.subtype_mk _

theorem continuous_outerFlipPoint : Continuous outerFlipPoint :=
  continuous_outerFlipNet.subtype_mk _

theorem continuous_splitPrunePoint : Continuous splitPrunePoint :=
  continuous_splitPruneNet.subtype_mk _

/-- A continuous zero-loss path between actual parameter vectors. -/
noncomputable def signedSplitPath : Path (signedSplitPoint 0) (signedSplitPoint 1) where
  toFun t := signedSplitPoint t
  continuous_toFun := continuous_signedSplitPoint.comp continuous_subtype_val
  source' := rfl
  target' := rfl

/-- A continuous zero-loss path reversing the outer comparison. -/
noncomputable def outerFlipPath : Path (outerFlipPoint 0) (outerFlipPoint 1) where
  toFun t := outerFlipPoint t
  continuous_toFun := continuous_outerFlipPoint.comp continuous_subtype_val
  source' := rfl
  target' := rfl

noncomputable def splitPrunePath : Path (splitPrunePoint 0) (splitPrunePoint 1) where
  toFun t := splitPrunePoint t
  continuous_toFun := continuous_splitPrunePoint.comp continuous_subtype_val
  source' := rfl
  target' := rfl

theorem signed_split_joined : Joined (signedSplitPoint 0) (signedSplitPoint 1) :=
  ⟨signedSplitPath⟩

theorem outer_flip_joined : Joined (outerFlipPoint 0) (outerFlipPoint 1) :=
  ⟨outerFlipPath⟩

theorem splitPrunePoint_start : splitPrunePoint 0 = signedSplitPoint 1 := by
  apply Subtype.ext
  exact splitPruneNet_start

/-- The complete signed-to-split move includes deletion of the dormant gate. -/
noncomputable def signedToPaddedSplitPath :
    Path (signedSplitPoint 0) (splitPrunePoint 1) :=
  signedSplitPath.trans (splitPrunePath.cast splitPrunePoint_start.symm rfl)

theorem signedToPaddedSplitPath_end_unused : (splitPrunePoint 1).val.w₃ 1 = 0 :=
  splitPruneNet_end_unused

theorem installOtherComparison_eq :
    replaceSecond (signedSplitNet 0) 3 (rightRow-leftRow) 0 = outerFlipNet 0 := by
  change replaceSecond (signedSplitNet 0) (Fin.last 3) (rightRow-leftRow) 0 = outerFlipNet 0
  simp only [replaceSecond, signedSplitNet, outerFlipNet, pairedNet,
    zero_smul, one_smul, sub_zero, add_zero, zero_mul, one_mul, neg_zero]
  congr 1
  · funext k
    fin_cases k <;> norm_num [Function.update_apply, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.last]
  · simp [Function.update_eq_self]

theorem signedSplitPoint_zero_unused : (signedSplitPoint 0).val.w₃ 3 = 0 := by
  change -(0 : ℝ) = 0
  exact neg_zero

theorem installOtherComparisonPoint_eq :
    unusedSecondPoint (signedSplitPoint 0) 3 signedSplitPoint_zero_unused
      (rightRow-leftRow) 0 1 = outerFlipPoint 0 := by
  apply Subtype.ext
  change unusedSecondMove (signedSplitNet 0) 3 (rightRow-leftRow) 0 1 = outerFlipNet 0
  rw [unusedSecondMove_one, installOtherComparison_eq]

/-- Install the reversed comparison while the spare neuron's output weight is
zero. This joins the starting points of the two explicit bridge families. -/
noncomputable def installOtherComparisonPath :
    Path (signedSplitPoint 0) (outerFlipPoint 0) :=
  (unusedSecondPath (signedSplitPoint 0) 3 signedSplitPoint_zero_unused
    (rightRow-leftRow) 0).cast rfl installOtherComparisonPoint_eq.symm

/-- One known signed implementation is connected to the implementation based
on the opposite outer comparison. -/
noncomputable def signedToOppositeOuterPath :
    Path (signedSplitPoint 0) (outerFlipPoint 1) :=
  installOtherComparisonPath.trans outerFlipPath

end Connected64
end Fiber
end MaxCaterpillar
