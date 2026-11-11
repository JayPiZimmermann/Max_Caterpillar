import MaxCaterpillar.Fiber.BinaryPatterns.Update

/-! # Strict binary-pattern changes in both layers of one exact-fiber component -/
set_option autoImplicit false
namespace MaxCaterpillar
open BigOperators
namespace Fiber.BinaryPatterns
open Frontier unitInterval

/-! ## A strict negative-to-positive witness, without a zero-endpoint convention -/

/-- The inactive-side slack varies while the code remains fixed at its start. -/
noncomputable def hybridMatrix (s : ℝ) : Fin 3 → Fin 6 → ℝ :=
  ![![0,1,0,0,1,0],![0,0,0,0,-s,1],![1,-1,1,-1,0,0]]

noncomputable def hybridNet (s : ℝ) : Network 4 6 3 :=
  Network.replaceSecondMatrix (net 0) (hybridMatrix s)

lemma firstHidden_hybrid (s : ℝ) (x : Point 4) :
    (hybridNet s).firstHidden x = (net 0).firstHidden x :=
by
  unfold hybridNet
  exact Network.firstHidden_replaceSecondMatrix (net 0) (hybridMatrix s) x

private lemma inactive_negative (s z : ℝ) (hs : 0 ≤ s) :
    relu (-s*relu z+relu (-z)) = relu (-z) := by
  rcases le_total 0 z with hz | hz
  · rw [relu_of_nonneg hz,relu_of_nonpos (neg_nonpos.mpr hz)]
    apply relu_of_nonpos
    nlinarith
  · rw [relu_of_nonpos hz,mul_zero,zero_add,relu_relu]

lemma secondHidden_hybrid (s : ℝ) (hs : 0 ≤ s) (x : Point 4) :
    (hybridNet s).secondHidden x = (net 0).secondHidden x := by
  conv_rhs => rw [secondHidden_net 0 (by norm_num)]
  unfold hybridNet
  rw [Network.secondHidden_replaceSecondMatrix]
  rw [firstHidden_net]
  funext k
  fin_cases k
  · norm_num [hybridNet,hybridMatrix,Network.replaceSecondMatrix,net,features,common,Fin.sum_univ_succ]
    exact relu_of_nonneg (add_nonneg (relu_nonneg (x 2-x 3)) (relu_nonneg (x 3)))
  · norm_num [hybridNet,hybridMatrix,Network.replaceSecondMatrix,net,features,common,Fin.sum_univ_succ]
    simpa only [neg_mul] using inactive_negative s (x 3) hs
  · change relu ((∑ j,hybridMatrix s 2 j*features 0 x j)+0) = _
    have hsum : (∑ j,hybridMatrix s 2 j*features 0 x j) =
        features 0 x 0-features 0 x 1+features 0 x 2-features 0 x 3 := by
      norm_num [hybridMatrix,Fin.sum_univ_succ]
      simp only [show Fin.succ (2 : Fin 5) = (3 : Fin 6) from rfl]
      ring
    rw [add_zero,hsum]
    change relu (relu (x 0-x 1)-relu (x 2-x 3)+relu (code 0 x)-relu (-code 0 x)) = _
    congr 1
    have hA := relu_sub_add (x 1) (x 0)
    have hB := relu_sub_add (x 3) (x 2)
    rw [max_comm] at hA hB
    have hu := relu_sub_relu_neg (code 0 x)
    unfold code at hu ⊢
    linear_combination hA-hB+hu

theorem hybridNet_eval (s : ℝ) (hs : 0 ≤ s) (x : Point 4) :
    (hybridNet s).eval x = Maximum 4 x := by
  exact (Network.eval_replaceSecondMatrix_of_secondHidden (net 0) (hybridMatrix s)
    x (secondHidden_hybrid s hs x)).trans (net_eval 0 (by norm_num) x)

lemma hybridNet_zero : hybridNet 0 = net 0 := by
  have hw : hybridMatrix 0 = (net 0).W₂ := by
    funext k j
    fin_cases k <;> fin_cases j <;> norm_num [hybridMatrix,net]
  unfold hybridNet
  rw [hw,Network.replaceSecondMatrix_self]

lemma hybrid_zeroBiases (s : ℝ) : (hybridNet s).HasZeroBiases :=
  (Network.zeroBiases_replaceSecondMatrix (net 0) (hybridMatrix s)).mpr (net_zeroBiases 0)

lemma hybrid_output_nonzero (s : ℝ) (k : Fin 3) : (hybridNet s).w₃ k ≠ 0 := by
  change (net 0).w₃ k ≠ 0
  exact output_weights_nonzero 0 k

theorem continuous_hybridNet : Continuous hybridNet := by
  unfold hybridNet
  apply (Network.continuous_replaceSecondMatrix (net 0)).comp
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  fin_cases k <;> fin_cases j <;> first
    | exact continuous_const
    | change Continuous (fun s : ℝ => -s)
      exact continuous_id.neg

noncomputable def hybridExact (s : ℝ) (hs : 0 ≤ s) : ExactFiber 4 6 3 :=
  ⟨hybridNet s,hybridNet_eval s hs⟩

/-- The inactive-side leg joins the strict negative gate to the common-offset leg. -/
noncomputable def hybridPath : Path (hybridExact 1 (by norm_num)) zeroExact where
  toFun t := hybridExact (1-(t : ℝ)) (by linarith [t.property.2])
  continuous_toFun :=
    (continuous_hybridNet.comp (continuous_const.sub continuous_subtype_val)).subtype_mk _
  source' := by
    apply Subtype.ext
    change hybridNet (1-(0 : ℝ)) = hybridNet 1
    norm_num
  target' := by
    apply Subtype.ext
    change hybridNet (1-(1 : ℝ)) = net 0
    simpa only [sub_self] using hybridNet_zero

/-- The two exact legs compose to a path with strict sign differences at its ends. -/
noncomputable def strictPath : Path (hybridExact 1 (by norm_num)) oneExact :=
  hybridPath.trans exactPath

theorem strictPath_zeroBiases (t : I) : (strictPath t).val.HasZeroBiases := by
  unfold strictPath
  rw [Path.trans_apply]
  split_ifs
  · exact hybrid_zeroBiases _
  · exact net_zeroBiases _

theorem strictPath_output_nonzero (t : I) (k : Fin 3) :
    (strictPath t).val.w₃ k ≠ 0 := by
  unfold strictPath
  rw [Path.trans_apply]
  split_ifs
  · exact hybrid_output_nonzero _ k
  · exact output_weights_nonzero _ k

/-- Here both changed preactivations are strictly negative initially. -/
def strictWitness : Point 4 := fun i => if i.val < 2 then 0 else 1

private lemma binary_succ_two_fin4 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl

private lemma strictWitness_zero : strictWitness 0 = 0 := rfl
private lemma strictWitness_one : strictWitness 1 = 0 := rfl
private lemma strictWitness_two : strictWitness 2 = 1 := rfl
private lemma strictWitness_three : strictWitness 3 = 1 := rfl

lemma firstPreactivation_start :
    (hybridNet 1).firstPreactivation strictWitness 2 = -1 := by
  norm_num [Network.firstPreactivation,hybridNet,hybridMatrix,Network.replaceSecondMatrix,net,strictWitness_zero,strictWitness_one,strictWitness_two,strictWitness_three,Fin.sum_univ_succ]
  norm_num [binary_succ_two_fin4,strictWitness_three]

lemma firstPreactivation_end : (net 1).firstPreactivation strictWitness 2 = 1 := by
  norm_num [Network.firstPreactivation,net,strictWitness_zero,strictWitness_one,strictWitness_two,strictWitness_three,Fin.sum_univ_succ]
  norm_num [binary_succ_two_fin4,strictWitness_three]

lemma secondPreactivation_start :
    (hybridNet 1).secondPreactivation strictWitness 1 = -1 := by
  unfold Network.secondPreactivation
  rw [firstHidden_hybrid,firstHidden_net]
  norm_num [hybridNet,hybridMatrix,Network.replaceSecondMatrix,net,features,code,strictWitness_zero,strictWitness_one,strictWitness_two,strictWitness_three,Fin.sum_univ_succ,relu]

lemma secondPreactivation_end : (net 1).secondPreactivation strictWitness 1 = 2 := by
  unfold Network.secondPreactivation
  rw [firstHidden_net]
  norm_num [net,features,code,strictWitness_zero,strictWitness_one,strictWitness_two,strictWitness_three,Fin.sum_univ_succ,relu]

private lemma bool_false_of_not_true (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => exact (h rfl).elim

/-- Both tracked gates go from strictly inactive to strictly active. -/
theorem strict_binary_gate_changes :
    (hybridNet 1).firstBinary strictWitness 2 = false ∧
    (net 1).firstBinary strictWitness 2 = true ∧
    (hybridNet 1).secondBinary strictWitness 1 = false ∧
    (net 1).secondBinary strictWitness 1 = true := by
  refine ⟨?_,?_,?_,?_⟩
  · apply bool_false_of_not_true
    intro h
    have hp := (Network.firstBinary_eq_true_iff (hybridNet 1) strictWitness 2).mp h
    change 0 < (hybridNet 1).firstPreactivation strictWitness 2 at hp
    rw [firstPreactivation_start] at hp
    norm_num at hp
  · apply (Network.firstBinary_eq_true_iff (net 1) strictWitness 2).mpr
    change 0 < (net 1).firstPreactivation strictWitness 2
    rw [firstPreactivation_end]
    norm_num
  · apply bool_false_of_not_true
    intro h
    have hp := (Network.secondBinary_eq_true_iff (hybridNet 1) strictWitness 1).mp h
    change 0 < (hybridNet 1).secondPreactivation strictWitness 1 at hp
    rw [secondPreactivation_start] at hp
    norm_num at hp
  · apply (Network.secondBinary_eq_true_iff (net 1) strictWitness 1).mpr
    change 0 < (net 1).secondPreactivation strictWitness 1
    rw [secondPreactivation_end]
    norm_num

lemma hybrid_first_count : (hybridNet 1).firstActiveCount diagonal = 1 :=
  (Network.firstActiveCount_replaceSecondMatrix (net 0) (hybridMatrix 1) diagonal).trans first_count_zero

lemma hybrid_second_count : (hybridNet 1).secondActiveCount diagonal = 1 :=
  (Network.secondActiveCount_of_secondHidden diagonal
    (secondHidden_hybrid 1 (by norm_num) diagonal)).trans second_count_zero

/-- Strict endpoint changes in both hidden layers, in one full exact-fiber path
component, with no zero output weight and no extra hidden width. -/
theorem strict_connected_binary_pattern_counterexample :
    ∃ a b : ExactFiber 4 6 3,
      Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
      (∀ k,a.val.w₃ k ≠ 0 ∧ b.val.w₃ k ≠ 0) ∧
      a.val.firstPreactivation strictWitness 2 = -1 ∧
      b.val.firstPreactivation strictWitness 2 = 1 ∧
      a.val.secondPreactivation strictWitness 1 = -1 ∧
      b.val.secondPreactivation strictWitness 1 = 2 ∧
      a.val.firstActiveCount diagonal = 1 ∧ b.val.firstActiveCount diagonal = 2 ∧
      a.val.secondActiveCount diagonal = 1 ∧ b.val.secondActiveCount diagonal = 2 := by
  exact ⟨hybridExact 1 (by norm_num),oneExact,⟨strictPath⟩,
    hybrid_zeroBiases 1,net_zeroBiases 1,
    fun k => ⟨hybrid_output_nonzero 1 k,output_weights_nonzero 1 k⟩,
    firstPreactivation_start,firstPreactivation_end,
    secondPreactivation_start,secondPreactivation_end,
    hybrid_first_count,first_count_one,hybrid_second_count,second_count_one⟩

end Fiber.BinaryPatterns
end MaxCaterpillar
