import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointContinuity
import MaxCaterpillar.Fiber.Symmetry

/-! # Actual paths remove baseline scaling and dormant slots at paired endpoints -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

noncomputable def scaledEndpointNet (U : Fin 2 → Fin 2 → ℝ) (d K : ℝ)
    (Z : Fin 6 → ℝ) : Network 4 6 5 where
  W₁ := pairedRows U
  b₁ := 0
  W₂ := ![0,K⁻¹ • baselineRow U,-(K⁻¹ • baselineRow U),comparisonRow U,Z]
  b₂ := 0
  w₃ := ![d,K,-K,1,0]
  b₃ := 0

lemma endpointForm_smul (U : Fin 2 → Fin 2 → ℝ) (a : ℝ) (v : Fin 6 → ℝ) (x : Point 4) :
    endpointForm U (a • v) x=a*endpointForm U v x := by
  simp [endpointForm,Finset.mul_sum,mul_assoc]

lemma scaledEndpointNet_eval_formula (U : Fin 2 → Fin 2 → ℝ) (d K : ℝ)
    (hK : K≠0) (Z : Fin 6 → ℝ) (x : Point 4) :
    (scaledEndpointNet U d K Z).eval x=endpointForm U (baselineRow U) x+
      relu (endpointForm U (comparisonRow U) x) := by
  simp only [Network.eval,scaledEndpointNet,Pi.zero_apply,add_zero]
  change (∑ k : Fin 5,(![d,K,-K,1,0] : Fin 5 → ℝ) k*
    relu (endpointForm U ((![0,K⁻¹ • baselineRow U,-(K⁻¹ • baselineRow U),comparisonRow U,Z] :
      Fin 5 → Fin 6 → ℝ) k) x))= _
  have hz : relu (0 : ℝ)=0 := by simp [relu]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,one_mul,neg_mul,
    zero_mul,mul_zero,add_zero,zero_add,endpointForm_neg,endpointForm_zero,
    endpointForm_smul,hz]
  have hB : K*(K⁻¹*endpointForm U (baselineRow U) x)=endpointForm U (baselineRow U) x := by
    rw [← mul_assoc,mul_inv_cancel hK,one_mul]
  linear_combination K*relu_sub_relu_neg (K⁻¹*endpointForm U (baselineRow U) x)+hB

lemma scaledEndpointNet_exact (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) :
    ∀ x,(scaledEndpointNet U d K Z).eval x=Maximum 4 x := by
  intro x
  rw [scaledEndpointNet_eval_formula U d K hK Z,baselineRow_form U hU,
    comparisonRow_form U hU,Maximum_four]
  have he := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3))] at he
  linarith only [he]

lemma continuous_scaledEndpointNet_of {X : Type*} [TopologicalSpace X]
    (U : Fin 2 → Fin 2 → ℝ) (d K : X → ℝ) (Z : X → Fin 6 → ℝ)
    (hd : Continuous d) (hK : Continuous K) (hZ : Continuous Z)
    (hne : ∀ x,K x≠0) : Continuous (fun x => scaledEndpointNet U (d x) (K x) (Z x)) := by
  have hi := hK.inv₀ hne
  have hB : Continuous (fun x => (K x)⁻¹ • baselineRow U) := by
    apply continuous_pi
    intro j
    exact hi.mul continuous_const
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,continuous_const,?_,continuous_const⟩
  · apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact hB
    · exact hB.neg
    · exact continuous_const
    · exact hZ
  · apply continuous_pi
    intro i
    fin_cases i
    · exact hd
    · exact hK
    · exact hK.neg
    · exact continuous_const
    · exact continuous_const

noncomputable def scaledEndpointPoint (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (d K : ℝ) (hK : K≠0) (Z : Fin 6 → ℝ) : ExactFiber 4 6 5 :=
  ⟨scaledEndpointNet U d K Z,scaledEndpointNet_exact U hU d K hK Z⟩

lemma positive_endpoint_coefficient (K : ℝ) (hK : 0<K) (t : unitInterval) :
    0 < (1-(t : ℝ))*K+(t : ℝ) := by
  by_cases he : (t : ℝ)=1
  · rw [he]
    norm_num
  · have hp : 0<1-(t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 he)
    exact add_pos_of_pos_of_nonneg (mul_pos hp hK) t.property.1

/-- A concrete exact-network path normalizes a positive baseline coefficient,
removes the silent output, and clears an arbitrary dormant row. -/
noncomputable def scaledEndpointPositivePath (U : Fin 2 → Fin 2 → ℝ)
    (hU : codeDet U≠0) (d K : ℝ) (hK : 0<K) (Z : Fin 6 → ℝ) :
    Path (scaledEndpointPoint U hU d K hK.ne' Z)
      (scaledEndpointPoint U hU 0 1 (by norm_num) 0) where
  toFun t := scaledEndpointPoint U hU ((1-(t : ℝ))*d) ((1-(t : ℝ))*K+(t : ℝ))
    (positive_endpoint_coefficient K hK t).ne' ((1-(t : ℝ)) • Z)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_scaledEndpointNet_of
    · continuity
    · continuity
    · apply continuous_pi
      intro j
      change Continuous (fun t : unitInterval => (1-(t : ℝ))*Z j)
      continuity
    · exact fun t => (positive_endpoint_coefficient K hK t).ne'
  source' := by
    apply Subtype.ext
    simp [scaledEndpointPoint]
  target' := by
    apply Subtype.ext
    simp [scaledEndpointPoint]

#print axioms scaledEndpointNet_exact
#print axioms scaledEndpointPositivePath
end MaxCaterpillar.Fiber.Count65.Paired
