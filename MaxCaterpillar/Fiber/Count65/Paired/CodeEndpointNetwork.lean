import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets
import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Connected64

/-! # Actual padded signed endpoints for arbitrary invertible anchor codes -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier

noncomputable def leftEndpointRow (U : Fin 2 → Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![1,0,inverseCode U 0 0,-inverseCode U 0 0,inverseCode U 0 1,-inverseCode U 0 1]
noncomputable def baselineRow (U : Fin 2 → Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![0,1,inverseCode U 1 0,-inverseCode U 1 0,inverseCode U 1 1,-inverseCode U 1 1]
noncomputable def comparisonRow (U : Fin 2 → Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![1,-1,inverseCode U 0 0-inverseCode U 1 0,-(inverseCode U 0 0-inverseCode U 1 0),
    inverseCode U 0 1-inverseCode U 1 1,-(inverseCode U 0 1-inverseCode U 1 1)]

noncomputable def pairedMinimalNet (U : Fin 2 → Fin 2 → ℝ) : Network 4 6 5 where
  W₁ := pairedRows U
  b₁ := 0
  W₂ := ![baselineRow U,-baselineRow U,comparisonRow U,0,0]
  b₂ := 0
  w₃ := ![1,-1,1,0,0]
  b₃ := 0

lemma pairedMinimalNet_zeroBias (U : Fin 2 → Fin 2 → ℝ) :
    (pairedMinimalNet U).HasZeroBiases := ⟨rfl,rfl,rfl⟩

noncomputable def endpointFeature (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) (j : Fin 6) : ℝ :=
  relu (∑ i,pairedRows U j i*x i)
noncomputable def anchorCodeValue (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) (i : Fin 2) : ℝ :=
  U i 0*x 1+U i 1*x 3
noncomputable def endpointForm (U : Fin 2 → Fin 2 → ℝ) (v : Fin 6 → ℝ) (x : Point 4) : ℝ :=
  ∑ j,v j*endpointFeature U x j

lemma endpointFeature_eq (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    endpointFeature U x=![relu (x 0-x 1),relu (x 2-x 3),
      relu (anchorCodeValue U x 0),relu (-anchorCodeValue U x 0),
      relu (anchorCodeValue U x 1),relu (-anchorCodeValue U x 1)] := by
  funext j
  fin_cases j <;> simp [endpointFeature,pairedRows,anchorCodeValue,Fin.sum_univ_succ] <;>
    congr 1 <;> ring
  all_goals rfl

lemma inverseCode_anchor_eval (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (a b : ℝ) :
    inverseCode U 0 0*(U 0 0*a+U 0 1*b)+inverseCode U 0 1*(U 1 0*a+U 1 1*b)=a ∧
    inverseCode U 1 0*(U 0 0*a+U 0 1*b)+inverseCode U 1 1*(U 1 0*a+U 1 1*b)=b := by
  constructor
  · change (U 1 1/codeDet U)*(U 0 0*a+U 0 1*b)+
      (-U 0 1/codeDet U)*(U 1 0*a+U 1 1*b)=a
    field_simp [hU]
    unfold codeDet
    ring
  · change (-U 1 0/codeDet U)*(U 0 0*a+U 0 1*b)+
      (U 0 0/codeDet U)*(U 1 0*a+U 1 1*b)=b
    field_simp [hU]
    unfold codeDet
    ring

lemma endpointForm_neg (U : Fin 2 → Fin 2 → ℝ) (v : Fin 6 → ℝ) (x : Point 4) :
    endpointForm U (-v) x= -endpointForm U v x := by
  simp [endpointForm,Finset.sum_neg_distrib]
lemma endpointForm_zero (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    endpointForm U 0 x=0 := by simp [endpointForm]

lemma leftEndpointRow_form (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (x : Point 4) :
    endpointForm U (leftEndpointRow U) x=max (x 0) (x 1) := by
  have hanchor := (inverseCode_anchor_eval U hU (x 1) (x 3)).1
  change inverseCode U 0 0*anchorCodeValue U x 0+
    inverseCode U 0 1*anchorCodeValue U x 1=x 1 at hanchor
  have hmax := relu_sub_add (x 1) (x 0)
  rw [max_comm] at hmax
  rw [endpointForm,endpointFeature_eq]
  norm_num [leftEndpointRow,Fin.sum_univ_succ]
  calc
    _ = relu (x 0-x 1)+inverseCode U 0 0*
      (relu (anchorCodeValue U x 0)-relu (-anchorCodeValue U x 0))+
      inverseCode U 0 1*(relu (anchorCodeValue U x 1)-relu (-anchorCodeValue U x 1)) := by ring
    _ = max (x 0) (x 1) := by
      rw [relu_sub_relu_neg,relu_sub_relu_neg]
      linarith only [hanchor,hmax]

lemma baselineRow_form (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (x : Point 4) :
    endpointForm U (baselineRow U) x=max (x 2) (x 3) := by
  have hanchor := (inverseCode_anchor_eval U hU (x 1) (x 3)).2
  change inverseCode U 1 0*anchorCodeValue U x 0+
    inverseCode U 1 1*anchorCodeValue U x 1=x 3 at hanchor
  have hmax := relu_sub_add (x 3) (x 2)
  rw [max_comm] at hmax
  rw [endpointForm,endpointFeature_eq]
  norm_num [baselineRow,Fin.sum_univ_succ]
  calc
    _ = relu (x 2-x 3)+inverseCode U 1 0*
      (relu (anchorCodeValue U x 0)-relu (-anchorCodeValue U x 0))+
      inverseCode U 1 1*(relu (anchorCodeValue U x 1)-relu (-anchorCodeValue U x 1)) := by ring
    _ = max (x 2) (x 3) := by
      rw [relu_sub_relu_neg,relu_sub_relu_neg]
      linarith only [hanchor,hmax]

lemma comparisonRow_eq_sub (U : Fin 2 → Fin 2 → ℝ) :
    comparisonRow U=leftEndpointRow U-baselineRow U := by
  funext j
  fin_cases j <;> norm_num [comparisonRow,leftEndpointRow,baselineRow] <;> ring
lemma comparisonRow_form (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (x : Point 4) :
    endpointForm U (comparisonRow U) x=max (x 0) (x 1)-max (x 2) (x 3) := by
  rw [comparisonRow_eq_sub]
  have he : endpointForm U (leftEndpointRow U-baselineRow U) x=
      endpointForm U (leftEndpointRow U) x-endpointForm U (baselineRow U) x := by
    simp [endpointForm,sub_mul,Finset.sum_sub_distrib]
  rw [he,leftEndpointRow_form U hU,baselineRow_form U hU]

lemma pairedMinimalNet_eval_formula (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    (pairedMinimalNet U).eval x=endpointForm U (baselineRow U) x+
      relu (endpointForm U (comparisonRow U) x) := by
  simp only [Network.eval,pairedMinimalNet,Pi.zero_apply,add_zero]
  change (∑ k : Fin 5,(![1,-1,1,0,0] : Fin 5 → ℝ) k*
    relu (endpointForm U ((![baselineRow U,-baselineRow U,comparisonRow U,0,0] :
      Fin 5 → Fin 6 → ℝ) k) x))= _
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,one_mul,neg_one_mul,
    zero_mul,add_zero,endpointForm_neg]
  linear_combination relu_sub_relu_neg (endpointForm U (baselineRow U) x)

/-- Genuine six-array networks compute MAX4 for every real input at every
invertible real anchor code. -/
theorem pairedMinimalNet_eval (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) :
    ∀ x,(pairedMinimalNet U).eval x=Maximum 4 x := by
  intro x
  rw [pairedMinimalNet_eval_formula,baselineRow_form U hU,comparisonRow_form U hU,Maximum_four]
  have he := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3))] at he
  linarith only [he]

#print axioms pairedMinimalNet_eval
end MaxCaterpillar.Fiber.Count65.Paired
