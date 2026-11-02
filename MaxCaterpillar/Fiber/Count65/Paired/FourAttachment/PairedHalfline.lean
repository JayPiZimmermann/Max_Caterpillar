import MaxCaterpillar.Fiber.Count65.Paired.FourAttachment.HalflinePath
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork

/-! # Half-line attachment with the actual invertible paired first matrix -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
open BigOperators Frontier Absorption
variable {k : ℕ}

noncomputable def positiveCodeRow : Fin 6 → ℝ := ![0,0,1,0,0,0]
noncomputable def negativeCodeRow : Fin 6 → ℝ := ![0,0,0,1,0,0]

lemma paired_preact_eq_endpointForm (U : Fin 2 → Fin 2 → ℝ)
    (V : Fin 6 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 V 0 x=endpointForm U V x := by
  simp only [preact,endpointForm,endpointFeature,Pi.zero_apply,add_zero]

lemma positiveCodeRow_preact (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 positiveCodeRow 0 x=relu (anchorCodeValue U x 0) := by
  rw [paired_preact_eq_endpointForm,endpointForm,endpointFeature_eq]
  norm_num [positiveCodeRow,Fin.sum_univ_succ]

lemma negativeCodeRow_preact (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 negativeCodeRow 0 x=relu (-anchorCodeValue U x 0) := by
  rw [paired_preact_eq_endpointForm,endpointForm,endpointFeature_eq]
  norm_num [negativeCodeRow,Fin.sum_univ_succ]

lemma paired_max_decomposition (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (x : Point 4) :
    preact (pairedRows U) 0 (baselineRow U) 0 x+
      relu (preact (pairedRows U) 0 (comparisonRow U) 0 x)=Maximum 4 x := by
  rw [paired_preact_eq_endpointForm,paired_preact_eq_endpointForm]
  exact (pairedMinimalNet_eval_formula U x).symm.trans (pairedMinimalNet_eval U hU x)

lemma paired_anchor_increment_probe (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (u v q r : ℝ) (hq : 0≤q) (hr : 0≤r) :
    ∃ x : Point 4,anchorCodeValue U x 0=u ∧ anchorCodeValue U x 1=v ∧
      relu (x 0-x 1)=q ∧ relu (x 2-x 3)=r := by
  let a := inverseCode U 0 0*u+inverseCode U 0 1*v
  let b := inverseCode U 1 0*u+inverseCode U 1 1*v
  have hcode := code_rightInverse_eval U (inverseCode U) (inverseCode_rightInverse U hU) u v
  refine ⟨![a+q,a,b+r,b],?_,?_,?_,?_⟩
  · exact hcode.1
  · exact hcode.2
  · change relu (a+q-a)=q
    rw [show a+q-a=q by ring,relu_of_nonneg hq]
  · change relu (b+r-b)=r
    rw [show b+r-b=r by ring,relu_of_nonneg hr]

lemma paired_carrier_linear_part (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    preact (pairedRows U) 0 (baselineRow U) 0 x+
      s*preact (pairedRows U) 0 (comparisonRow U) 0 x=
    s*relu (x 0-x 1)+(1-s)*relu (x 2-x 3)+
      (s*inverseCode U 0 0+(1-s)*inverseCode U 1 0)*anchorCodeValue U x 0+
      (s*inverseCode U 0 1+(1-s)*inverseCode U 1 1)*anchorCodeValue U x 1 := by
  rw [paired_preact_eq_endpointForm,paired_preact_eq_endpointForm,
    baselineRow_form U hU,comparisonRow_form U hU]
  have ha := (inverseCode_anchor_eval U hU (x 1) (x 3)).1
  have hb := (inverseCode_anchor_eval U hU (x 1) (x 3)).2
  have hA := relu_sub_add (x 1) (x 0)
  have hB := relu_sub_add (x 3) (x 2)
  rw [max_comm (x 1) (x 0)] at hA
  rw [max_comm (x 3) (x 2)] at hB
  change inverseCode U 0 0*anchorCodeValue U x 0+
    inverseCode U 0 1*anchorCodeValue U x 1=x 1 at ha
  change inverseCode U 1 0*anchorCodeValue U x 0+
    inverseCode U 1 1*anchorCodeValue U x 1=x 3 at hb
  linear_combination -s*ha-(1-s)*hb-s*hA-(1-s)*hB

/-- With the actual paired first matrix and an ordinary invertible code, any
nonnegative-carrier two-half-line completion joins a globally common-support
completion. Both endpoint networks are ordinary `(4,6,k+1)` networks. -/
theorem paired_halflineCompletion_contract (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (S T : Finset (Fin k)) (c e : ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hS : (∑ i in S,j i)=0) (hT : (∑ i in T,j i)=0) (hj : (∑ i,j i)=1)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow j flip (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveCodeRow negativeCodeRow S T c e)) 0 x) :
    JoinedIn (ExactSet 4 6 (k+1))
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveCodeRow negativeCodeRow S T c e) j flip)
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveCodeRow negativeCodeRow S T 0 e) j flip) ∨
    JoinedIn (ExactSet 4 6 (k+1))
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveCodeRow negativeCodeRow S T c e) j flip)
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveCodeRow negativeCodeRow S T c 0) j flip) := by
  let s := ∑ i,orientationWeight j flip i
  have hp := halflineCompletion_contract (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    positiveCodeRow negativeCodeRow S T c e
    (s*inverseCode U 0 0+(1-s)*inverseCode U 1 0)
    (s*inverseCode U 0 1+(1-s)*inverseCode U 1 1) j flip hS hT hj
    (fun x => anchorCodeValue U x 0) (fun x => anchorCodeValue U x 1)
    (fun x => relu (x 0-x 1)) (fun x => relu (x 2-x 3))
    (fun _ => relu_nonneg _) (fun _ => relu_nonneg _)
    (positiveCodeRow_preact U) (negativeCodeRow_preact U)
    (paired_carrier_linear_part U hU s) (paired_anchor_increment_probe U hU) hg
    (paired_max_decomposition U hU)
  exact hp.imp And.right And.right

noncomputable def positiveRightCodeRow : Fin 6 → ℝ := ![0,0,0,0,1,0]
noncomputable def negativeRightCodeRow : Fin 6 → ℝ := ![0,0,0,0,0,1]

lemma positiveRightCodeRow_preact (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 positiveRightCodeRow 0 x=relu (anchorCodeValue U x 1) := by
  rw [paired_preact_eq_endpointForm,endpointForm,endpointFeature_eq]
  norm_num [positiveRightCodeRow,Fin.sum_univ_succ]

lemma negativeRightCodeRow_preact (U : Fin 2 → Fin 2 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 negativeRightCodeRow 0 x=relu (-anchorCodeValue U x 1) := by
  rw [paired_preact_eq_endpointForm,endpointForm,endpointFeature_eq]
  norm_num [negativeRightCodeRow,Fin.sum_univ_succ]

/-- The second code coordinate contracts in the same fixed physical first
matrix; no internal code change is treated as a parameter path. -/
theorem paired_right_halflineCompletion_contract (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (S T : Finset (Fin k)) (c e : ℝ) (j : Fin k → ℝ) (flip : Fin k → Bool)
    (hS : (∑ i in S,j i)=0) (hT : (∑ i in T,j i)=0) (hj : (∑ i,j i)=1)
    (hg : ∀ x,0≤preact (pairedRows U) 0
      (carrierRow j flip (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c e)) 0 x) :
    JoinedIn (ExactSet 4 6 (k+1))
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c e) j flip)
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T 0 e) j flip) ∨
    JoinedIn (ExactSet 4 6 (k+1))
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c e) j flip)
      (orientedCompletionNet (pairedRows U) 0 (baselineRow U) (comparisonRow U)
        (halflineOffsets positiveRightCodeRow negativeRightCodeRow S T c 0) j flip) := by
  let s := ∑ i,orientationWeight j flip i
  have hlinear (x : Point 4) :
      preact (pairedRows U) 0 (baselineRow U) 0 x+
        s*preact (pairedRows U) 0 (comparisonRow U) 0 x=
      s*relu (x 0-x 1)+(1-s)*relu (x 2-x 3)+
        (s*inverseCode U 0 1+(1-s)*inverseCode U 1 1)*anchorCodeValue U x 1+
        (s*inverseCode U 0 0+(1-s)*inverseCode U 1 0)*anchorCodeValue U x 0 := by
    linear_combination paired_carrier_linear_part U hU s x
  have hprobe : ∀ u v q r : ℝ,0≤q → 0≤r → ∃ x : Point 4,
      anchorCodeValue U x 1=u ∧ anchorCodeValue U x 0=v ∧
        relu (x 0-x 1)=q ∧ relu (x 2-x 3)=r := by
    intro u v q r hq hr
    obtain ⟨x,hv,hu,hq,hr⟩ := paired_anchor_increment_probe U hU v u q r hq hr
    exact ⟨x,hu,hv,hq,hr⟩
  have hp := halflineCompletion_contract (pairedRows U) 0 (baselineRow U) (comparisonRow U)
    positiveRightCodeRow negativeRightCodeRow S T c e
    (s*inverseCode U 0 1+(1-s)*inverseCode U 1 1)
    (s*inverseCode U 0 0+(1-s)*inverseCode U 1 0) j flip hS hT hj
    (fun x => anchorCodeValue U x 1) (fun x => anchorCodeValue U x 0)
    (fun x => relu (x 0-x 1)) (fun x => relu (x 2-x 3))
    (fun _ => relu_nonneg _) (fun _ => relu_nonneg _)
    (positiveRightCodeRow_preact U) (negativeRightCodeRow_preact U)
    hlinear hprobe hg (paired_max_decomposition U hU)
  exact hp.imp And.right And.right

end MaxCaterpillar.Fiber.Count65.Paired.FourAttachment
