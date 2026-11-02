import MaxCaterpillar.Fiber.Count65.Paired.MixedBaseline
import MaxCaterpillar.Fiber.Count65.Paired.SwitchingCompensated
import MaxCaterpillar.Fiber.Count65.Paired.ComparisonResidual

/-! # Actual baseline extraction from exceptional three-comparison profiles -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
open BigOperators Frontier Absorption

def ExceptionalFlags (b₁ b₂ b₃ : Bool) : Prop :=
  (b₁=true ∧ b₂=true ∧ b₃=false) ∨ (b₁=false ∧ b₂=false ∧ b₃=true)

def profileNet (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool) : Network 4 6 5 :=
  switchingWithSpectators (pairedRows U) 0 (comparisonRow U) F G 0 0 0 0
    b₁ b₂ b₃ rows 0 weights 0

def residualRow (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) : Fin 6 → ℝ := fun j =>
  baselineRow U j+(orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*comparisonRow U j-
    (orientationIndicator b₁-orientationIndicator b₃)*F j-
    (orientationIndicator b₂-orientationIndicator b₃)*G j

lemma preact_endpointForm (U : Fin 2 → Fin 2 → ℝ) (L : Fin 6 → ℝ) (x : Point 4) :
    preact (pairedRows U) 0 L 0 x=endpointForm U L x := by
  simp only [preact,endpointForm,endpointFeature,Pi.zero_apply,add_zero]

lemma maximum_decomposition (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0) (x : Point 4) :
    preact (pairedRows U) 0 (baselineRow U) 0 x+
      relu (preact (pairedRows U) 0 (comparisonRow U) 0 x)=Maximum 4 x := by
  rw [preact_endpointForm,preact_endpointForm]
  rw [← pairedMinimalNet_eval_formula,pairedMinimalNet_eval U hU]

lemma residualRow_preact (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) (x : Point 4) :
    preact (pairedRows U) 0 (residualRow U F G b₁ b₂ b₃) 0 x=
      preact (pairedRows U) 0 (baselineRow U) 0 x+
        (orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*
          preact (pairedRows U) 0 (comparisonRow U) 0 x-
        (orientationIndicator b₁-orientationIndicator b₃)*preact (pairedRows U) 0 F 0 x-
        (orientationIndicator b₂-orientationIndicator b₃)*preact (pairedRows U) 0 G 0 x := by
  simp only [preact,residualRow,add_mul,sub_mul,mul_assoc,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,← Finset.mul_sum,Pi.zero_apply,add_zero]

lemma profileNet_eval (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (b₁ b₂ b₃ : Bool)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (x : Point 4) :
    (profileNet U F G rows weights b₁ b₂ b₃).eval x=
      relu (preact (pairedRows U) 0 (comparisonRow U) 0 x)-
        (orientationIndicator b₁+orientationIndicator b₂-orientationIndicator b₃)*
          preact (pairedRows U) 0 (comparisonRow U) 0 x+
        (orientationIndicator b₁-orientationIndicator b₃)*preact (pairedRows U) 0 F 0 x+
        (orientationIndicator b₂-orientationIndicator b₃)*preact (pairedRows U) 0 G 0 x+
        ∑ k, weights k*relu (preact (pairedRows U) 0 (rows k) 0 x) := by
  rw [profileNet,switchingWithSpectators,appendSpectators_eval,
    switchingTripleNet_eval (pairedRows U) 0 (comparisonRow U) F G 0 0 0 0 b₁ b₂ b₃ hFG 0 x]
  simp only [sub_zero,one_mul,add_zero]
  rfl

/-- The two actual physical heads represent the explicit residual. No
baseline classification or coefficient path is assumed. -/
theorem profile_baseline_identity (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (F G : Fin 6 → ℝ) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ)
    (b₁ b₂ b₃ : Bool)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G rows weights b₁ b₂ b₃).eval x=Maximum 4 x) (x : Point 4) :
    (∑ k, weights k*relu (preact (pairedRows U) 0 (rows k) 0 x))=
      preact (pairedRows U) 0 (residualRow U F G b₁ b₂ b₃) 0 x := by
  have hh := hnet x
  rw [profileNet_eval U F G rows weights b₁ b₂ b₃ hFG x] at hh
  have hm := maximum_decomposition U hU x
  rw [residualRow_preact]
  linarith only [hh,hm]

theorem residual_increment_signs (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₁ b₂ b₃ : Bool) (hex : ExceptionalFlags b₁ b₂ b₃)
    (hF0 : F 0=0) (hF1 : F 1=0) (hG0 : G 0=0) (hG1 : G 1=0) :
    (0<residualRow U F G b₁ b₂ b₃ 0 ∧ residualRow U F G b₁ b₂ b₃ 1<0) ∨
    (residualRow U F G b₁ b₂ b₃ 0<0 ∧ 0<residualRow U F G b₁ b₂ b₃ 1) := by
  rcases hex with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
    norm_num [residualRow,orientationIndicator,baselineRow,comparisonRow,hF0,hF1,hG0,hG1]

lemma preact_q_unit (U : Fin 2 → Fin 2 → ℝ) (L : Fin 6 → ℝ) :
    preact (pairedRows U) 0 L 0 ![1,0,0,0]=L 0 := by
  have hh := paired_preact_increment_probe U L 0 0 1 0 (by norm_num) le_rfl
  simpa [codeIntercept,relu] using hh

lemma preact_r_unit (U : Fin 2 → Fin 2 → ℝ) (L : Fin 6 → ℝ) :
    preact (pairedRows U) 0 L 0 ![0,0,1,0]=L 1 := by
  have hh := paired_preact_increment_probe U L 0 0 0 1 le_rfl (by norm_num)
  simpa [codeIntercept,relu] using hh

theorem residual_takes_both_signs (U : Fin 2 → Fin 2 → ℝ) (L : Fin 6 → ℝ)
    (hop : (0<L 0 ∧ L 1<0) ∨ (L 0<0 ∧ 0<L 1)) :
    (∃ x, 0<preact (pairedRows U) 0 L 0 x) ∧ (∃ x, preact (pairedRows U) 0 L 0 x<0) := by
  rcases hop with ⟨h0,h1⟩|⟨h0,h1⟩
  · exact ⟨⟨![1,0,0,0],by rw [preact_q_unit]; exact h0⟩,
      ⟨![0,0,1,0],by rw [preact_r_unit]; exact h1⟩⟩
  · exact ⟨⟨![0,0,1,0],by rw [preact_r_unit]; exact h1⟩,
      ⟨![1,0,0,0],by rw [preact_q_unit]; exact h0⟩⟩

end MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
