import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional.Core
import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional.OutputNormalization

/-! # Actual exceptional three-comparison profiles attach to a unit comparison

Both remaining baseline rows and their output coefficients are arbitrary.
All-input exactness supplies the mixed-increment baseline, forces opposite
nonzero output signs, and supplies its signed/split classification. Every
normalization and contraction is a path of actual physical parameters.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
open BigOperators Frontier Absorption

theorem exceptional_head_output_signs (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (F G : Fin 6 → ℝ) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ)
    (b₁ b₂ b₃ : Bool) (hex : ExceptionalFlags b₁ b₂ b₃)
    (hF0 : F 0=0) (hF1 : F 1=0) (hG0 : G 0=0) (hG1 : G 1=0)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G rows weights b₁ b₂ b₃).eval x=Maximum 4 x) :
    (0<weights 0 ∧ weights 1<0) ∨ (weights 0<0 ∧ 0<weights 1) := by
  let L := residualRow U F G b₁ b₂ b₃
  have hreadout : ∀ x, weights 0*relu (preact (pairedRows U) 0 (rows 0) 0 x)+
      weights 1*relu (preact (pairedRows U) 0 (rows 1) 0 x)=preact (pairedRows U) 0 L 0 x := by
    intro x
    simpa only [Fin.sum_univ_two] using
      profile_baseline_identity U hU F G rows weights b₁ b₂ b₃ hFG hnet x
  have hb := residual_takes_both_signs U L
    (residual_increment_signs U F G b₁ b₂ b₃ hex hF0 hF1 hG0 hG1)
  exact two_relu_readout_opposite_signs
    (fun x => preact (pairedRows U) 0 (rows 0) 0 x)
    (fun x => preact (pairedRows U) 0 (rows 1) 0 x)
    (fun x => preact (pairedRows U) 0 L 0 x) (weights 0) (weights 1) hreadout hb.1 hb.2

/-- An exceptional literal profile with arbitrary baseline heads reaches a
global unit comparison. No baseline classification or baseline path is an
input hypothesis; both are derived from the physical source identity. -/
theorem exceptional_profile_to_unit (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (F G : Fin 6 → ℝ) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ)
    (b₁ b₂ b₃ : Bool) (hex : ExceptionalFlags b₁ b₂ b₃)
    (hF0 : F 0=0) (hF1 : F 1=0) (hG0 : G 0=0) (hG1 : G 1=0)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G rows weights b₁ b₂ b₃).eval x=Maximum 4 x) :
    ∃ endpoint : Network 4 6 5,
      JoinedIn (ExactSet 4 6 5) (profileNet U F G rows weights b₁ b₂ b₃) endpoint ∧
      endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
      (∀ x, endpoint.eval x=Maximum 4 x) ∧ endpoint.w₃ 0=1 ∧
      endpoint.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U) := by
  apply opposite_profile_to_unit U F G rows weights b₁ b₂ b₃
    (exceptional_head_output_signs U hU F G rows weights b₁ b₂ b₃ hex hF0 hF1 hG0 hG1 hFG hnet) hnet
  intro P Q hnormalized
  exact normalized_profile_to_unit U hU F G P Q b₁ b₂ b₃ hex hF0 hF1 hG0 hG1 hFG hnormalized

/-- The exact-fiber form consumed by raw three-atom attachment assembly. -/
theorem exceptional_profile_to_unit_fiber (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (F G : Fin 6 → ℝ) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ)
    (b₁ b₂ b₃ : Bool) (hex : ExceptionalFlags b₁ b₂ b₃)
    (hF0 : F 0=0) (hF1 : F 1=0) (hG0 : G 0=0) (hG1 : G 1=0)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G rows weights b₁ b₂ b₃).eval x=Maximum 4 x) :
    ∃ endpoint : ExactFiber 4 6 5,
      JoinedIn (ExactSet 4 6 5) (profileNet U F G rows weights b₁ b₂ b₃) endpoint.val ∧
      endpoint.val.W₁=pairedRows U ∧ endpoint.val.HasZeroBiases ∧ endpoint.val.w₃ 0=1 ∧
      endpoint.val.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U) := by
  obtain ⟨endpoint,hjoin,hfirst,hbias,hexact,houtput,hrow⟩ :=
    exceptional_profile_to_unit U hU F G rows weights b₁ b₂ b₃ hex hF0 hF1 hG0 hG1 hFG hnet
  exact ⟨⟨endpoint,hexact⟩,hjoin,hfirst,hbias,houtput,hrow⟩

end MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
