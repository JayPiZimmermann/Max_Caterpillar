import MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional.Heads

/-! # Exceptional literal profiles with normalized baseline outputs reach a unit gate -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
open BigOperators Frontier Absorption

lemma compensated_zeroBias (U : Fin 2 → Fin 2 → ℝ) (F G H : Fin 6 → ℝ)
    (b₁ b₂ b₃ split : Bool) (t : ℝ) :
    (switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H
      0 0 0 0 0 b₁ b₂ b₃ split t).HasZeroBiases := by
  refine ⟨rfl,?_,rfl⟩
  funext k
  let E := switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H
    0 0 0 0 0 b₁ b₂ b₃ split t
  change E.b₂ k=0
  refine Fin.addCases (motive := fun k : Fin (3+2) => E.b₂ k=0)
    (fun i : Fin 3 => ?_) (fun i : Fin 2 => ?_) k
  · fin_cases i
    · change (if b₁ then -(0+(t-1)*0+0*0) else 0+(t-1)*0+0*0)=0
      simp
    · change (if b₂ then -(0+0*0+(-1)*0) else 0+0*0+(-1)*0)=0
      simp
    · change (if b₃ then -(0+(t-1)*0+(-1)*0) else 0+(t-1)*0+(-1)*0)=0
      simp
  · simp only [E,switchingCompensatedNet,appendSpectators,Fin.append_right]
    change affineHeadBiases split (0+t*(orientationIndicator b₁-orientationIndicator b₃)*0) i=0
    simp only [mul_zero,zero_add,affineHeadBiases_zero,Pi.zero_apply]

lemma compensated_endpoint_row_zero (U : Fin 2 → Fin 2 → ℝ) (F G H : Fin 6 → ℝ)
    (b₁ b₂ b₃ split : Bool) :
    (switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H
      0 0 0 0 0 b₁ b₂ b₃ split 1).W₂ 0=
        if b₁ then -comparisonRow U else comparisonRow U := by
  cases b₁
  · funext j
    change comparisonRow U j+(1-1)*F j+0*G j=comparisonRow U j
    ring
  · funext j
    change -(comparisonRow U j+(1-1)*F j+0*G j)= -comparisonRow U j
    ring

theorem canonical_heads_to_unit (U : Fin 2 → Fin 2 → ℝ) (F G H : Fin 6 → ℝ)
    (b₁ b₂ b₃ split : Bool)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G (affineHeadRows split H) ![1,-1] b₁ b₂ b₃).eval x=Maximum 4 x) :
    ∃ endpoint : Network 4 6 5,
      JoinedIn (ExactSet 4 6 5) (profileNet U F G (affineHeadRows split H) ![1,-1] b₁ b₂ b₃) endpoint ∧
      endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
      (∀ x, endpoint.eval x=Maximum 4 x) ∧ endpoint.w₃ 0=1 ∧
      endpoint.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U) := by
  have hs : ∀ x, (switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H
      0 0 0 0 0 b₁ b₂ b₃ split 0).eval x=Maximum 4 x := by
    rw [compensated_start]
    exact hnet
  have hj := switchingCompensatedNet_joinedIn_exact (pairedRows U) 0 (comparisonRow U) F G H
    0 0 0 0 0 b₁ b₂ b₃ split hFG hs
  rw [compensated_start] at hj
  refine ⟨switchingCompensatedNet (pairedRows U) 0 (comparisonRow U) F G H
    0 0 0 0 0 b₁ b₂ b₃ split 1,hj,rfl,
    compensated_zeroBias U F G H b₁ b₂ b₃ split 1,hj.target_mem,rfl,?_⟩
  exact compensated_endpoint_row_zero U F G H b₁ b₂ b₃ split

/-- The baseline branch is derived from the actual all-input exact identity.
Its signed/split normalization and compensated contraction are physical paths. -/
theorem normalized_profile_to_unit (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (F G P Q : Fin 6 → ℝ) (b₁ b₂ b₃ : Bool) (hex : ExceptionalFlags b₁ b₂ b₃)
    (hF0 : F 0=0) (hF1 : F 1=0) (hG0 : G 0=0) (hG1 : G 1=0)
    (hFG : ∀ x, preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hnet : ∀ x, (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃).eval x=Maximum 4 x) :
    ∃ endpoint : Network 4 6 5,
      JoinedIn (ExactSet 4 6 5) (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃) endpoint ∧
      endpoint.W₁=pairedRows U ∧ endpoint.HasZeroBiases ∧
      (∀ x, endpoint.eval x=Maximum 4 x) ∧ endpoint.w₃ 0=1 ∧
      endpoint.W₂ 0=(if b₁ then -comparisonRow U else comparisonRow U) := by
  let L := residualRow U F G b₁ b₂ b₃
  have hf : ∀ x, relu (preact (pairedRows U) 0 P 0 x)-relu (preact (pairedRows U) 0 Q 0 x)=
      preact (pairedRows U) 0 L 0 x := by
    intro x
    have hh := profile_baseline_identity U hU F G ![P,Q] ![1,-1] b₁ b₂ b₃ hFG hnet x
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.tail_cons,one_mul,neg_one_mul,sub_eq_add_neg] using hh
  have hop := residual_increment_signs U F G b₁ b₂ b₃ hex hF0 hF1 hG0 hG1
  have hstyle : ∃ split : Bool, JoinedIn (ExactSet 4 6 5)
      (profileNet U F G ![P,Q] ![1,-1] b₁ b₂ b₃)
      (profileNet U F G (affineHeadRows split L) ![1,-1] b₁ b₂ b₃) := by
    rcases paired_mixed_baseline_classification U P Q L hop hf with hs|hs
    · refine ⟨false,equal_head_preacts_joined U F G ![P,Q] (affineHeadRows false L)
        ![1,-1] b₁ b₂ b₃ ?_ hnet⟩
      intro k x
      fin_cases k
      · change preact (pairedRows U) 0 L 0 x=preact (pairedRows U) 0 P 0 x
        exact (hs x).1.symm
      · change preact (pairedRows U) 0 (fun j => -L j) 0 x=preact (pairedRows U) 0 Q 0 x
        have hh := preact_neg (pairedRows U) 0 L 0 x
        simp only [neg_zero] at hh
        rw [hh]
        exact (hs x).2.symm
    · exact ⟨true,nonnegative_heads_joined_split U F G P Q L b₁ b₂ b₃
        (fun x => (hs x).1) (fun x => (hs x).2.1) hf hnet⟩
  obtain ⟨split,hheads⟩ := hstyle
  obtain ⟨endpoint,hjoin,hfirst,hbias,hexact,houtput,hcomparison⟩ :=
    canonical_heads_to_unit U F G L b₁ b₂ b₃ split hFG hheads.target_mem
  exact ⟨endpoint,hheads.trans hjoin,hfirst,hbias,hexact,houtput,hcomparison⟩

end MaxCaterpillar.Fiber.Count65.Paired.ThreeExceptional
