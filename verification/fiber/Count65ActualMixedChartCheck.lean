import MaxCaterpillar.Fiber.Count65.Mixed.ActualChartCoverage
set_option autoImplicit false
open MaxCaterpillar MaxCaterpillar.Fiber MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Fiber.Count65.ActualMixedLabels

example (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=false) :
    ∃ q : ResidualHeadChartA (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetA (orientations l) q :=
  physicalClass_chartA p l hl hz hb

example (p : Slice) (l : Label) (hl : p ∈ physicalClass l)
    (hz : p.val.2.HasZeroBiases) (hb : branch l=true) :
    ∃ q : ResidualHeadChartB (orientations l),
      q.val.1.1.val=time p ∧ q.val.2=actualHeadData p (rowOrder l) ∧
      permuteHidden p.val.2 (Equiv.refl _) (rowOrder l)=chartNetB (orientations l) q :=
  physicalClass_chartB p l hl hz hb

example (p : Slice) (l : Label) (hl : p ∈ physicalClass l) :
    if signed l then ∀ x : InvariantState,
      (Count65.HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x+
        (Count65.HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x=0
    else ∀ x : InvariantState,
      0 ≤ (Count65.HeadTopology.toHeads (actualHeadData p (rowOrder l))).A x ∧
        0 ≤ (Count65.HeadTopology.toHeads (actualHeadData p (rowOrder l))).B x :=
  physicalClass_headData_test p l hl

example (p : Slice) (hz : p.val.2.HasZeroBiases) :
    ∃ e : Equiv.Perm (Fin 5), ∃ bits : Fin 3 → Bool,
      (∃ q : ResidualHeadChartA bits, q.val.1.1.val=time p ∧
        q.val.2=actualHeadData p e ∧
        permuteHidden p.val.2 (Equiv.refl _) e=chartNetA bits q) ∨
      (∃ q : ResidualHeadChartB bits, q.val.1.1.val=time p ∧
        q.val.2=actualHeadData p e ∧
        permuteHidden p.val.2 (Equiv.refl _) e=chartNetB bits q) :=
  zeroBias_chart_coverage p hz

noncomputable def witness : Slice :=
  ⟨(1,branchANet 1 1),by
    refine ⟨by norm_num,rfl,?_,?_⟩
    · exact branchANet_eval 1 1 (by norm_num) (by norm_num)
    · intro i
      fin_cases i <;> norm_num [branchANet,signedLift]⟩

example : ∃ e : Equiv.Perm (Fin 5), ∃ bits : Fin 3 → Bool,
    (∃ q : ResidualHeadChartA bits,
      permuteHidden witness.val.2 (Equiv.refl _) e=chartNetA bits q) ∨
    (∃ q : ResidualHeadChartB bits,
      permuteHidden witness.val.2 (Equiv.refl _) e=chartNetB bits q) := by
  have hz : witness.val.2.HasZeroBiases := ⟨rfl,rfl,rfl⟩
  obtain ⟨e,bits,h⟩ := zeroBias_chart_coverage witness hz
  refine ⟨e,bits,?_⟩
  rcases h with ⟨q,_,_,he⟩ | ⟨q,_,_,he⟩
  · exact Or.inl ⟨q,he⟩
  · exact Or.inr ⟨q,he⟩

#print axioms physicalClass_chartA
#print axioms physicalClass_chartB
#print axioms physicalClass_headData_test
#print axioms zeroBias_chart_coverage
#print axioms witness
