import MaxCaterpillar.Fiber.Count65.Star.PhysicalChart.Core

/-! # Actual coordinate recovery and separation of the star physical charts

Every statement concerns entries of the ordinary network arrays. Dictionary
parameter, core orientation bits, slack, and translation coefficients can be
read back from these entries without using semantic network equality.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open MaxCaterpillar.Frontier

lemma orientation_ne_zero (b : Bool) : orientation b≠0 := by
  cases b <;> norm_num [orientation]

lemma orientation_mul_self (b : Bool) : orientation b*orientation b=1 := by
  cases b <;> norm_num [orientation]

theorem orientation_injective : Function.Injective orientation := by
  intro a b h
  cases a <;> cases b <;> norm_num [orientation] at h ⊢

lemma neg_orientation_positive_iff (b : Bool) : 0 < -orientation b ↔ b=true := by
  cases b <;> norm_num [orientation]

/-- The actual first matrix records r in one coordinate. -/
theorem branchIChart_dictionary_coordinate (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₁ 3 1=p.val.1.val.1-1 := rfl

theorem branchIIChart_dictionary_coordinate (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).W₁ 3 1=p.val.1.val.1-1 := rfl

theorem branchIChart_dictionary_recover (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₁ 3 1+1=p.val.1.val.1 := by
  rw [branchIChart_dictionary_coordinate]
  ring

theorem branchIIChart_dictionary_recover (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).W₁ 3 1+1=p.val.1.val.1 := by
  rw [branchIIChart_dictionary_coordinate]
  ring

/-- The independent feature coefficient reads every original orientation bit. -/
theorem branchIChart_core_W (o : Fin 3→Bool) (p : BranchIFiber o) (i : Fin 3) :
    (branchIChart o p).W₂ (Fin.castAdd 2 i) 2 = -orientation (o i) := by
  fin_cases i
  · change orientation (o 0)*(-1) = -orientation (o 0)
    ring
  · change orientation (o 1)*(-1) = -orientation (o 1)
    ring
  · change orientation (o 2)*(-1) = -orientation (o 2)
    ring

theorem branchIIChart_core_W (o : Fin 3→Bool) (p : BranchIIFiber o) (i : Fin 3) :
    (branchIIChart o p).W₂ (Fin.castAdd 2 i) 2 = -orientation (o i) := by
  fin_cases i
  · change orientation (o 0)*(-1) = -orientation (o 0)
    ring
  · change orientation (o 1)*(-1) = -orientation (o 1)
    ring
  · change orientation (o 2)*(-1) = -orientation (o 2)
    ring

theorem branchIChart_orientation_iff (o : Fin 3→Bool) (p : BranchIFiber o) (i : Fin 3) :
    0 < (branchIChart o p).W₂ (Fin.castAdd 2 i) 2 ↔ o i=true := by
  rw [branchIChart_core_W]
  exact neg_orientation_positive_iff _

theorem branchIIChart_orientation_iff (o : Fin 3→Bool) (p : BranchIIFiber o) (i : Fin 3) :
    0 < (branchIIChart o p).W₂ (Fin.castAdd 2 i) 2 ↔ o i=true := by
  rw [branchIIChart_core_W]
  exact neg_orientation_positive_iff _

theorem branchIChart_slack_coordinate (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₂ 1 0=orientation (o 1)*p.val.1.val.2 := by
  change orientation (o 1)*(p.val.1.val.1*p.val.1.val.2)/p.val.1.val.1=
    orientation (o 1)*p.val.1.val.2
  field_simp [ne_of_gt p.val.1.property.1]
  ring

theorem branchIIChart_slack_coordinate (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).W₂ 0 1=orientation (o 0)*p.val.1.val.2 := rfl

theorem branchIChart_slack_recover (o : Fin 3→Bool) (p : BranchIFiber o) :
    orientation (o 1)*(branchIChart o p).W₂ 1 0=p.val.1.val.2 := by
  rw [branchIChart_slack_coordinate,← mul_assoc,orientation_mul_self,one_mul]

theorem branchIIChart_slack_recover (o : Fin 3→Bool) (p : BranchIIFiber o) :
    orientation (o 0)*(branchIIChart o p).W₂ 0 1=p.val.1.val.2 := by
  rw [branchIIChart_slack_coordinate,← mul_assoc,orientation_mul_self,one_mul]

/-- Ordered physical output coefficients of both complete charts. -/
theorem branchIChart_outputs (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).w₃=![1,1,-1,1,-1] := rfl

theorem branchIIChart_outputs (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).w₃=![1,1,-1,1,-1] := rfl

/-- The third core uses the comparison feature throughout the first branch. -/
theorem branchIChart_negative_T (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₂ 2 3=orientation (o 2)/p.val.1.val.1 := by
  change orientation (o 2)*1/p.val.1.val.1=orientation (o 2)/p.val.1.val.1
  rw [mul_one]

theorem branchIChart_negative_T_ne_zero (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₂ 2 3≠0 := by
  rw [branchIChart_negative_T]
  exact div_ne_zero (orientation_ne_zero _) (ne_of_gt p.val.1.property.1)

/-- The third core omits that comparison feature throughout the second branch. -/
theorem branchIIChart_negative_T (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).W₂ 2 3=0 := by
  change orientation (o 2)*0/p.val.1.val.1=0
  simp

/-- The two ordered actual chart images cannot meet, including r=1. -/
theorem branch_charts_ne (o : Fin 3→Bool) (p : BranchIFiber o)
    (o' : Fin 3→Bool) (q : BranchIIFiber o') : branchIChart o p≠branchIIChart o' q := by
  intro he
  have hc := congrArg (fun net : Network 4 6 5 => net.W₂ 2 3) he
  dsimp only at hc
  rw [branchIIChart_negative_T] at hc
  exact branchIChart_negative_T_ne_zero o p hc

theorem branch_chart_images_disjoint :
    Disjoint (⋃ o, Set.range (branchIChart o)) (⋃ o, Set.range (branchIIChart o)) := by
  apply Set.disjoint_left.mpr
  intro net hn hm
  obtain ⟨o,p,hp⟩ := Set.mem_iUnion.mp hn
  obtain ⟨o',q,hq⟩ := Set.mem_iUnion.mp hm
  exact branch_charts_ne o p o' q (hp.trans hq.symm)

/-- Equal actual chart networks have equal orientation labels. -/
theorem branchIChart_equal_orientation (o o' : Fin 3→Bool) (p : BranchIFiber o)
    (q : BranchIFiber o') (he : branchIChart o p=branchIChart o' q) : o=o' := by
  funext i
  apply orientation_injective
  have hc := congrArg (fun net : Network 4 6 5 => net.W₂ (Fin.castAdd 2 i) 2) he
  dsimp only at hc
  rw [branchIChart_core_W,branchIChart_core_W] at hc
  exact neg_injective hc

theorem branchIIChart_equal_orientation (o o' : Fin 3→Bool) (p : BranchIIFiber o)
    (q : BranchIIFiber o') (he : branchIIChart o p=branchIIChart o' q) : o=o' := by
  funext i
  apply orientation_injective
  have hc := congrArg (fun net : Network 4 6 5 => net.W₂ (Fin.castAdd 2 i) 2) he
  dsimp only at hc
  rw [branchIIChart_core_W,branchIIChart_core_W] at hc
  exact neg_injective hc

/-- Actual translation coefficients of the two physical head rows. -/
theorem branchIChart_head_coordinates (o : Fin 3→Bool) (p : BranchIFiber o) :
    (branchIChart o p).W₂ 3 4=p.val.2.1 0 ∧
    (branchIChart o p).W₂ 3 5=p.val.2.1 1 ∧
    (branchIChart o p).W₂ 4 4=p.val.2.1 2 ∧
    (branchIChart o p).W₂ 4 5=p.val.2.1 3 := ⟨rfl,rfl,rfl,rfl⟩

theorem branchIIChart_head_coordinates (o : Fin 3→Bool) (p : BranchIIFiber o) :
    (branchIIChart o p).W₂ 3 4=p.val.2.1 0 ∧
    (branchIIChart o p).W₂ 3 5=p.val.2.1 1 ∧
    (branchIIChart o p).W₂ 4 4=p.val.2.1 2 ∧
    (branchIIChart o p).W₂ 4 5=p.val.2.1 3 := ⟨rfl,rfl,rfl,rfl⟩
/-- Recover fixed-space head coefficients from the actual physical matrix. -/
noncomputable def headCoefficients (r : ℝ) (net : Network 4 6 5) (k : Fin 5) : Fin 4→ℝ :=
  ![r*net.W₂ k 0,net.W₂ k 1,net.W₂ k 2,r*net.W₂ k 3]

theorem headLift_recover_positive_intercept {r : ℝ} (hr : 0<r)
    (P Q N : Fin 4→ℝ) (h : HeadTopology.Data (featureSpace 1)) :
    coefficientReadout 1 (headCoefficients r (headLift r P Q N h) 3)=h.2.1 := by
  have hc : headCoefficients r (headLift r P Q N h) 3=recoverReadout 1 h.2.1 := by
    funext j
    fin_cases j
    · change r*(recoverReadout 1 h.2.1 0/r)=recoverReadout 1 h.2.1 0
      exact mul_div_cancel' _ (ne_of_gt hr)
    · rfl
    · rfl
    · change r*(recoverReadout 1 h.2.1 3/r)=recoverReadout 1 h.2.1 3
      exact mul_div_cancel' _ (ne_of_gt hr)
  rw [hc]
  exact coefficientReadout_recover (by norm_num) _

theorem headLift_recover_negative_intercept {r : ℝ} (hr : 0<r)
    (P Q N : Fin 4→ℝ) (h : HeadTopology.Data (featureSpace 1)) :
    coefficientReadout 1 (headCoefficients r (headLift r P Q N h) 4)=h.2.2 := by
  have hc : headCoefficients r (headLift r P Q N h) 4=recoverReadout 1 h.2.2 := by
    funext j
    fin_cases j
    · change r*(recoverReadout 1 h.2.2 0/r)=recoverReadout 1 h.2.2 0
      exact mul_div_cancel' _ (ne_of_gt hr)
    · rfl
    · rfl
    · change r*(recoverReadout 1 h.2.2 3/r)=recoverReadout 1 h.2.2 3
      exact mul_div_cancel' _ (ne_of_gt hr)
  rw [hc]
  exact coefficientReadout_recover (by norm_num) _

theorem branchIChart_recover_head_intercepts (o : Fin 3→Bool) (p : BranchIFiber o) :
    coefficientReadout 1 (headCoefficients p.val.1.val.1 (branchIChart o p) 3)=p.val.2.2.1 ∧
    coefficientReadout 1 (headCoefficients p.val.1.val.1 (branchIChart o p) 4)=p.val.2.2.2 := by
  exact ⟨headLift_recover_positive_intercept p.val.1.property.1 _ _ _ _,
    headLift_recover_negative_intercept p.val.1.property.1 _ _ _ _⟩

theorem branchIIChart_recover_head_intercepts (o : Fin 3→Bool) (p : BranchIIFiber o) :
    coefficientReadout 1 (headCoefficients p.val.1.val.1 (branchIIChart o p) 3)=p.val.2.2.1 ∧
    coefficientReadout 1 (headCoefficients p.val.1.val.1 (branchIIChart o p) 4)=p.val.2.2.2 := by
  exact ⟨headLift_recover_positive_intercept p.val.1.property.1 _ _ _ _,
    headLift_recover_negative_intercept p.val.1.property.1 _ _ _ _⟩

lemma continuous_headCoefficients {β : Type*} [TopologicalSpace β]
    (r : β→ℝ) (n : β→Network 4 6 5) (k : Fin 5)
    (hr : Continuous r) (hn : Continuous n) :
    Continuous (fun b => headCoefficients (r b) (n b) k) := by
  have hw (j : Fin 6) : Continuous (fun b => (n b).W₂ k j) :=
    (continuous_apply j).comp ((continuous_apply k).comp (continuous_W₂.comp hn))
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun b => r b*(n b).W₂ k 0)
    exact hr.mul (hw 0)
  · change Continuous (fun b => (n b).W₂ k 1)
    exact hw 1
  · change Continuous (fun b => (n b).W₂ k 2)
    exact hw 2
  · change Continuous (fun b => r b*(n b).W₂ k 3)
    exact hr.mul (hw 3)
/-- All head parameters recovered directly from ordinary matrix entries. -/
noncomputable def recoverHeadData (r : ℝ) (net : Network 4 6 5) :
    HeadTopology.Data (featureSpace 1) :=
  (![net.W₂ 3 4,net.W₂ 3 5,net.W₂ 4 4,net.W₂ 4 5],
    coefficientReadout 1 (headCoefficients r net 3),
    coefficientReadout 1 (headCoefficients r net 4))

theorem branchIChart_recover_headData (o : Fin 3→Bool) (p : BranchIFiber o) :
    recoverHeadData p.val.1.val.1 (branchIChart o p)=p.val.2 := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · exact Prod.ext (branchIChart_recover_head_intercepts o p).1
      (branchIChart_recover_head_intercepts o p).2

theorem branchIIChart_recover_headData (o : Fin 3→Bool) (p : BranchIIFiber o) :
    recoverHeadData p.val.1.val.1 (branchIIChart o p)=p.val.2 := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · exact Prod.ext (branchIIChart_recover_head_intercepts o p).1
      (branchIIChart_recover_head_intercepts o p).2

/-- Each complete ordered physical chart has an exact coefficient inverse. -/
theorem branchIChart_injective (o : Fin 3→Bool) : Function.Injective (branchIChart o) := by
  intro p q he
  have hr := congrArg (fun n : Network 4 6 5 => n.W₁ 3 1+1) he
  dsimp only at hr
  rw [branchIChart_dictionary_recover,branchIChart_dictionary_recover] at hr
  have hk := congrArg (fun n : Network 4 6 5 => orientation (o 1)*n.W₂ 1 0) he
  dsimp only at hk
  rw [branchIChart_slack_recover,branchIChart_slack_recover] at hk
  have hh := congrArg (recoverHeadData p.val.1.val.1) he
  rw [branchIChart_recover_headData,hr,branchIChart_recover_headData] at hh
  exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hr hk)) hh)

theorem branchIIChart_injective (o : Fin 3→Bool) : Function.Injective (branchIIChart o) := by
  intro p q he
  have hr := congrArg (fun n : Network 4 6 5 => n.W₁ 3 1+1) he
  dsimp only at hr
  rw [branchIIChart_dictionary_recover,branchIIChart_dictionary_recover] at hr
  have hk := congrArg (fun n : Network 4 6 5 => orientation (o 0)*n.W₂ 0 1) he
  dsimp only at hk
  rw [branchIIChart_slack_recover,branchIIChart_slack_recover] at hk
  have hh := congrArg (recoverHeadData p.val.1.val.1) he
  rw [branchIIChart_recover_headData,hr,branchIIChart_recover_headData] at hh
  exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hr hk)) hh)

lemma continuous_recoverHeadData {β : Type*} [TopologicalSpace β]
    (r : β→ℝ) (n : β→Network 4 6 5) (hr : Continuous r) (hn : Continuous n) :
    Continuous (fun b => recoverHeadData (r b) (n b)) := by
  have hw (k : Fin 5) (j : Fin 6) : Continuous (fun b => (n b).W₂ k j) :=
    (continuous_apply j).comp ((continuous_apply k).comp (continuous_W₂.comp hn))
  have hs : Continuous (fun b => ![(n b).W₂ 3 4,(n b).W₂ 3 5,(n b).W₂ 4 4,(n b).W₂ 4 5]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hw 3 4
    · exact hw 3 5
    · exact hw 4 4
    · exact hw 4 5
  exact hs.prod_mk (((continuous_coefficientReadout 1).comp
    (continuous_headCoefficients r n 3 hr hn)).prod_mk
    ((continuous_coefficientReadout 1).comp (continuous_headCoefficients r n 4 hr hn)))
end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
