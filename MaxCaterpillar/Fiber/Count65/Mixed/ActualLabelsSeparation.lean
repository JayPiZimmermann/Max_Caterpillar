import MaxCaterpillar.Fiber.Count65.Mixed.ActualLabels
import MaxCaterpillar.Fiber.Count65.Mixed.RoleUniqueness

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ActualMixedLabels
open Set Function Mixed65 MaxCaterpillar.Frontier

lemma class_outputs {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    ∀ i, output p (rowOrder l i)=outputPattern i := h.1.1.1.1
lemma class_stationary {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    ∀ i : Fin 3, coeff p (rowOrder l (Fin.castAdd 2 i)) 4=0 ∧
      coeff p (rowOrder l (Fin.castAdd 2 i)) 5=0 := h.1.1.1.2
lemma class_orientations {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    ∀ i : Fin 3, (core p (rowOrder l)).W i=eps (orientations l) i := h.1.1.2
lemma class_directions {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    p ∈ directionClass l := h.1.2
lemma class_heads {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    p ∈ headClass l := h.2

lemma class_left_U {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    coeff p (rowOrder l 0) 0 = -(1+time p)*coeff p (rowOrder l 0) 2 := by
  have hd := class_directions h
  cases hb : branch l
  · have he : 1 ≤ time p*parameter l p ∧
        (core p (rowOrder l)).HasADirections (time p) (parameter l p) := by
      simpa [directionClass,hb] using hd
    exact he.2.1
  · have he : 1+time p ≤ time p*parameter l p ∧
        (core p (rowOrder l)).HasBDirections (time p) (parameter l p) := by
      simpa [directionClass,hb] using hd
    exact he.2.1

lemma class_right_U {p : Slice} {l : Label} (h : p ∈ physicalClass l) :
    coeff p (rowOrder l 1) 0 = -coeff p (rowOrder l 1) 2 := by
  have hd := class_directions h
  cases hb : branch l
  · have he : 1 ≤ time p*parameter l p ∧
        (core p (rowOrder l)).HasADirections (time p) (parameter l p) := by
      simpa [directionClass,hb] using hd
    exact he.2.2.2.2.1
  · have he : 1+time p ≤ time p*parameter l p ∧
        (core p (rowOrder l)).HasBDirections (time p) (parameter l p) := by
      simpa [directionClass,hb] using hd
    exact he.2.2.2.2.1

lemma class_positive_head {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l : Label} (h : p ∈ physicalClass l) : rowOrder l 3=r.positiveHead := by
  obtain ⟨i,hi⟩ := (rowOrder l).surjective r.positiveHead
  fin_cases i
  · have hz := (class_stationary h 0).1
    change coeff p (rowOrder l 0) 4=0 at hz
    change rowOrder l 0=r.positiveHead at hi
    rw [hi] at hz
    exact (r.positiveHead_carrier.ne' hz).elim
  · have hz := (class_stationary h 1).1
    change coeff p (rowOrder l 1) 4=0 at hz
    change rowOrder l 1=r.positiveHead at hi
    rw [hi] at hz
    exact (r.positiveHead_carrier.ne' hz).elim
  · have hz := (class_stationary h 2).1
    change coeff p (rowOrder l 2) 4=0 at hz
    change rowOrder l 2=r.positiveHead at hi
    rw [hi] at hz
    exact (r.positiveHead_carrier.ne' hz).elim
  · exact hi
  · have ho := class_outputs h 4
    change output p (rowOrder l 4) = -1 at ho
    change rowOrder l 4=r.positiveHead at hi
    rw [hi] at ho
    have hp := r.positive_output
    change output p r.positiveHead=1 at hp
    linarith only [ho,hp]

lemma class_negative_head {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l : Label} (h : p ∈ physicalClass l) : rowOrder l 4=r.negativeHead := by
  obtain ⟨i,hi⟩ := (rowOrder l).surjective r.negativeHead
  fin_cases i
  · have hz := (class_stationary h 0).2
    change coeff p (rowOrder l 0) 5=0 at hz
    change rowOrder l 0=r.negativeHead at hi
    rw [hi] at hz
    exact (r.negativeHead_carrier.ne' hz).elim
  · have hz := (class_stationary h 1).2
    change coeff p (rowOrder l 1) 5=0 at hz
    change rowOrder l 1=r.negativeHead at hi
    rw [hi] at hz
    exact (r.negativeHead_carrier.ne' hz).elim
  · have hz := (class_stationary h 2).2
    change coeff p (rowOrder l 2) 5=0 at hz
    change rowOrder l 2=r.negativeHead at hi
    rw [hi] at hz
    exact (r.negativeHead_carrier.ne' hz).elim
  · have ho := class_outputs h 3
    change output p (rowOrder l 3) = 1 at ho
    change rowOrder l 3=r.negativeHead at hi
    rw [hi] at ho
    have hn := r.negative_output
    change output p r.negativeHead = -1 at hn
    linarith only [ho,hn]
  · exact hi

lemma class_core_zero {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l : Label} (h : p ∈ physicalClass l) : rowOrder l 0=r.coreIndex 0 :=
  r.core_left_unique p.property.1 _ (class_outputs h 0)
    (class_stationary h 0).1 (class_stationary h 0).2 (class_left_U h)
lemma class_core_one {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l : Label} (h : p ∈ physicalClass l) : rowOrder l 1=r.coreIndex 1 :=
  r.core_right_unique p.property.1 _ (class_outputs h 1)
    (class_stationary h 1).1 (class_stationary h 1).2 (class_right_U h)
lemma class_core_two {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l : Label} (h : p ∈ physicalClass l) : rowOrder l 2=r.coreIndex 2 :=
  r.core_negative_unique _ (class_outputs h 2)
    (class_stationary h 2).1 (class_stationary h 2).2

lemma class_orders_unique {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l m : Label} (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) :
    rowOrder l=rowOrder m := by
  apply Equiv.ext
  intro i
  fin_cases i
  · exact (class_core_zero r hl).trans (class_core_zero r hm).symm
  · exact (class_core_one r hl).trans (class_core_one r hm).symm
  · exact (class_core_two r hl).trans (class_core_two r hm).symm
  · exact (class_positive_head r hl).trans (class_positive_head r hm).symm
  · exact (class_negative_head r hl).trans (class_negative_head r hm).symm

lemma class_branch_A_marker {p : Slice} {l : Label} (h : p ∈ physicalClass l)
    (hb : branch l=false) : coeff p (rowOrder l 0) 1=0 := by
  have he : 1 ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasADirections (time p) (parameter l p) := by
    simpa [directionClass,hb] using class_directions h
  exact he.2.2.1
lemma class_branch_B_marker {p : Slice} {l : Label} (h : p ∈ physicalClass l)
    (hb : branch l=true) : coeff p (rowOrder l 1) 3=0 := by
  have he : 1+time p ≤ time p*parameter l p ∧
      (core p (rowOrder l)).HasBDirections (time p) (parameter l p) := by
    simpa [directionClass,hb] using class_directions h
  exact he.2.2.2.2.2.2.1

lemma class_branches_unique {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l m : Label} (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) :
    branch l=branch m := by
  cases hb : branch l <;> cases hc : branch m
  · rfl
  · have hv := class_branch_A_marker hl hb
    have hT := class_branch_B_marker hm hc
    rw [class_core_zero r hl] at hv
    rw [class_core_one r hm] at hT
    exact (r.branch_markers_disjoint p.property.1 ⟨hv,hT⟩).elim
  · have hv := class_branch_A_marker hm hc
    have hT := class_branch_B_marker hl hb
    rw [class_core_zero r hm] at hv
    rw [class_core_one r hl] at hT
    exact (r.branch_markers_disjoint p.property.1 ⟨hv,hT⟩).elim
  · rfl

lemma eps_injective (a b : Bool) :
    (if a then (-1 : ℝ) else 1)=(if b then (-1 : ℝ) else 1) → a=b := by
  cases a <;> cases b <;> norm_num

lemma class_orientations_unique {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l m : Label} (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) :
    orientations l=orientations m := by
  have ho := class_orders_unique r hl hm
  funext i
  apply eps_injective
  change eps (orientations l) i=eps (orientations m) i
  rw [← class_orientations hl i,← class_orientations hm i,ho]

private lemma class_signed_hybrid_false {p : Slice}
    (r : PhysicalNormalForm p.val.2 p.val.1) {l m : Label}
    (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m)
    (hs : signed l=true) (hh : signed m=false) : False := by
  have hz : ∀ x : InvariantState,
      intercept p (rowOrder l 3) x+intercept p (rowOrder l 4) x=0 := by
    simpa [headClass,hs] using class_heads hl
  have hn : ∀ x : InvariantState,
      0 ≤ intercept p (rowOrder m 3) x ∧ 0 ≤ intercept p (rowOrder m 4) x := by
    simpa [headClass,hh] using class_heads hm
  have ho := class_orders_unique r hl hm
  rw [← ho] at hn
  obtain ⟨x,hx⟩ := r.remainder_nonzero
  have hA : intercept p (rowOrder l 3) x=0 := by
    have h := hn x
    have he := hz x
    linarith only [h.1,h.2,he]
  have hB : intercept p (rowOrder l 4) x=0 := by
    have h := hn x
    have he := hz x
    linarith only [h.1,h.2,he]
  have he := r.head_identity x 0
  simp only [Heads.eval,actualHeads,relu,neg_zero,max_self,mul_zero,zero_add] at he
  change relu (intercept p r.positiveHead x)-relu (intercept p r.negativeHead x)=
    r.core.base p.val.1 x.1 x.2.1 x.2.2 at he
  have hAr : intercept p r.positiveHead x=0 :=
    (congrArg (fun i => intercept p i x) (class_positive_head r hl)).symm.trans hA
  have hBr : intercept p r.negativeHead x=0 :=
    (congrArg (fun i => intercept p i x) (class_negative_head r hl)).symm.trans hB
  rw [hAr,hBr] at he
  have hzero : r.core.base p.val.1 x.1 x.2.1 x.2.2=0 := by
    simpa only [relu, max_self,sub_self,zero_add] using he.symm
  exact hx hzero

lemma class_headKinds_unique {p : Slice} (r : PhysicalNormalForm p.val.2 p.val.1)
    {l m : Label} (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) :
    signed l=signed m := by
  cases hs : signed l <;> cases ht : signed m
  · rfl
  · exact (class_signed_hybrid_false r hm hl ht hs).elim
  · exact (class_signed_hybrid_false r hl hm hs ht).elim
  · rfl

/-- All actual closed coefficient classes are disjoint; the certificate is
used only as an already-derived witness of the network's physical roles. -/
theorem physicalClass_unique_of_normalForm {p : Slice}
    (r : PhysicalNormalForm p.val.2 p.val.1) {l m : Label}
    (hl : p ∈ physicalClass l) (hm : p ∈ physicalClass m) : l=m :=
  Prod.ext (class_orders_unique r hl hm)
    (Prod.ext (class_branches_unique r hl hm)
      (Prod.ext (class_orientations_unique r hl hm) (class_headKinds_unique r hl hm)))

#print axioms physicalClass_unique_of_normalForm
end MaxCaterpillar.Fiber.Count65.ActualMixedLabels
