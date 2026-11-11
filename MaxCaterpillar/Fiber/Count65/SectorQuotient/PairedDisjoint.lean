import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairedInvariance
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! The paired first-matrix sector is disjoint from the mixed and star sectors
on raw physical networks. A positive linear functional isolates the sole
opposite pair in either nonpaired frame; paired frames have two such pairs. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

@[simp] private lemma v6_three {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 3 = d := rfl
@[simp] private lemma v6_four {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 4 = e := rfl
@[simp] private lemma v6_five {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 5 = f := rfl
@[simp] private lemma v4_three {α : Type*} (a b c d : α) :
    (![a,b,c,d] : Fin 4 → α) 3 = d := rfl

private def rowTest (F : Fin 6 → Point 4) (a : ℝ) (j : Fin 6) : ℝ :=
  a * F j 0 + F j 1 + F j 3

private lemma rowTest_opposite (F : Fin 6 → Point 4) (a c : ℝ) (j k : Fin 6)
    (h : F j = (-c) • F k) : rowTest F a j = -c * rowTest F a k := by
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  have h3 := congr_fun h 3
  simp only [Pi.smul_apply,smul_eq_mul] at h0 h1 h3
  unfold rowTest
  rw [h0,h1,h3]
  ring

private lemma opposite_only_anchors (F : Fin 6 → Point 4) (a : ℝ)
    (hn : ∀ j, 0 ≤ rowTest F a j)
    (hz : ∀ j, rowTest F a j = 0 ↔ j = 4 ∨ j = 5)
    (h4 : F 4 2 = 1) (h5 : F 5 2 = -1)
    (j k : Fin 6) (c : ℝ) (hc : 0 < c) (h : F j = (-c) • F k) :
    (j = 4 ∧ k = 5) ∨ (j = 5 ∧ k = 4) := by
  have he := rowTest_opposite F a c j k h
  have hp : c * rowTest F a k = 0 := by nlinarith [hn j,hn k]
  have hk0 := (mul_eq_zero.mp hp).resolve_left hc.ne'
  have hj0 : rowTest F a j = 0 := by nlinarith
  have hj := (hz j).mp hj0
  have hk := (hz k).mp hk0
  rcases hj with rfl|rfl <;> rcases hk with rfl|rfl
  · have hh := congr_fun h 2
    simp only [Pi.smul_apply,smul_eq_mul,h4] at hh
    nlinarith
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · have hh := congr_fun h 2
    simp only [Pi.smul_apply,smul_eq_mul,h5] at hh
    nlinarith

private lemma mixed_test (t : ℝ) (ht : 0 < t) :
    rowTest (Mixed65.firstRows t) ((t+2)/t) = ![2/t,1,1,1,0,0] := by
  funext j
  fin_cases j <;>
    simp only [rowTest,Mixed65.firstRows,v6_three,v6_four,v6_five,v4_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      mul_one,mul_zero,zero_add,add_zero]
  all_goals first | rfl | (field_simp [ht.ne'] <;> ring)

private lemma star_test (r : ℝ) :
    rowTest (Star65.firstRows r) 2 = ![1,1,1,1+r,0,0] := by
  funext j
  fin_cases j <;>
    simp only [rowTest,Star65.firstRows,v6_three,v6_four,v6_five,v4_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      mul_one,mul_zero,zero_add,add_zero]
  all_goals first | rfl | ring

theorem mixed_opposite_rows (t : ℝ) (ht : 0 < t) (j k : Fin 6)
    (c : ℝ) (hc : 0 < c) (h : Mixed65.firstRows t j = (-c) • Mixed65.firstRows t k) :
    (j = 4 ∧ k = 5) ∨ (j = 5 ∧ k = 4) := by
  have hdiv : 0 < (2:ℝ)/t := div_pos (by norm_num) ht
  apply opposite_only_anchors (Mixed65.firstRows t) ((t+2)/t) ?_ ?_ (by rfl) (by rfl) j k c hc h
  · intro i
    rw [mixed_test t ht]
    fin_cases i <;> simp only [v6_three,v6_four,v6_five,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    all_goals first | exact hdiv.le | norm_num
  · intro i
    rw [mixed_test t ht]
    fin_cases i <;> norm_num [Fin.ext_iff,Fin.coe_ofNat_eq_mod,ht.ne',hdiv.ne']
    all_goals decide

theorem star_opposite_rows (r : ℝ) (hr : 0 < r) (j k : Fin 6)
    (c : ℝ) (hc : 0 < c) (h : Star65.firstRows r j = (-c) • Star65.firstRows r k) :
    (j = 4 ∧ k = 5) ∨ (j = 5 ∧ k = 4) := by
  have hsum : 0 < 1+r := by linarith
  apply opposite_only_anchors (Star65.firstRows r) 2 ?_ ?_ (by rfl) (by rfl) j k c hc h
  · intro i
    rw [star_test]
    fin_cases i <;> simp only [v6_three,v6_four,v6_five,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    all_goals first | exact hsum.le | norm_num
  · intro i
    rw [star_test]
    fin_cases i <;> norm_num [Fin.ext_iff,Fin.coe_ofNat_eq_mod,hsum.ne']
    all_goals decide

private lemma paired_opposite_23 (a b c d : ℝ) (i : Fin 4) :
    pairedRows a b c d 2 i = -pairedRows a b c d 3 i := by
  fin_cases i <;> simp only [pairedRows,v6_three,v6_four,v6_five,v4_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
    neg_zero,neg_neg]
  all_goals rfl
private lemma paired_opposite_45 (a b c d : ℝ) (i : Fin 4) :
    pairedRows a b c d 4 i = -pairedRows a b c d 5 i := by
  fin_cases i <;> simp only [pairedRows,v6_three,v6_four,v6_five,v4_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
    neg_zero,neg_neg]
  all_goals rfl

private lemma not_paired_of_only_anchors (net : Network 4 6 5) (F : Fin 6 → Point 4)
    (hw : net.W₁ = F)
    (ho : ∀ (j k : Fin 6) (c : ℝ), 0 < c → F j = (-c) • F k →
      (j = 4 ∧ k = 5) ∨ (j = 5 ∧ k = 4)) : ¬PairedFirstMatrixForm net := by
  rintro ⟨a,b,c,d,_hd,s,hs,p,q,hrows⟩
  rw [hw] at hrows
  have h23 : F (p.symm 2) = (-(s (p.symm 2)/s (p.symm 3))) • F (p.symm 3) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hrows,hrows]
    simp only [Equiv.apply_symm_apply]
    rw [paired_opposite_23]
    field_simp [(hs (p.symm 3)).ne']
    ring
  have h45 : F (p.symm 4) = (-(s (p.symm 4)/s (p.symm 5))) • F (p.symm 5) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hrows,hrows]
    simp only [Equiv.apply_symm_apply]
    rw [paired_opposite_45]
    field_simp [(hs (p.symm 5)).ne']
    ring
  have h0 := ho _ _ _ (div_pos (hs (p.symm 2)) (hs (p.symm 3))) h23
  have h1 := ho _ _ _ (div_pos (hs (p.symm 4)) (hs (p.symm 5))) h45
  have h42 : p.symm (4:Fin 6) ≠ p.symm 2 := by
    intro h
    exact (by decide : (4:Fin 6) ≠ 2) (p.symm.injective h)
  have h43 : p.symm (4:Fin 6) ≠ p.symm 3 := by
    intro h
    exact (by decide : (4:Fin 6) ≠ 3) (p.symm.injective h)
  rcases h0 with ⟨ha,hb⟩|⟨ha,hb⟩ <;> rcases h1 with ⟨hc,hd⟩|⟨hc,hd⟩
  · exact h42 (hc.trans ha.symm)
  · exact h43 (hc.trans hb.symm)
  · exact h43 (hc.trans hb.symm)
  · exact h42 (hc.trans ha.symm)

theorem not_paired_of_mixed_rows (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hw : net.W₁ = Mixed65.firstRows t) : ¬PairedFirstMatrixForm net :=
  not_paired_of_only_anchors net _ hw (mixed_opposite_rows t ht)

theorem not_paired_of_star_rows (net : Network 4 6 5) (r : ℝ) (hr : 0 < r)
    (hw : net.W₁ = Star65.firstRows r) : ¬PairedFirstMatrixForm net :=
  not_paired_of_only_anchors net _ hw (star_opposite_rows r hr)

private lemma paired_canonicalize (net : Network 4 6 5) (F : Fin 6 → Point 4)
    (s : Fin 6 → ℝ) (hs : ∀ j, 0 < s j)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (hw : ∀ j i, net.W₁ j i = s j * F (p j) (q i))
    (hp : PairedFirstMatrixForm net) :
    ∃ n : Network 4 6 5, n.W₁=F ∧ PairedFirstMatrixForm n := by
  let b := scaleFirst net (fun j => (s j)⁻¹)
  let d := permuteHidden b p.symm (Equiv.refl _)
  let n := permuteInputs d q.symm
  have hb : PairedFirstMatrixForm b :=
    (SectorSeparation.pairedFirstMatrixForm_scaleFirst net _
      (fun j => inv_pos.mpr (hs j))).mpr hp
  have hd : PairedFirstMatrixForm d :=
    (SectorSeparation.pairedFirstMatrixForm_permuteHidden b p.symm (Equiv.refl _)).mpr hb
  refine ⟨n,?_,(SectorSeparation.pairedFirstMatrixForm_permuteInputs d q.symm).mpr hd⟩
  funext j i
  change (s (p.symm j))⁻¹ * net.W₁ (p.symm j) (q.symm i) = F j i
  rw [hw]
  simp only [Equiv.apply_symm_apply,←mul_assoc,inv_mul_cancel (hs (p.symm j)).ne',one_mul]

theorem not_paired_of_mixedFirstMatrixForm (net : Network 4 6 5)
    (hm : Mixed65.FirstMatrixForm net) : ¬PairedFirstMatrixForm net := by
  obtain ⟨t,ht,s,hs,p,q,hw⟩ := hm
  intro hp
  obtain ⟨n,hn,hp⟩ := paired_canonicalize net (Mixed65.firstRows t) s hs p q hw hp
  exact not_paired_of_mixed_rows n t ht hn hp

theorem not_paired_of_starFirstMatrixForm (net : Network 4 6 5)
    (hm : StarFirstMatrixForm net) : ¬PairedFirstMatrixForm net := by
  obtain ⟨r,hr,_hr1,s,hs,p,q,hw⟩ := hm
  intro hp
  obtain ⟨n,hn,hp⟩ := paired_canonicalize net (Star65.firstRows r) s hs p q hw hp
  exact not_paired_of_star_rows n r hr hn hp

end MaxCaterpillar.Fiber.Count65.SectorQuotient
