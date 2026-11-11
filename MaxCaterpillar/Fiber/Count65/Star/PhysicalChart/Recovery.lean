import MaxCaterpillar.Fiber.Count65.Star.FunctionSpans

/-! # Recovering actual physical coefficient rows

Actual function identities determine all four incoming coefficients because the
star dictionary is independent. No signs or unit magnitudes are assumed for
this recovery: every original nonzero independent-feature coefficient is kept.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

noncomputable def coefficientRow (d : CoefficientSystem (Fin 3)) (i : Fin 3) : Fin 4→ℝ :=
  ![d.U i,d.V i,d.W i,d.T i]

noncomputable def baseRow (d : CoefficientSystem (Fin 3)) : Fin 4→ℝ :=
  ![d.lU,d.lV,d.lW,d.lT]

noncomputable def rowForm (r : ℝ) (a : Fin 4→ℝ) (q v w : ℝ) : ℝ :=
  starLinearForm r (a 0) (a 1) (a 2) (a 3) q v w

noncomputable def branchIRows (r k : ℝ) : Fin 3→Fin 4→ℝ :=
  ![![(r-1)/r,0,-1,1/r],![k,1,-1,0],![k-1/r,0,-1,1/r]]

noncomputable def branchIIRows (r h : ℝ) : Fin 3→Fin 4→ℝ :=
  ![![(r-1)/r,h,-1,1/r],![1,1,-1,0],![1,1+h,-1,0]]

lemma rows_eq_of_functions {r : ℝ} (hr : 0<r) (a b : Fin 4→ℝ)
    (H : ∀ q v w,rowForm r a q v w=rowForm r b q v w) : a=b := by
  have hz := features_independent hr (a 0-b 0) (a 1-b 1) (a 2-b 2) (a 3-b 3) (by
    intro q v w
    have he := H q v w
    unfold rowForm starLinearForm at he
    linear_combination he)
  funext n
  fin_cases n
  · exact sub_eq_zero.mp hz.1
  · exact sub_eq_zero.mp hz.2.1
  · exact sub_eq_zero.mp hz.2.2.1
  · exact sub_eq_zero.mp hz.2.2.2

lemma row_recovered_of_normalized_function (d : CoefficientSystem (Fin 3))
    {r : ℝ} (hr : 0<r) (i : Fin 3) (hw : d.W i≠0) (a : Fin 4→ℝ)
    (H : ∀ q v w,starGate d r i q v w/(-d.W i)=rowForm r a q v w) :
    coefficientRow d i = fun n => (-d.W i)*a n := by
  apply rows_eq_of_functions hr
  intro q v w
  have he := (div_eq_iff (neg_ne_zero.mpr hw)).mp (H q v w)
  change starGate d r i q v w = _
  dsimp only [rowForm,starLinearForm] at he ⊢
  dsimp only [starGate] at he ⊢
  dsimp only [starLinearForm] at he ⊢
  linear_combination he

/-- Complete first-branch recovery of the four actual incoming coefficients. -/
theorem branchI_rows_recovered (d : CoefficientSystem (Fin 3)) {r : ℝ}
    (hr : 0<r) (hw : ∀ i,d.W i≠0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0)
    (hh : normalizedH d=0) (hn : normalizedN d r=normalizedK d-1)
    (hm : normalizedM d=0) (hl : normalizedL d r=1) :
    ∀ i,coefficientRow d i=fun n => (-d.W i)*branchIRows r (normalizedK d) i n := by
  obtain ⟨f0,f1,f2⟩ := ordered_gate_functions d r hr hw hu0 ht0 ht1 hv1
  intro i
  apply row_recovered_of_normalized_function d hr i (hw i)
  intro q v w
  fin_cases i
  · change starGate d r 0 q v w/(-d.W 0)=rowForm r (branchIRows r (normalizedK d) 0) q v w
    rw [f0,hh]
    change comparison r q v-max 0 w+0*max 0 v =
      starLinearForm r ((r-1)/r) 0 (-1) (1/r) q v w
    unfold comparison starLinearForm
    field_simp [ne_of_gt hr]
    ring
  · change starGate d r 1 q v w/(-d.W 1)=rowForm r (branchIRows r (normalizedK d) 1) q v w
    rw [f1]
    change max 0 v-max 0 w+normalizedK d*max 0 q=
      starLinearForm r (normalizedK d) 1 (-1) 0 q v w
    unfold starLinearForm
    ring
  · change starGate d r 2 q v w/(-d.W 2)=rowForm r (branchIRows r (normalizedK d) 2) q v w
    rw [f2,hn,hm,hl]
    change (normalizedK d-1)*max 0 q+0*max 0 v+1*comparison r q v-max 0 w=
      starLinearForm r (normalizedK d-1/r) 0 (-1) (1/r) q v w
    unfold comparison starLinearForm
    field_simp [ne_of_gt hr]
    ring

/-- Complete second-branch recovery, including its finite slack boundary. -/
theorem branchII_rows_recovered (d : CoefficientSystem (Fin 3)) {r : ℝ}
    (hr : 0<r) (hw : ∀ i,d.W i≠0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0)
    (hk : normalizedK d=1) (hn : normalizedN d r=1)
    (hm : normalizedM d=1+normalizedH d) (hl : normalizedL d r=0) :
    ∀ i,coefficientRow d i=fun n => (-d.W i)*branchIIRows r (normalizedH d) i n := by
  obtain ⟨f0,f1,f2⟩ := ordered_gate_functions d r hr hw hu0 ht0 ht1 hv1
  intro i
  apply row_recovered_of_normalized_function d hr i (hw i)
  intro q v w
  fin_cases i
  · change starGate d r 0 q v w/(-d.W 0)=rowForm r (branchIIRows r (normalizedH d) 0) q v w
    rw [f0]
    change comparison r q v-max 0 w+normalizedH d*max 0 v=
      starLinearForm r ((r-1)/r) (normalizedH d) (-1) (1/r) q v w
    unfold comparison starLinearForm
    field_simp [ne_of_gt hr]
    ring
  · change starGate d r 1 q v w/(-d.W 1)=rowForm r (branchIIRows r (normalizedH d) 1) q v w
    rw [f1,hk]
    change max 0 v-max 0 w+1*max 0 q=starLinearForm r 1 1 (-1) 0 q v w
    unfold starLinearForm
    ring
  · change starGate d r 2 q v w/(-d.W 2)=rowForm r (branchIIRows r (normalizedH d) 2) q v w
    rw [f2,hn,hm,hl]
    change 1*max 0 q+(1+normalizedH d)*max 0 v+0*comparison r q v-max 0 w=
      starLinearForm r 1 (1+normalizedH d) (-1) 0 q v w
    unfold starLinearForm
    ring

/-- The normalized branch classification recovers one of the two complete
actual row matrices, with the original orientation scale on every row. -/
theorem rows_recovered_of_branch (d : CoefficientSystem (Fin 3)) {r : ℝ}
    (hr : 0<r) (hw : ∀ i,d.W i≠0)
    (hu0 : d.U 0+d.W 0+d.T 0=0) (ht0 : d.W 0+r*d.T 0=0)
    (ht1 : d.T 1=0) (hv1 : d.V 1+d.W 1=0) (H : BranchNormalForm d r) :
    (normalizedK d≤0 ∧ ∀ i,coefficientRow d i=
      fun n => (-d.W i)*branchIRows r (normalizedK d) i n) ∨
    (normalizedH d≤-1 ∧ ∀ i,coefficientRow d i=
      fun n => (-d.W i)*branchIIRows r (normalizedH d) i n) := by
  rcases H with ⟨hh,hk,hn,hm,hl⟩ | ⟨hk,hh,hn,hm,hl⟩
  · exact Or.inl ⟨hk,branchI_rows_recovered d hr hw hu0 ht0 ht1 hv1 hh hn hm hl⟩
  · exact Or.inr ⟨hh,branchII_rows_recovered d hr hw hu0 ht0 ht1 hv1 hk hn hm hl⟩

noncomputable def correctionRow (d : CoefficientSystem (Fin 3)) : Fin 4→ℝ :=
  fun n => ∑ i : Fin 3,if 0<d.W i then d.out i*coefficientRow d i n else 0

lemma correctionRow_form (d : CoefficientSystem (Fin 3)) (r q v w : ℝ) :
    rowForm r (correctionRow d) q v w=
      ∑ i : Fin 3,if 0<d.W i then d.out i*starGate d r i q v w else 0 := by
  unfold rowForm correctionRow starLinearForm
  simp only [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0<d.W i
  · simp only [if_pos hi]
    change d.out i*d.U i*max 0 q+d.out i*d.V i*max 0 v+
      d.out i*d.W i*max 0 w+d.out i*d.T i*max 0 (q+r*v)=
      d.out i*(d.U i*max 0 q+d.V i*max 0 v+d.W i*max 0 w+d.T i*max 0 (q+r*v))
    ring
  · simp only [if_neg hi,zero_mul,zero_add]

/-- Recover the actual remainder coefficients from the actual orientation
correction identity, without any branch or output normalization assumption. -/
theorem base_row_recovered (d : CoefficientSystem (Fin 3)) {r : ℝ} (hr : 0<r)
    (H : ∀ q v w : ℝ,correctedBase d r (q,v,w)=max 0 w) :
    baseRow d=fun n => (![0,0,1,0] : Fin 4→ℝ) n-correctionRow d n := by
  apply rows_eq_of_functions hr
  intro q v w
  have he := H q v w
  change starBase d r q v w+
    (∑ i : Fin 3,if 0<d.W i then d.out i*starGate d r i q v w else 0)=max 0 w at he
  rw [← correctionRow_form] at he
  change starBase d r q v w=_
  dsimp only [rowForm,baseRow,starBase,starLinearForm] at he ⊢
  change d.lU*max 0 q+d.lV*max 0 v+d.lW*max 0 w+d.lT*max 0 (q+r*v)=
    (0-correctionRow d 0)*max 0 q+(0-correctionRow d 1)*max 0 v+
    (1-correctionRow d 2)*max 0 w+(0-correctionRow d 3)*max 0 (q+r*v)
  linear_combination he

/-- The physical orientation coefficient is exactly a binary sign whenever its
independent-feature coefficient has unit magnitude. -/
lemma orientation_factor_of_unit {w : ℝ} (hw : w = -1 ∨ w=1) :
    -w=if 0<w then -1 else 1 := by
  rcases hw with rfl | rfl <;> norm_num

private lemma correction_term_of_unit (o c : ℝ) {w : ℝ} (hw : w = -1 ∨ w=1) :
    (if 0<w then o*((-w)*c) else 0)=-(if 0<w then (1:ℝ) else 0)*o*c := by
  rcases hw with rfl | rfl <;> norm_num <;> ring

/-- In unit output normalization, the recovered remainder is precisely the
canonical independent feature plus the three binary orientation corrections. -/
theorem base_row_oriented (d : CoefficientSystem (Fin 3)) {r : ℝ} (hr : 0<r)
    (H : ∀ q v w : ℝ,correctedBase d r (q,v,w)=max 0 w)
    (C : Fin 3→Fin 4→ℝ) (hrow : ∀ i,coefficientRow d i=fun n => (-d.W i)*C i n)
    (hw : ∀ i,d.W i = -1 ∨ d.W i=1)
    (ho0 : d.out 0=1) (ho1 : d.out 1=1) (ho2 : d.out 2 = -1) :
    baseRow d=fun n => (![0,0,1,0] : Fin 4→ℝ) n+
      (if 0<d.W 0 then 1 else 0)*C 0 n+
      (if 0<d.W 1 then 1 else 0)*C 1 n-
      (if 0<d.W 2 then 1 else 0)*C 2 n := by
  funext n
  have he := congrFun (base_row_recovered d hr H) n
  have hc : correctionRow d n=
      -(if 0<d.W 0 then (1:ℝ) else 0)*C 0 n-
      (if 0<d.W 1 then 1 else 0)*C 1 n+
      (if 0<d.W 2 then 1 else 0)*C 2 n := by
    unfold correctionRow
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (if 0<d.W 0 then d.out 0*coefficientRow d 0 n else 0)+
      ((if 0<d.W 1 then d.out 1*coefficientRow d 1 n else 0)+
        ((if 0<d.W 2 then d.out 2*coefficientRow d 2 n else 0)+0))=_
    rw [hrow 0,hrow 1,hrow 2,ho0,ho1,ho2]
    have h0 := correction_term_of_unit 1 (C 0 n) (hw 0)
    have h1 := correction_term_of_unit 1 (C 1 n) (hw 1)
    have h2 := correction_term_of_unit (-1) (C 2 n) (hw 2)
    linear_combination h0+h1+h2
  rw [hc] at he
  change baseRow d n=_
  linarith only [he]

end MaxCaterpillar.Fiber.Count65.Star.PhysicalChart
