import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.First65.Irredundancy
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! The actual star first-matrix sector is relatively closed in the exact fiber.
All biases and all parameters after the first matrix remain unrestricted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation.StarClosed

open MaxCaterpillar.Fiber
variable {h₂ : ℕ}

@[simp] private theorem vec6_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))) = d
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem vec6_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))) = e
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem vec6_five {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))) = f
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem vec4_three {α : Type*} (a b c d : α) :
    ![a,b,c,d] (3 : Fin 4) = d := by
  change ![a,b,c,d] (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) = d
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem zero_four : (![0,0,0,0] : Fin 4 → ℝ) = 0 := by
  funext i
  fin_cases i <;> simp only [vec4_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
    Matrix.cons_val_succ', Pi.zero_apply]


noncomputable def rowScale (net : Network 4 6 h₂) : Fin 6 → ℝ :=
  ![net.W₁ 0 0, net.W₁ 1 1, net.W₁ 2 3, net.W₁ 3 0,
    net.W₁ 4 2, -net.W₁ 5 2]

noncomputable def branch (net : Network 4 6 h₂) : ℝ := -net.W₁ 3 2

noncomputable def template (net : Network 4 6 h₂) : Fin 6 → Fin 4 → ℝ :=
  ![![rowScale net 0, -rowScale net 0, 0, 0],
    ![0, rowScale net 1, -rowScale net 1, 0],
    ![0, 0, -rowScale net 2, rowScale net 2],
    ![rowScale net 3, branch net - rowScale net 3, -branch net, 0],
    ![0, 0, rowScale net 4, 0],
    ![0, 0, -rowScale net 5, 0]]

def ClosedRows (net : Network 4 6 h₂) : Prop :=
  (∀ j, 0 ≤ rowScale net j) ∧ 0 ≤ branch net ∧
    branch net ≤ rowScale net 3 ∧ net.W₁ = template net

private theorem continuous_entry (j : Fin 6) (i : Fin 4) :
    Continuous (fun net : Network 4 6 h₂ => net.W₁ j i) :=
  (continuous_apply i).comp ((continuous_apply j).comp continuous_W₁)

theorem continuous_rowScale : Continuous (rowScale : Network 4 6 h₂ → Fin 6 → ℝ) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [rowScale, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first | exact continuous_entry _ _ | exact (continuous_entry _ _).neg

theorem continuous_branch : Continuous (branch : Network 4 6 h₂ → ℝ) :=
  (continuous_entry 3 2).neg

private theorem continuous_template :
    Continuous (template : Network 4 6 h₂ → Fin 6 → Fin 4 → ℝ) := by
  have hs (j : Fin 6) : Continuous (fun net : Network 4 6 h₂ => rowScale net j) :=
    (continuous_apply j).comp continuous_rowScale
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  fin_cases j <;> fin_cases i <;> norm_num [template]
  all_goals first
    | exact continuous_const
    | exact hs _
    | exact (hs _).neg
    | exact continuous_branch.neg
    | exact continuous_branch.sub (hs _)

theorem isClosed_closedRows :
    IsClosed {net : Network 4 6 h₂ | ClosedRows net} := by
  unfold ClosedRows
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun j => ?_).inter ?_
  · exact isClosed_le continuous_const ((continuous_apply j).comp continuous_rowScale)
  · exact (isClosed_le continuous_const continuous_branch).inter
      ((isClosed_le continuous_branch ((continuous_apply 3).comp continuous_rowScale)).inter
        (isClosed_eq continuous_W₁ continuous_template))

private theorem fixed_row_zero (net : Network 4 6 h₂) (hn : ClosedRows net)
    (j : Fin 6) (hj : j ≠ 3) (hs : rowScale net j = 0) : net.W₁ j = 0 := by
  rw [hn.2.2.2]
  fin_cases j
  · change ![rowScale net 0, -rowScale net 0, 0, 0] = 0
    rw [show rowScale net 0 = 0 from hs]
    simpa only [neg_zero] using zero_four
  · change ![0, rowScale net 1, -rowScale net 1, 0] = 0
    rw [show rowScale net 1 = 0 from hs]
    simpa only [neg_zero] using zero_four
  · change ![0, 0, -rowScale net 2, rowScale net 2] = 0
    rw [show rowScale net 2 = 0 from hs]
    simpa only [neg_zero] using zero_four
  · exact (hj rfl).elim
  · change ![0, 0, rowScale net 4, 0] = 0
    rw [show rowScale net 4 = 0 from hs]
    exact zero_four
  · change ![0, 0, -rowScale net 5, 0] = 0
    rw [show rowScale net 5 = 0 from hs]
    simpa only [neg_zero] using zero_four

private theorem scale_pos (net : Network 4 6 h₂)
    (he : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net) :
    ∀ j, 0 < rowScale net j := by
  intro j
  have hz : rowScale net j ≠ 0 := by
    intro hs
    obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six he j
    apply hi
    by_cases hj : j = 3
    · subst j
      have hv : branch net = 0 := le_antisymm (hs ▸ hn.2.2.1) hn.2.1
      have hw : net.W₁ 3 = 0 := by
        rw [hn.2.2.2]
        change ![rowScale net 3, branch net - rowScale net 3, -branch net, 0] = 0
        rw [hs, hv]
        simpa only [sub_zero, neg_zero] using zero_four
      exact congr_fun hw i
    · exact congr_fun (fixed_row_zero net hn j hj hs) i
  exact lt_of_le_of_ne (hn.1 j) (Ne.symm hz)

theorem branch_pos (net : Network 4 6 h₂)
    (he : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net) :
    0 < branch net := by
  have hq := scale_pos net he hn 0
  have hu := scale_pos net he hn 3
  have hv : branch net ≠ 0 := by
    intro hv
    have hprop : net.W₁ 3 = (rowScale net 3 / rowScale net 0) • net.W₁ 0 := by
      rw [hn.2.2.2]
      funext i
      fin_cases i <;>
        simp only [template, vec6_three, vec6_four, vec6_five, vec4_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
          Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
          Pi.smul_apply, smul_eq_mul, hv, zero_sub, neg_zero, mul_zero, mul_neg,
          div_mul_cancel _ hq.ne']
    exact net.first_rows_not_pos_proportional_of_max4_six he
      (j := 3) (k := 0) (by decide) (div_pos hu hq) hprop
  exact lt_of_le_of_ne hn.2.1 (Ne.symm hv)

def labeled : Set (ExactFiber 4 6 5) :=
  {net | ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ s : Fin 6 → ℝ,
    (∀ j, 0 < s j) ∧ net.val.W₁ = fun j i => s j * Star65.firstRows r j i}

theorem closedRows_labeled (net : ExactFiber 4 6 5) (hn : ClosedRows net.val) :
    net ∈ labeled := by
  have hs := scale_pos net.val net.property hn
  have hv := branch_pos net.val net.property hn
  have hz : net.val.W₁ 3 0 ≠ 0 := (hs 3).ne'
  refine ⟨branch net.val / rowScale net.val 3, div_pos hv (hs 3), ?_,
    rowScale net.val, hs, ?_⟩
  · exact (div_le_one (hs 3)).mpr hn.2.2.1
  · rw [hn.2.2.2]
    funext j i
    fin_cases j <;> fin_cases i <;>
      simp only [template, Star65.firstRows, vec6_three, vec6_four, vec6_five, vec4_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
        mul_one, mul_neg, mul_zero, neg_zero, neg_neg]
    all_goals first | rfl | skip
    all_goals simp only [rowScale, branch, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ, vec6_three, vec6_four, vec6_five]
    all_goals (field_simp [hz]; ring)

theorem labeled_closedRows (net : ExactFiber 4 6 5) (hn : net ∈ labeled) :
    ClosedRows net.val := by
  obtain ⟨r, hr, hr1, s, hs, hw⟩ := hn
  have hscale : rowScale net.val = s := by
    funext j
    fin_cases j <;>
      simp only [rowScale, hw, Star65.firstRows, vec6_three, vec6_four, vec6_five, vec4_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
        mul_one, mul_neg, neg_neg]
    all_goals rfl
  have hb : branch net.val = s 3 * r := by
    unfold branch
    rw [hw]
    change -(s 3 * (-r)) = s 3 * r
    ring
  refine ⟨fun j => (hscale ▸ (hs j).le), ?_, ?_, ?_⟩
  · rw [hb]; exact (mul_pos (hs 3) hr).le
  · rw [hb, hscale]; nlinarith [hs 3]
  · rw [hw]
    funext j i
    fin_cases j <;> fin_cases i <;>
      simp only [template, hscale, hb, Star65.firstRows,
        vec6_three, vec6_four, vec6_five, vec4_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
        mul_one, mul_neg, mul_zero, neg_zero, neg_neg]
    all_goals first | rfl | skip
    all_goals change s 3 * _ = _
    all_goals simp only [sub_eq_add_neg, mul_add, mul_one, mul_neg]

theorem isClosed_labeled : IsClosed labeled := by
  have heq : labeled = {net : ExactFiber 4 6 5 | ClosedRows net.val} := by
    ext net
    exact ⟨labeled_closedRows net, closedRows_labeled net⟩
  rw [heq]
  exact isClosed_closedRows.preimage continuous_subtype_val

theorem star_eq_iUnion :
    {net : ExactFiber 4 6 5 | StarFirstMatrixForm net.val} =
      ⋃ p : Equiv.Perm (Fin 6), ⋃ q : Equiv.Perm (Fin 4),
        Mixed65.permutationHomeomorph p q '' labeled := by
  ext net
  constructor
  · rintro ⟨r, hr, hr1, c, hc, p, q, hrows⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    refine ⟨(Mixed65.permutationHomeomorph p q).symm net, ?_,
      (Mixed65.permutationHomeomorph p q).apply_symm_apply net⟩
    refine ⟨r, hr, hr1, (fun j => c (p.symm j)), (fun j => hc (p.symm j)), ?_⟩
    funext j i
    rw [Mixed65.permutationHomeomorph_symm_W₁, hrows]
    simp only [Equiv.apply_symm_apply]
  · intro hn
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hn
    obtain ⟨q, b, ⟨r, hr, hr1, c, hc, hrows⟩, hb⟩ := Set.mem_iUnion.mp hp
    subst net
    refine ⟨r, hr, hr1, (fun j => c (p j)), (fun j => hc (p j)), p, q, ?_⟩
    intro j i
    rw [Mixed65.permutationHomeomorph_W₁, hrows]

theorem isClosed_starFirstMatrixForm :
    IsClosed {net : ExactFiber 4 6 5 | StarFirstMatrixForm net.val} := by
  rw [star_eq_iUnion]
  apply isClosed_iUnion_of_finite
  intro p
  apply isClosed_iUnion_of_finite
  intro q
  exact (Mixed65.permutationHomeomorph p q).isClosedMap _ isClosed_labeled

end MaxCaterpillar.Fiber.Count65.SectorSeparation.StarClosed
