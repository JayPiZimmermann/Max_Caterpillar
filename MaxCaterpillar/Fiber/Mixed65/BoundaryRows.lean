import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.First65.Irredundancy
import MaxCaterpillar.Fiber.Mixed65.Construction

/-! # The closed coordinate wedge around mixed first rows

`ClosedRows` is a condition directly on the actual first weight matrix. Its
non-strict inequalities include both possible coordinate boundaries. Exactness
at first width six excludes all zero scaling factors and the duplicate-root
boundary. The remaining boundary is the vanishing of `mixedA`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.Fiber.Mixed65

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

/-- The six normalization pivots, read directly from the first weight matrix. -/
noncomputable def rowScale (net : Network 4 6 h₂) : Fin 6 → ℝ :=
  ![net.W₁ 0 0, net.W₁ 1 1, net.W₁ 2 3, net.W₁ 3 2,
    net.W₁ 4 2, -net.W₁ 5 2]

noncomputable def mixedA (net : Network 4 6 h₂) : ℝ := net.W₁ 3 0

noncomputable def mixedB (net : Network 4 6 h₂) : ℝ := net.W₁ 3 2

/-- The first matrix reconstructed from the seven pivot coordinates. -/
noncomputable def closedRowsTemplate (net : Network 4 6 h₂) : Fin 6 → Fin 4 → ℝ :=
  ![![rowScale net 0, -rowScale net 0, 0, 0],
    ![0, rowScale net 1, -rowScale net 1, 0],
    ![0, 0, -rowScale net 2, rowScale net 2],
    ![mixedA net, -mixedA net - mixedB net, mixedB net, 0],
    ![0, 0, rowScale net 4, 0],
    ![0, 0, -rowScale net 5, 0]]

/-- Nonnegative pivot coordinates and explicit matrix equations. No network
classification, scaling witness, or suffix condition is part of this predicate. -/
def ClosedRows (net : Network 4 6 h₂) : Prop :=
  (∀ j, 0 ≤ rowScale net j) ∧ 0 ≤ mixedA net ∧ net.W₁ = closedRowsTemplate net

private theorem continuous_first_entry (j : Fin 6) (i : Fin 4) :
    Continuous (fun net : Network 4 6 h₂ => net.W₁ j i) :=
  (continuous_apply i).comp ((continuous_apply j).comp continuous_W₁)

theorem continuous_rowScale : Continuous (rowScale : Network 4 6 h₂ → Fin 6 → ℝ) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [rowScale, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first | exact continuous_first_entry _ _ | exact (continuous_first_entry _ _).neg

theorem continuous_mixedA : Continuous (mixedA : Network 4 6 h₂ → ℝ) :=
  continuous_first_entry 3 0

theorem continuous_mixedB : Continuous (mixedB : Network 4 6 h₂ → ℝ) :=
  continuous_first_entry 3 2

private theorem continuous_closedRowsTemplate :
    Continuous (closedRowsTemplate : Network 4 6 h₂ → Fin 6 → Fin 4 → ℝ) := by
  have hs (j : Fin 6) : Continuous (fun net : Network 4 6 h₂ => rowScale net j) :=
    (continuous_apply j).comp continuous_rowScale
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  fin_cases j <;> fin_cases i <;> norm_num [closedRowsTemplate]
  all_goals first
    | exact continuous_const
    | exact hs _
    | exact (hs _).neg
    | exact continuous_mixedA
    | exact continuous_mixedB
    | exact continuous_mixedA.neg.sub continuous_mixedB

/-- The coordinate wedge is closed in the original Euclidean parameter space. -/
theorem isClosed_closedRows :
    IsClosed {net : Network 4 6 h₂ | ClosedRows net} := by
  unfold ClosedRows
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun j => ?_).inter ?_
  · exact isClosed_le continuous_const ((continuous_apply j).comp continuous_rowScale)
  · exact (isClosed_le continuous_const continuous_mixedA).inter
      (isClosed_eq continuous_W₁ continuous_closedRowsTemplate)

/-- The same wedge is relatively closed in the all-input exact fiber. -/
theorem isClosed_closedRows_exactFiber :
    IsClosed {net : ExactFiber 4 6 h₂ | ClosedRows net.val} :=
  isClosed_closedRows.preimage continuous_subtype_val

theorem closedRows_a_nonneg (net : Network 4 6 h₂) (hn : ClosedRows net) :
    0 ≤ mixedA net := hn.2.1

theorem closedRows_b_nonneg (net : Network 4 6 h₂) (hn : ClosedRows net) :
    0 ≤ mixedB net := hn.1 3

private theorem fixed_row_zero_of_scale_zero (net : Network 4 6 h₂)
    (hn : ClosedRows net) (j : Fin 6) (hj : j ≠ 3) (hs : rowScale net j = 0) :
    net.W₁ j = 0 := by
  rw [hn.2.2]
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

private theorem fixed_scale_pos (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net)
    (j : Fin 6) (hj : j ≠ 3) : 0 < rowScale net j := by
  have hz : rowScale net j ≠ 0 := by
    intro hs
    obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six hnet j
    apply hi
    exact congr_fun (fixed_row_zero_of_scale_zero net hn j hj hs) i
  exact lt_of_le_of_ne (hn.1 j) (Ne.symm hz)

/-- The mixed row's second pivot cannot vanish: it would then be zero or a
positive multiple of the first comparison row. -/
theorem closedRows_b_pos (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net) :
    0 < mixedB net := by
  have hb := closedRows_b_nonneg net hn
  have hq : 0 < rowScale net 0 := fixed_scale_pos net hnet hn 0 (by decide)
  have hbne : mixedB net ≠ 0 := by
    intro hb0
    have ha : 0 < mixedA net := by
      by_contra hna
      have ha0 : mixedA net = 0 :=
        le_antisymm (le_of_not_gt hna) (closedRows_a_nonneg net hn)
      obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six hnet 3
      apply hi
      have hz : net.W₁ 3 = 0 := by
        rw [hn.2.2]
        change ![mixedA net, -mixedA net - mixedB net, mixedB net, 0] = 0
        rw [ha0, hb0]
        simpa only [neg_zero, sub_zero] using zero_four
      exact congr_fun hz i
    have hprop : net.W₁ 3 = (mixedA net / rowScale net 0) • net.W₁ 0 := by
      rw [hn.2.2]
      funext i
      fin_cases i <;>
        simp only [closedRowsTemplate, vec6_three, vec6_four, vec6_five, vec4_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
          Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
          Pi.smul_apply, smul_eq_mul, hb0, sub_zero, mul_zero, mul_neg,
          div_mul_cancel _ hq.ne']
    exact net.first_rows_not_pos_proportional_of_max4_six hnet
      (j := 3) (k := 0) (by decide) (div_pos ha hq) hprop
  exact lt_of_le_of_ne hb (Ne.symm hbne)

/-- All six normalization factors are strictly positive on the exact fiber. -/
theorem closedRows_fixed_positive (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net) :
    ∀ j, 0 < rowScale net j := by
  intro j
  by_cases hj : j = 3
  · subst j
    exact closedRows_b_pos net hnet hn
  · exact fixed_scale_pos net hnet hn j hj

/-- Away from the remaining `mixedA = 0` boundary, the actual first matrix
has the mixed normal form with its uniquely determined continuous scales. -/
theorem closedRows_pos_scaled (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x) (hn : ClosedRows net)
    (ha : 0 < mixedA net) :
    0 < mixedA net / mixedB net ∧ (∀ j, 0 < rowScale net j) ∧
      net.W₁ = fun j i => rowScale net j * firstRows (mixedA net / mixedB net) j i := by
  have hb := closedRows_b_pos net hnet hn
  refine ⟨div_pos ha hb, closedRows_fixed_positive net hnet hn, ?_⟩
  rw [hn.2.2]
  funext j i
  have hnz : net.W₁ 3 2 ≠ 0 := hb.ne'
  fin_cases j <;> fin_cases i <;>
    simp only [closedRowsTemplate, firstRows, rowScale, mixedA, mixedB,
      vec6_three, vec6_four, vec6_five, vec4_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
      mul_one, mul_neg, mul_zero, neg_zero, neg_neg]
  all_goals (field_simp [hnz]; ring)

/-- Reading the pivots of an already scaled mixed matrix recovers every scale. -/
theorem rowScale_of_scaled_firstRows (net : Network 4 6 h₂) (t : ℝ) (s : Fin 6 → ℝ)
    (hW : net.W₁ = fun j i => s j * firstRows t j i) : rowScale net = s := by
  funext j
  fin_cases j <;>
    simp only [rowScale, hW, firstRows, vec6_three, vec6_four, vec6_five, vec4_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
      mul_one, mul_neg, neg_neg]
  all_goals rfl

end MaxCaterpillar.Fiber.Mixed65
