import MaxCaterpillar.SmallN.Max5General4

/-! A physical (10,6) no-skip max-five network, proved from the existing
kernel-checked identity. No external numerical or certificate verdict is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MaxCaterpillar.WidthTradeoff
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections

private def firstQ : Fin 10 → Fin 5 → ℚ :=
  ![![1,-1,0,0,0], ![1,0,-1,0,0], ![0,1,-1,0,0],
    ![0,-1,1,0,0], ![0,-1,0,1,0], ![0,1,0,0,-1],
    ![0,-1,0,0,1], ![0,0,0,1,-1], ![0,1,0,0,0], ![0,-1,0,0,0]]

private def rowsQ : Fin 4 → Fin 10 → ℚ :=
  ![![0,-1,1,-1,0,-1,1,1,0,0],
    ![1/2,-1,1,-1/2,-1/2,-1,1/2,1,0,0],
    ![-1,0,0,1,-1,0,1,0,0,0],
    ![-1,0,0,1,1,0,-1,0,0,0]]

private def outQ : Fin 4 → ℚ := ![1,-1,1/2,1/2]
private def remQ : Fin 10 → ℚ := ![1,0,0,0,0,0,0,0,1,-1]
private def first : Fin 10 → Fin 5 → ℝ := fun j i => firstQ j i
private def rows : Fin 4 → Fin 10 → ℝ := fun k j => rowsQ k j
private def out : Fin 4 → ℝ := fun k => outQ k
private def rem : Fin 10 → ℝ := fun j => remQ j

private noncomputable def features (x : Point 5) : Fin 10 → ℝ :=
  ![relu (x 0-x 1), relu (x 0-x 2), relu (x 1-x 2),
    relu (x 2-x 1), relu (x 3-x 1), relu (x 1-x 4),
    relu (x 4-x 1), relu (x 3-x 4), relu (x 1), relu (-x 1)]

private theorem first_eval (x : Point 5) (j : Fin 10) :
    relu (∑ i, first j i*x i) = features x j := by
  fin_cases j <;> norm_num [first, firstQ, features, Fin.sum_univ_succ] <;>
    congr 1 <;> ring_nf <;> rfl

private theorem reverse_relu (a b : ℝ) :
    relu (b-a) = relu (a-b)-a+b := by
  have h := relu_sub_relu_neg_self (a-b)
  rw [neg_sub] at h
  linarith

private theorem expansion (x : Point 5) :
    Maximum 5 x =
      ∑ k, out k * relu (lf (rows k) fun j => relu (∑ i, first j i*x i)) +
      lf rem (fun j => relu (∑ i, first j i*x i)) := by
  simp_rw [first_eval]
  rw [Max5General4.identity]
  simp [lf, rows, rowsQ, out, outQ, rem, remQ, features,
    Fin.sum_univ_succ, Max5General4.rhs]
  rw [reverse_relu (x 1) (x 2), reverse_relu (x 1) (x 3),
    reverse_relu (x 1) (x 4)]
  have h := relu_sub_relu_neg_self (x 1)
  ring_nf
  linarith [h]

/-- Exact max-five at physical widths (10,6), rational weights, zero biases. -/
theorem max_five_ten_six :
    ∃ net : Network 5 10 6,
      (∀ x, net.eval x = Maximum 5 x) ∧
      net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply network_of_rows first (fun j i => ?_) rows (fun k j => ?_)
    out (fun k => ?_) rem (fun j => ?_) (Maximum 5) expansion
  all_goals apply mem_ratField_iff.mpr
  · exact ⟨firstQ j i, rfl⟩
  · exact ⟨rowsQ k j, rfl⟩
  · exact ⟨outQ k, rfl⟩
  · exact ⟨remQ j, rfl⟩

#print axioms max_five_ten_six
end MaxCaterpillar.WidthTradeoff
