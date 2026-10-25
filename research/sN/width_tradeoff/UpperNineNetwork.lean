import research.sN.width_tradeoff.UpperNineIdentity

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections


private def firstQ : Fin 9 → Fin 5 → ℚ := ![![-1,1,0,0,0],
    ![-1,0,1,0,0],
    ![0,-1,1,0,0],
    ![-1,0,0,1,0],
    ![-1,0,0,0,1],
    ![0,0,0,1,-1],
    ![0,0,1,0,-1],
    ![1,0,0,0,0],
    ![-1,0,0,0,0]]

private def rowsQ : Fin 12 → Fin 9 → ℚ := ![![0,1/2,-1/2,-1/2,0,0,-1/2,0,0],
    ![1/2,0,0,-1/2,0,1/2,-1/2,0,0],
    ![1/2,0,1/2,0,0,1/2,-1/2,0,0],
    ![0,0,0,0,0,1,-1,0,0],
    ![0,0,1/2,0,0,1/2,-1/2,0,0],
    ![0,1/2,-1/2,-1/2,0,0,0,0,0],
    ![0,1/2,-1/2,0,-1/2,0,0,0,0],
    ![0,1/2,0,0,-1/2,0,0,0,0],
    ![0,1/2,0,0,0,1/2,-1/2,0,0],
    ![1,0,0,-1,0,0,0,0,0],
    ![1/2,0,0,-1/2,0,1/2,0,0,0],
    ![1,0,0,0,-1,0,0,0,0]]

private def outQ : Fin 12 → ℚ := ![1,-1,1,1,-1,-1,-1,1,-1,1,-1,1]

private def remQ : Fin 9 → ℚ := ![-1/2,1/2,0,0,1,1/2,0,1,-1]

private def first : Fin 9 → Fin 5 → ℝ := fun j i => firstQ j i

private def rows : Fin 12 → Fin 9 → ℝ := fun k j => rowsQ k j

private def out : Fin 12 → ℝ := fun k => outQ k

private def rem : Fin 9 → ℝ := fun j => remQ j

private noncomputable def features (x : Point 5) : Fin 9 → ℝ := ![relu (x 1 - x 0), relu (x 2 - x 0), relu (x 2 - x 1), relu (x 3 - x 0), relu (x 4 - x 0), relu (x 3 - x 4), relu (x 2 - x 4), relu (x 0), relu (-x 0)]

private theorem first_eval (x : Point 5) (j : Fin 9) :
    relu (∑ i, first j i*x i) = features x j := by
  fin_cases j <;> norm_num [first, firstQ, features, Fin.sum_univ_succ] <;>
    congr 1 <;> ring_nf <;> rfl

private theorem expansion (x : Point 5) :
    Maximum 5 x =
      ∑ k, out k * relu (lf (rows k) fun j => relu (∑ i, first j i*x i)) +
      lf rem (fun j => relu (∑ i, first j i*x i)) := by
  simp_rw [first_eval]
  rw [identity]
  simp [lf, rows, rowsQ, out, outQ, rem, remQ, features, Fin.sum_univ_succ, rhs]
  have h := relu_sub_relu_neg_self (x 0)
  ring_nf
  linarith [h]

/-- Exact max-five at physical widths (9,14), rational weights, zero biases. -/
theorem max_five_nine_fourteen :
    ∃ net : Network 5 9 14,
      (∀ x, net.eval x = Maximum 5 x) ∧
      net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply network_of_rows first (fun j i => ?_) rows (fun k j => ?_)
    out (fun k => ?_) rem (fun j => ?_) (Maximum 5) expansion
  all_goals apply mem_ratField_iff.mpr
  · exact ⟨firstQ j i, rfl⟩
  · exact ⟨rowsQ k j, rfl⟩
  · exact ⟨outQ k, rfl⟩
  · exact ⟨remQ j, rfl⟩

#print axioms max_five_nine_fourteen
end MaxCaterpillar.WidthTradeoff.P4
