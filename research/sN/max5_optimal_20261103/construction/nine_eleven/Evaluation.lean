import research.sN.max5_optimal_20261103.construction.nine_eleven.Defs
import research.sN.max5_optimal_20261103.construction.nine_eleven.Weights

/-! The existing physical (9,11) construction, with all neurons counted.
The six-parameter Network is the ordinary no-skip architecture. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace MaxCaterpillar.Max5Optimal.NineEleven
open BigOperators SmallN

private theorem five_three (a b c d e : ℚ) : (![a,b,c,d,e] : Fin 5 → ℚ) 3 = d := rfl
private theorem five_four (a b c d e : ℚ) : (![a,b,c,d,e] : Fin 5 → ℚ) 4 = e := rfl

noncomputable def network : Network 5 9 11 :=
  ⟨fun j i => (firstWeights j i : ℝ), 0,
    fun k j => (secondWeights k j : ℝ), 0,
    fun k => (outputWeights k : ℝ), 0⟩

theorem rational_weights : network.HasRationalWeights :=
  ⟨fun j i => ⟨firstWeights j i,rfl⟩,
    fun k j => ⟨secondWeights k j,rfl⟩,
    fun k => ⟨outputWeights k,rfl⟩⟩

theorem zero_biases : network.HasZeroBiases := ⟨rfl,rfl,rfl⟩

theorem first_layer (x : Point 5) :
    (fun j => relu (∑ i, (firstWeights j i : ℝ)*x i)) =
      ![relu (x 0-x 3), relu (x 1-x 0), relu (x 1-x 2),
        relu (x 1-x 4), relu (x 2-x 3), relu (x 3-x 0),
        relu (x 4-x 0), relu (x 0), relu (-x 0)] := by
  funext j
  fin_cases j <;> norm_num [firstWeights,Fin.sum_univ_five,five_three,five_four] <;> congr 1 <;> ring

theorem eval_eq_rhs (x : Point 5) : network.eval x = rhs x := by
  unfold Network.eval network
  simp only [Pi.zero_apply,add_zero]
  have hf := fun j => congrFun (first_layer x) j
  simp_rw [hf]
  norm_num [secondWeights,outputWeights,Fin.sum_univ_succ,Fin.succ]
  have hhead := relu_sub_relu_neg_self
    (-relu (x 0-x 3)+relu (x 2-x 3)+relu (x 3-x 0)+relu (x 0)-relu (-x 0))
  have hcoord := relu_sub_relu_neg_self (x 0)
  unfold rhs
  ring_nf at hhead hcoord ⊢
  linear_combination hhead + hcoord

end MaxCaterpillar.Max5Optimal.NineEleven
