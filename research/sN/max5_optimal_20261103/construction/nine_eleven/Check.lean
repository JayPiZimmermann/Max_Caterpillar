import research.sN.max5_optimal_20261103.construction.nine_eleven.Physical

/-! Independent expected-type and literal-array checks for the physical network. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Max5Optimal.NineEleven.Check
open BigOperators

example : ∃ net : Network 5 9 11,
    (∀ x : Fin 5 → ℝ,net.eval x=Maximum 5 x) ∧
      net.HasRationalWeights ∧ net.HasZeroBiases := exists_network

/-- The expected ordinary architecture is spelled out with all six arrays. -/
theorem literal_arrays :
    ∃ (A : Fin 9 → Fin 5 → ℝ) (b : Fin 9 → ℝ)
      (W : Fin 11 → Fin 9 → ℝ) (c : Fin 11 → ℝ)
      (d : Fin 11 → ℝ) (e : ℝ),
      b=0 ∧ c=0 ∧ e=0 ∧
      ∀ x : Fin 5 → ℝ,
        (∑ k, d k * relu ((∑ j,W k j * relu ((∑ i,A j i*x i)+b j))+c k))+e
          = Maximum 5 x := by
  refine ⟨network.W₁,network.b₁,network.W₂,network.b₂,network.w₃,network.b₃,
    rfl,rfl,rfl,?_⟩
  exact network_correct

/-- A concrete off-diagonal input tests the literal matrix convention. -/
theorem input_control : network.eval ![1,0,0,0,0] = 1 := by
  rw [network_correct]
  apply SmallN.maximum_eq_of_le _ (0 : Fin 5)
  intro i
  fin_cases i <;> norm_num

/-- Deleting the last positively weighted correction does change the function. -/
noncomputable def deletedLast : Network 5 9 11 :=
  {network with w₃ := fun k => if k.val=10 then 0 else network.w₃ k}

theorem deletion_control : deletedLast.eval ![1,0,0,0,0] = (1/2:ℝ) := by
  norm_num [deletedLast,network,Network.eval,firstWeights,secondWeights,outputWeights,
    Fin.sum_univ_succ,Fin.succ,Fin.ext_iff,relu]

#check @network_correct
#check @exists_network
#print axioms network_correct
#print axioms exists_network
#print axioms literal_arrays
#print axioms input_control
#print axioms deletion_control
end MaxCaterpillar.Max5Optimal.NineEleven.Check
