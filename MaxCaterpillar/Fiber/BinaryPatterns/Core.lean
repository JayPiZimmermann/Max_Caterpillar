import MaxCaterpillar.Fiber.NaturalInterventions

/-!
# Binary activation patterns can change inside one exact-fiber component

The binary convention is exactly the strict ReLU active predicate `0 < h`;
a zero preactivation is inactive. An explicit path of ordinary minimal-width
bias-free Max4 networks changes the binary patterns in both hidden layers.
At the diagonal input, even the number of active neurons changes in both
layers, so the endpoint difference is more than a relabelling of neurons.
-/
set_option autoImplicit false
namespace MaxCaterpillar
open BigOperators

namespace Network
variable {N h₁ h₂ : ℕ}

/-- The physical affine first preactivation, before applying ReLU. -/
noncomputable def firstPreactivation (net : Network N h₁ h₂) (x : Point N)
    (j : Fin h₁) : ℝ := (∑ i,net.W₁ j i*x i)+net.b₁ j

/-- The physical second preactivation on a natural input. -/
noncomputable def secondPreactivation (net : Network N h₁ h₂) (x : Point N)
    (k : Fin h₂) : ℝ := (∑ j,net.W₂ k j*net.firstHidden x j)+net.b₂ k

/-- Binary active/inactive pattern at the first hidden layer; zero is inactive. -/
noncomputable def firstBinary (net : Network N h₁ h₂) (x : Point N) : Fin h₁ → Bool :=
  fun j => decide (0 < net.firstHidden x j)

/-- Binary active/inactive pattern at the second hidden layer; zero is inactive. -/
noncomputable def secondBinary (net : Network N h₁ h₂) (x : Point N) : Fin h₂ → Bool :=
  fun k => decide (0 < net.secondHidden x k)

lemma firstBinary_eq_true_iff (net : Network N h₁ h₂) (x : Point N) (j : Fin h₁) :
    net.firstBinary x j = true ↔ 0 < (∑ i, net.W₁ j i*x i)+net.b₁ j := by
  simp [firstBinary, firstHidden, relu, lt_max_iff]

lemma secondBinary_eq_true_iff (net : Network N h₁ h₂) (x : Point N) (k : Fin h₂) :
    net.secondBinary x k = true ↔ 0 < (∑ j, net.W₂ k j*net.firstHidden x j)+net.b₂ k := by
  simp [secondBinary, secondHidden, relu, lt_max_iff]

/-- The number of active first hidden neurons on an input. -/
noncomputable def firstActiveCount (net : Network N h₁ h₂) (x : Point N) : ℕ :=
  (Finset.univ.filter fun j => net.firstBinary x j = true).card

/-- The number of active second hidden neurons on an input. -/
noncomputable def secondActiveCount (net : Network N h₁ h₂) (x : Point N) : ℕ :=
  (Finset.univ.filter fun k => net.secondBinary x k = true).card

lemma firstHidden_congr {a b : Network N h₁ h₂}
    (hW : a.W₁ = b.W₁) (hb : a.b₁ = b.b₁) (x : Point N) :
    a.firstHidden x = b.firstHidden x := by
  unfold firstHidden
  rw [hW,hb]
end Network


namespace Fiber.BinaryPatterns
open Frontier

private lemma succ_two_fin4 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
private lemma succ_two_fin5 : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
private lemma succ_three_fin5 : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
private lemma succ_two_fin6 : Fin.succ (2 : Fin 5) = (3 : Fin 6) := rfl
private lemma succ_three_fin6 : Fin.succ (3 : Fin 5) = (4 : Fin 6) := rfl
private lemma succ_four_fin6 : Fin.succ (4 : Fin 5) = (5 : Fin 6) := rfl

/-- The varying invertible two-coordinate code. -/
noncomputable def code (t : ℝ) (x : Point 4) : ℝ := x 1+(2*t-1)*x 3

/-- A physical (6,3) network, with no biases or skip connections. -/
noncomputable def net (t : ℝ) : Network 4 6 3 where
  W₁ := ![![1,-1,0,0],![0,0,1,-1],![0,1,0,2*t-1],
    ![0,-1,0,1-2*t],![0,0,0,1],![0,0,0,-1]]
  b₁ := 0
  W₂ := ![![t,1+t,t,t,1+t,t],![t,t,t,t,t,1+t],![1,-1,1,-1,-2*t,2*t]]
  b₂ := 0
  w₃ := ![1,-1,1]
  b₃ := 0

noncomputable def features (t : ℝ) (x : Point 4) : Fin 6 → ℝ :=
  ![relu (x 0-x 1),relu (x 2-x 3),relu (code t x),relu (-code t x),
    relu (x 3),relu (-x 3)]

lemma features_nonneg (t : ℝ) (x : Point 4) (j : Fin 6) : 0 ≤ features t x j := by
  fin_cases j <;> exact relu_nonneg _

lemma firstHidden_net (t : ℝ) (x : Point 4) : (net t).firstHidden x = features t x := by
  funext j
  fin_cases j <;>
    simp [Network.firstHidden,net,features,code,Fin.sum_univ_succ,sub_eq_add_neg] <;>
    simp only [succ_two_fin4,succ_two_fin5,succ_three_fin5,succ_two_fin6,succ_three_fin6,succ_four_fin6] <;> congr 1 <;> ring


noncomputable def common (t : ℝ) (x : Point 4) : ℝ := t*∑ j,features t x j

lemma common_nonneg (t : ℝ) (ht : 0 ≤ t) (x : Point 4) : 0 ≤ common t x :=
  mul_nonneg ht (Finset.sum_nonneg fun j _ => features_nonneg t x j)

private lemma first_base_sum (t : ℝ) (z : Fin 6 → ℝ) :
    (∑ j,(net t).W₂ 0 j*z j) = z 1+z 4+t*∑ j,z j := by
  norm_num [net,Fin.sum_univ_succ] <;>
    simp only [succ_two_fin4,succ_two_fin5,succ_three_fin5,succ_two_fin6,succ_three_fin6,succ_four_fin6] <;> ring

private lemma second_base_sum (t : ℝ) (z : Fin 6 → ℝ) :
    (∑ j,(net t).W₂ 1 j*z j) = z 5+t*∑ j,z j := by
  norm_num [net,Fin.sum_univ_succ] <;>
    simp only [succ_two_fin4,succ_two_fin5,succ_three_fin5,succ_two_fin6,succ_three_fin6,succ_four_fin6] <;> ring

private lemma comparison_sum (t : ℝ) (z : Fin 6 → ℝ) :
    (∑ j,(net t).W₂ 2 j*z j) = z 0-z 1+z 2-z 3-2*t*z 4+2*t*z 5 := by
  norm_num [net,Fin.sum_univ_succ] <;>
    simp only [succ_two_fin4,succ_two_fin5,succ_three_fin5,succ_two_fin6,succ_three_fin6,succ_four_fin6] <;> ring


lemma comparison_identity (t : ℝ) (x : Point 4) :
    (∑ j,(net t).W₂ 2 j*features t x j) =
      max (x 0) (x 1)-max (x 2) (x 3) := by
  rw [comparison_sum]
  change relu (x 0-x 1)-relu (x 2-x 3)+relu (code t x)-relu (-code t x)-
    2*t*relu (x 3)+2*t*relu (-x 3) = _
  have hA : relu (x 0-x 1)+x 1 = max (x 0) (x 1) := by
    simpa only [max_comm] using relu_sub_add (x 1) (x 0)
  have hB : relu (x 2-x 3)+x 3 = max (x 2) (x 3) := by
    simpa only [max_comm] using relu_sub_add (x 3) (x 2)
  have hu := relu_sub_relu_neg (code t x)
  have hb := relu_sub_relu_neg (x 3)
  unfold code at hu ⊢
  linear_combination hA-hB+hu-2*t*hb


lemma secondHidden_net (t : ℝ) (ht : 0 ≤ t) (x : Point 4) :
    (net t).secondHidden x =
      ![relu (x 2-x 3)+relu (x 3)+common t x,
        relu (-x 3)+common t x,
        relu (max (x 0) (x 1)-max (x 2) (x 3))] := by
  unfold Network.secondHidden
  rw [firstHidden_net]
  funext k
  fin_cases k
  · change relu ((∑ j,(net t).W₂ 0 j*features t x j)+0) = _
    rw [add_zero,first_base_sum]
    change relu (relu (x 2-x 3)+relu (x 3)+common t x) = _
    exact relu_of_nonneg
      (add_nonneg (add_nonneg (relu_nonneg _) (relu_nonneg _)) (common_nonneg t ht x))
  · change relu ((∑ j,(net t).W₂ 1 j*features t x j)+0) = _
    rw [add_zero,second_base_sum]
    change relu (relu (-x 3)+common t x) = _
    exact relu_of_nonneg (add_nonneg (relu_nonneg _) (common_nonneg t ht x))
  · change relu ((∑ j,(net t).W₂ 2 j*features t x j)+0) = _
    rw [add_zero,comparison_identity]
    rfl

/-- Every member of the half-line family computes Max4 on every real input. -/
theorem net_eval (t : ℝ) (ht : 0 ≤ t) (x : Point 4) : (net t).eval x = Maximum 4 x := by
  rw [Network.eval_eq_secondHidden,secondHidden_net t ht,Maximum_four]
  norm_num [net,Fin.sum_univ_succ]
  have hb : relu (x 2-x 3)+relu (x 3)-relu (-x 3) = max (x 2) (x 3) := by
    have h := relu_sub_add (x 3) (x 2)
    rw [max_comm] at h
    linarith [relu_sub_relu_neg (x 3)]
  have hf := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1))] at hf
  linarith only [hb,hf]


lemma net_zeroBiases (t : ℝ) : (net t).HasZeroBiases := ⟨rfl,rfl,rfl⟩

/-- Every output coefficient is nonzero, throughout the path. -/
theorem output_weights_nonzero (t : ℝ) (k : Fin 3) : (net t).w₃ k ≠ 0 := by
  fin_cases k <;> norm_num [net]

/-- The ordinary six first-layer neurons all have nonzero incoming rows. -/
theorem first_rows_nonzero (t : ℝ) (j : Fin 6) : ∃ i,(net t).W₁ j i ≠ 0 := by
  fin_cases j
  · exact ⟨0,by norm_num [net]⟩
  · exact ⟨2,by norm_num [net]⟩
  · exact ⟨1,by norm_num [net]⟩
  · exact ⟨1,by norm_num [net]⟩
  · refine ⟨3,?_⟩
    change (1 : ℝ) ≠ 0
    norm_num
  · refine ⟨3,?_⟩
    change (-1 : ℝ) ≠ 0
    norm_num

/-- No smaller first or second width can compute Max4, even with arbitrary biases. -/
theorem widths_minimal {h₁ h₂ : ℕ} (a : Network 4 h₁ h₂)
    (ha : ∀ x,a.eval x = Maximum 4 x) : 6 ≤ h₁ ∧ 3 ≤ h₂ :=
  max4_widths_iff.mp ⟨a,ha⟩

theorem continuous_net : Continuous net := by
  apply (continuous_network_iff _).mpr
  refine ⟨?_,continuous_const,?_,continuous_const,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro j
    apply continuous_pi
    intro i
    fin_cases j <;> fin_cases i <;> first
      | exact continuous_const
      | change Continuous (fun t : ℝ => 2*t-1)
        exact (continuous_const.mul continuous_id).sub continuous_const
      | change Continuous (fun t : ℝ => 1-2*t)
        exact continuous_const.sub (continuous_const.mul continuous_id)
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> fin_cases j <;> first
      | exact continuous_const
      | change Continuous (fun t : ℝ => t)
        exact continuous_id
      | change Continuous (fun t : ℝ => 1+t)
        exact continuous_const.add continuous_id
      | change Continuous (fun t : ℝ => -2*t)
        exact continuous_const.mul continuous_id
      | change Continuous (fun t : ℝ => 2*t)
        exact continuous_const.mul continuous_id


noncomputable def zeroExact : ExactFiber 4 6 3 := ⟨net 0,net_eval 0 (by norm_num)⟩
noncomputable def oneExact : ExactFiber 4 6 3 := ⟨net 1,net_eval 1 (by norm_num)⟩

open unitInterval

/-- A continuous path in the full ordinary all-input exact parameter fiber. -/
noncomputable def exactPath : Path zeroExact oneExact where
  toFun t := ⟨net (t : ℝ),net_eval _ t.property.1⟩
  continuous_toFun := (continuous_net.comp continuous_subtype_val).subtype_mk _
  source' := by apply Subtype.ext; rfl
  target' := by apply Subtype.ext; rfl

theorem same_exact_component :
    ConnectedComponents.mk zeroExact = ConnectedComponents.mk oneExact :=
  ConnectedComponents.coe_eq_coe'.2
    (pathComponent_subset_component _ (show Joined zeroExact oneExact from ⟨exactPath⟩).symm)

/-- The all-ones input is fixed by every input permutation. -/
def diagonal : Point 4 := fun _ => 1

lemma firstHidden_zero_diagonal : (net 0).firstHidden diagonal = ![0,0,0,0,1,0] := by
  rw [firstHidden_net]
  norm_num [features,code,diagonal,relu]

lemma firstHidden_one_diagonal : (net 1).firstHidden diagonal = ![0,0,2,0,1,0] := by
  rw [firstHidden_net]
  norm_num [features,code,diagonal,relu]

lemma secondHidden_zero_diagonal : (net 0).secondHidden diagonal = ![1,0,0] := by
  rw [secondHidden_net 0 (by norm_num)]
  norm_num [common,features,code,diagonal,relu,Fin.sum_univ_succ]

lemma secondHidden_one_diagonal : (net 1).secondHidden diagonal = ![4,3,0] := by
  rw [secondHidden_net 1 (by norm_num)]
  norm_num [common,features,code,diagonal,relu,Fin.sum_univ_succ]

lemma firstBinary_zero_diagonal : (net 0).firstBinary diagonal = ![false,false,false,false,true,false] := by
  funext j
  unfold Network.firstBinary
  rw [firstHidden_zero_diagonal]
  fin_cases j <;> norm_num

lemma firstBinary_one_diagonal : (net 1).firstBinary diagonal = ![false,false,true,false,true,false] := by
  funext j
  unfold Network.firstBinary
  rw [firstHidden_one_diagonal]
  fin_cases j <;> norm_num

lemma secondBinary_zero_diagonal : (net 0).secondBinary diagonal = ![true,false,false] := by
  funext k
  unfold Network.secondBinary
  rw [secondHidden_zero_diagonal]
  fin_cases k <;> norm_num

lemma secondBinary_one_diagonal : (net 1).secondBinary diagonal = ![true,true,false] := by
  funext k
  unfold Network.secondBinary
  rw [secondHidden_one_diagonal]
  fin_cases k <;> norm_num

lemma first_count_zero : (net 0).firstActiveCount diagonal = 1 := by
  rw [Network.firstActiveCount,firstBinary_zero_diagonal]
  decide
lemma first_count_one : (net 1).firstActiveCount diagonal = 2 := by
  rw [Network.firstActiveCount,firstBinary_one_diagonal]
  decide
lemma second_count_zero : (net 0).secondActiveCount diagonal = 1 := by
  rw [Network.secondActiveCount,secondBinary_zero_diagonal]
  decide
lemma second_count_one : (net 1).secondActiveCount diagonal = 2 := by
  rw [Network.secondActiveCount,secondBinary_one_diagonal]
  decide


/-- Both hidden layers change their binary active/inactive patterns. -/
theorem binary_patterns_differ :
    (net 0).firstBinary diagonal ≠ (net 1).firstBinary diagonal ∧
      (net 0).secondBinary diagonal ≠ (net 1).secondBinary diagonal := by
  rw [firstBinary_zero_diagonal,firstBinary_one_diagonal,
    secondBinary_zero_diagonal,secondBinary_one_diagonal]
  constructor <;> decide


/-- Binary active counts change in both hidden layers inside one path component
of the minimal, ordinary, bias-free Max4 exact fiber. No output neuron is spare. -/
theorem connected_binary_pattern_counterexample :
    ∃ a b : ExactFiber 4 6 3,
      Joined a b ∧ a.val.HasZeroBiases ∧ b.val.HasZeroBiases ∧
      (∀ k,a.val.w₃ k ≠ 0 ∧ b.val.w₃ k ≠ 0) ∧
      a.val.firstActiveCount diagonal = 1 ∧ b.val.firstActiveCount diagonal = 2 ∧
      a.val.secondActiveCount diagonal = 1 ∧ b.val.secondActiveCount diagonal = 2 := by
  exact ⟨zeroExact,oneExact,⟨exactPath⟩,net_zeroBiases 0,net_zeroBiases 1,
    fun k => ⟨output_weights_nonzero 0 k,output_weights_nonzero 1 k⟩,
    first_count_zero,first_count_one,second_count_zero,second_count_one⟩



end Fiber.BinaryPatterns
end MaxCaterpillar
