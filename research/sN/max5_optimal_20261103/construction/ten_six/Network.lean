import MaxCaterpillar.SmallN.Max5General4

/-! The sparse physical `(10,6)` MAX₅ construction, with no skip connections.
The four-fold identity already in the library is compiled here through its
ten actually used first-layer features. All six second-layer neurons count,
including the positive and negative copies of the signed head.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MaxCaterpillar.MaxFiveTenSix
open BigOperators SmallN

def firstWeights : Fin 10 → Fin 5 → ℚ :=
  ![![1,-1,0,0,0], ![1,0,-1,0,0], ![0,1,-1,0,0], ![0,-1,1,0,0],
    ![0,-1,0,1,0], ![0,1,0,0,-1], ![0,-1,0,0,1], ![0,0,0,1,-1],
    ![0,1,0,0,0], ![0,-1,0,0,0]]

def secondWeights : Fin 6 → Fin 10 → ℚ :=
  ![![1,0,0,0,0,0,0,0,1,-1],
    ![-1,0,0,0,0,0,0,0,-1,1],
    ![0,-1,1,-1,0,-1,1,1,0,0],
    ![1/2,-1,1,-1/2,-1/2,-1,1/2,1,0,0],
    ![-1,0,0,1,-1,0,1,0,0,0],
    ![-1,0,0,1,1,0,-1,0,0,0]]

def outputWeights : Fin 6 → ℚ := ![1,-1,1,-1,1/2,1/2]

/-- Ordinary two-hidden-layer architecture; all biases are zero. -/
noncomputable def net : Network 5 10 6 where
  W₁ := fun j i => (firstWeights j i : ℝ)
  b₁ := 0
  W₂ := fun k j => (secondWeights k j : ℝ)
  b₂ := 0
  w₃ := fun k => (outputWeights k : ℝ)
  b₃ := 0

noncomputable def firstArguments (x : Point 5) : Fin 10 → ℝ :=
  ![x 0-x 1, x 0-x 2, x 1-x 2, x 2-x 1, x 3-x 1,
    x 1-x 4, x 4-x 1, x 3-x 4, x 1, -x 1]

noncomputable def secondArguments (x : Point 5) : Fin 6 → ℝ :=
  ![x 1+relu (x 0-x 1), -(x 1+relu (x 0-x 1)),
    -x 2+x 4-relu (x 0-x 2)+relu (x 3-x 4),
    1/2*x 1-1/2*x 2-1/2*x 3+1/2*x 4+1/2*relu (x 0-x 1)
      -relu (x 0-x 2)+1/2*relu (x 1-x 2)-1/2*relu (x 1-x 3)
      -1/2*relu (x 1-x 4)+relu (x 3-x 4),
    -x 1+x 2-x 3+x 4-relu (x 0-x 1)+relu (x 1-x 2)
      -relu (x 1-x 3)+relu (x 1-x 4),
    -x 1+x 2+x 3-x 4-relu (x 0-x 1)+relu (x 1-x 2)
      +relu (x 1-x 3)-relu (x 1-x 4)]

theorem firstArguments_eq (x : Point 5) (j : Fin 10) :
    (∑ i, net.W₁ j i*x i)+net.b₁ j=firstArguments x j := by
  fin_cases j <;>
    norm_num [net,firstWeights,firstArguments,Fin.sum_univ_five,
      SmallN.Max5General4.cv0,SmallN.Max5General4.cv1,SmallN.Max5General4.cv2,
      SmallN.Max5General4.cv3,SmallN.Max5General4.cv4] <;> ring

theorem secondArguments_eq (x : Point 5) (k : Fin 6) :
    (∑ j,net.W₂ k j*relu ((∑ i,net.W₁ j i*x i)+net.b₁ j))+net.b₂ k =
      secondArguments x k := by
  simp_rw [firstArguments_eq]
  have h21 : relu (x 2-x 1)=relu (x 1-x 2)+x 2-x 1 := by
    have h := relu_sub_relu_neg_self (x 2-x 1)
    rw [neg_sub] at h
    linarith only [h]
  have h31 : relu (x 3-x 1)=relu (x 1-x 3)+x 3-x 1 := by
    have h := relu_sub_relu_neg_self (x 3-x 1)
    rw [neg_sub] at h
    linarith only [h]
  have h41 : relu (x 4-x 1)=relu (x 1-x 4)+x 4-x 1 := by
    have h := relu_sub_relu_neg_self (x 4-x 1)
    rw [neg_sub] at h
    linarith only [h]
  have h1 : relu (-x 1)=relu (x 1)-x 1 := by
    have h := relu_sub_relu_neg_self (x 1)
    linarith only [h]
  fin_cases k <;>
    norm_num [net,secondWeights,firstArguments,secondArguments,Fin.sum_univ_succ]
  all_goals
    ring_nf at h21 h31 h41 h1 ⊢
    linarith only [h21,h31,h41,h1]

/-- Exact MAX₅ on every real input, with physical widths `(10,6)`. -/
theorem net_eval (x : Point 5) : net.eval x=Maximum 5 x := by
  unfold Network.eval
  simp_rw [secondArguments_eq]
  rw [SmallN.Max5General4.identity]
  norm_num [net,outputWeights,secondArguments,SmallN.Max5General4.rhs,Fin.sum_univ_succ]
  have h := relu_sub_relu_neg_self (x 1+relu (x 0-x 1))
  ring_nf at h ⊢
  linarith only [h]

theorem net_rational : net.HasRationalWeights :=
  ⟨fun j i => ⟨firstWeights j i,rfl⟩,
   fun k j => ⟨secondWeights k j,rfl⟩,
   fun k => ⟨outputWeights k,rfl⟩⟩

theorem net_zero_biases : net.HasZeroBiases := ⟨rfl,rfl,rfl⟩

theorem exists_network :
    ∃ f : Network 5 10 6,
      (∀ x,f.eval x=Maximum 5 x) ∧ f.HasRationalWeights ∧ f.HasZeroBiases :=
  ⟨net,net_eval,net_rational,net_zero_biases⟩

#check @net_eval
#check @exists_network
#print axioms net_eval
#print axioms exists_network

end MaxCaterpillar.MaxFiveTenSix
