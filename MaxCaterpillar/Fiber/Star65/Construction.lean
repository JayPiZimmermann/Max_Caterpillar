import MaxCaterpillar.Fiber.Star65.Residual
import MaxCaterpillar.Frontier.Constructions

/-! # Physical width-(6,5) positive-path Max4 networks

Both complete real-parameter residual families are compiled into the original
six-array network model. The construction includes `r = 1`. These existence
theorems do not assert completeness of the network fiber.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Star65

open BigOperators MaxCaterpillar.Frontier

private lemma vec_four_last (a b c d : ℝ) : (![a,b,c,d] : Fin 4 → ℝ) 3 = d := rfl

noncomputable def featureLin (C : Fin 4 → ℝ) (r q b c : ℝ) : ℝ :=
  C 0 * relu q + C 1 * relu b + C 2 * relu c + C 3 * relu (q + r * b)

/-- Four invariant features and the two signed parts of the translation coordinate. -/
noncomputable def firstRows (r : ℝ) : Fin 6 → Fin 4 → ℝ :=
  ![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, -1, 1],
    ![1, r - 1, -r, 0], ![0, 0, 1, 0], ![0, 0, -1, 0]]

noncomputable def firstValues (r : ℝ) (x : Point 4) : Fin 6 → ℝ :=
  ![relu (x 0 - x 1), relu (x 1 - x 2), relu (x 3 - x 2),
    relu ((x 0 - x 1) + r * (x 1 - x 2)), relu (x 2), relu (-x 2)]

theorem firstRows_eval (r : ℝ) (x : Point 4) (j : Fin 6) :
    relu (∑ i, firstRows r j i * x i) = firstValues r x j := by
  fin_cases j <;>
    simp only [firstRows, firstValues, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, one_mul, zero_mul, neg_mul, add_zero, zero_add]
  all_goals congr 1 <;> ring
  all_goals rfl

/-- Signed reconstruction of the translation plus the feature-linear remainder. -/
noncomputable def signedLift (r : ℝ) (L P Q N : Fin 4 → ℝ) : Network 4 6 5 where
  W₁ := firstRows r
  b₁ := 0
  W₂ := ![![L 0, L 1, L 2, L 3, 1, -1],
    ![-L 0, -L 1, -L 2, -L 3, -1, 1],
    ![P 0, P 1, P 2, P 3, 0, 0],
    ![Q 0, Q 1, Q 2, Q 3, 0, 0],
    ![N 0, N 1, N 2, N 3, 0, 0]]
  b₂ := 0
  w₃ := ![1, -1, 1, 1, -1]
  b₃ := 0

theorem signedLift_eval (r : ℝ) (L P Q N : Fin 4 → ℝ) (x : Point 4) :
    (signedLift r L P Q N).eval x = x 2 +
      featureLin L r (x 0 - x 1) (x 1 - x 2) (x 3 - x 2) +
      relu (featureLin P r (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) +
      relu (featureLin Q r (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) -
      relu (featureLin N r (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) := by
  simp only [Network.eval, signedLift, Pi.zero_apply, add_zero]
  simp_rw [firstRows_eval]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, firstValues, one_mul, zero_mul, neg_mul, add_zero, zero_add]
  simp only [featureLin]
  have hp := relu_sub_relu_neg (x 2)
  have hh := relu_sub_relu_neg
    (L 0 * relu (x 0 - x 1) + L 1 * relu (x 1 - x 2) +
      L 2 * relu (x 3 - x 2) + L 3 * relu ((x 0 - x 1) + r * (x 1 - x 2)) +
      (relu (x 2) - relu (-x 2)))
  ring_nf at hh ⊢
  linarith only [hh, hp]

theorem signedLift_hasZeroBiases (r : ℝ) (L P Q N : Fin 4 → ℝ) :
    (signedLift r L P Q N).HasZeroBiases := ⟨rfl, rfl, rfl⟩

noncomputable def branchINet (r k : ℝ) : Network 4 6 5 :=
  signedLift r ![0, 0, 1, 0] ![-(1-r)/r, 0, -1, 1/r]
    ![k, 1, -1, 0] ![-(1-r)/r - 1 + k, 0, -1, 1/r]

noncomputable def branchIINet (r h : ℝ) : Network 4 6 5 :=
  signedLift r ![0, 0, 1, 0] ![-(1-r)/r, h, -1, 1/r]
    ![1, 1, -1, 0] ![1, 1+h, -1, 0]

private theorem target_shift (x : Point 4) :
    x 2 + max (max 0 ((x 0 - x 1) + (x 1 - x 2)))
      (max (x 1 - x 2) (x 3 - x 2)) = Maximum 4 x := by
  calc
    _ = max (max (x 2) (x 0)) (max (x 1) (x 3)) := by
      rw [← max_add_add_left, ← max_add_add_left, ← max_add_add_left]
      congr 2 <;> ring
    _ = Maximum 4 x := by
      rw [Maximum_four]
      ac_rfl

private theorem branchINet_reduced (r k : ℝ) (x : Point 4) :
    (branchINet r k).eval x = x 2 +
      branchI r k (x 0 - x 1) (x 1 - x 2) (x 3 - x 2) := by
  rw [branchINet, signedLift_eval]
  simp only [featureLin, branchI, vec_four_last, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.tail_cons, one_mul, zero_mul, neg_mul, zero_add, add_zero]
  unfold comparison relu
  simp only [div_eq_mul_inv]
  ring_nf

private theorem branchIINet_reduced (r h : ℝ) (x : Point 4) :
    (branchIINet r h).eval x = x 2 +
      branchII r h (x 0 - x 1) (x 1 - x 2) (x 3 - x 2) := by
  rw [branchIINet, signedLift_eval]
  simp only [featureLin, branchII, vec_four_last, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.tail_cons, one_mul, zero_mul, neg_mul, zero_add, add_zero]
  unfold comparison relu
  simp only [div_eq_mul_inv]
  ring_nf

/-- Every real parameter in the first branch gives an exact physical Max4 network. -/
theorem branchINet_eval {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : k ≤ 0)
    (x : Point 4) : (branchINet r k).eval x = Maximum 4 x := by
  rw [branchINet_reduced, branchI_eq_max hr hr1 hk, target_shift]

/-- Every real parameter in the second branch gives an exact physical Max4 network. -/
theorem branchIINet_eval {r h : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hh : h ≤ -1)
    (x : Point 4) : (branchIINet r h).eval x = Maximum 4 x := by
  rw [branchIINet_reduced, branchII_eq_max hr hr1 hh, target_shift]

end MaxCaterpillar.Fiber.Star65
