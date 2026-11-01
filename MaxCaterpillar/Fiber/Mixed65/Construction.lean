import MaxCaterpillar.Fiber.Mixed65.Residual
import MaxCaterpillar.Frontier.Constructions

/-! # Actual width-(6,5) networks from mixed residual identities

This file supplies nonvacuity witnesses in the original six-array network
model. It is not a completeness or connected-component theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

@[simp] private lemma vecFour_three (a b c d : ℝ) : ![a, b, c, d] (3 : Fin 4) = d := rfl

/-- A linear form in the four invariant first hidden layer features. -/
noncomputable def featureLin (C : Fin 4 → ℝ) (t q b c : ℝ) : ℝ :=
  C 0 * relu q + C 1 * relu b + C 2 * relu c + C 3 * relu (t * q - b)

/-- The mixed first hidden layer, with the translation coordinate carried by
its positive and negative parts. -/
noncomputable def firstRows (t : ℝ) : Fin 6 → Fin 4 → ℝ :=
  ![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, -1, 1],
    ![t, -(t + 1), 1, 0], ![0, 0, 1, 0], ![0, 0, -1, 0]]

noncomputable def firstValues (t : ℝ) (x : Point 4) : Fin 6 → ℝ :=
  ![relu (x 0 - x 1), relu (x 1 - x 2), relu (x 3 - x 2),
    relu (t * (x 0 - x 1) - (x 1 - x 2)), relu (x 2), relu (-x 2)]

theorem firstRows_eval (t : ℝ) (x : Point 4) (j : Fin 6) :
    relu (∑ i, firstRows t j i * x i) = firstValues t x j := by
  fin_cases j <;> norm_num [firstRows, firstValues, Fin.sum_univ_succ] <;>
    try simp only [show (Fin.succ 2 : Fin 4) = 3 from rfl]
  all_goals congr 1 <;> ring

/-- A physical five-neuron signed lift of three invariant residual gates. -/
noncomputable def signedLift (t : ℝ) (L R S D : Fin 4 → ℝ) : Network 4 6 5 where
  W₁ := firstRows t
  b₁ := 0
  W₂ := ![![L 0, L 1, L 2, L 3, 1, -1],
    ![-L 0, -L 1, -L 2, -L 3, -1, 1],
    ![R 0, R 1, R 2, R 3, 0, 0],
    ![S 0, S 1, S 2, S 3, 0, 0],
    ![D 0, D 1, D 2, D 3, 0, 0]]
  b₂ := 0
  w₃ := ![1, -1, 1, 1, -1]
  b₃ := 0

theorem signedLift_eval (t : ℝ) (L R S D : Fin 4 → ℝ) (x : Point 4) :
    (signedLift t L R S D).eval x = x 2 +
      featureLin L t (x 0 - x 1) (x 1 - x 2) (x 3 - x 2) +
      relu (featureLin R t (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) +
      relu (featureLin S t (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) -
      relu (featureLin D t (x 0 - x 1) (x 1 - x 2) (x 3 - x 2)) := by
  simp only [Network.eval, signedLift, Pi.zero_apply, add_zero]
  simp_rw [firstRows_eval]
  norm_num [Fin.sum_univ_succ, firstValues, featureLin]
  have hp := relu_sub_relu_neg (x 2)
  have hh := relu_sub_relu_neg
    (L 0 * relu (x 0 - x 1) + L 1 * relu (x 1 - x 2) +
      L 2 * relu (x 3 - x 2) + L 3 * relu (t * (x 0 - x 1) - (x 1 - x 2)) +
      (relu (x 2) - relu (-x 2)))
  ring_nf at hh ⊢
  linarith only [hh, hp]

theorem signedLift_hasZeroBiases (t : ℝ) (L R S D : Fin 4 → ℝ) :
    (signedLift t L R S D).HasZeroBiases := ⟨rfl, rfl, rfl⟩

noncomputable def branchANet (t k : ℝ) : Network 4 6 5 :=
  signedLift t ![1, 1, 0, 0] ![-(1 + t), 0, 1, 1]
    ![-1, -1, 1, k] ![-(1 + t), 0, 1, k + 1]

noncomputable def branchBNet (t r : ℝ) : Network 4 6 5 :=
  signedLift t ![1 + t, 0, 0, -1] ![-(1 + t), r, 1, 1]
    ![-1, -1, 1, 0] ![-1, r - 1, 1, 0]

private theorem target_shift (x : Point 4) :
    x 2 + max (max ((x 0 - x 1) + (x 1 - x 2)) (x 1 - x 2))
      (relu (x 3 - x 2)) = Maximum 4 x := by
  rw [Maximum_four]
  unfold relu
  rw [← max_add_add_left, ← max_add_add_left, ← max_add_add_left]
  congr 2 <;> ring

/-- The first complete real-parameter mixed family computes Max4 on every input. -/
theorem branchANet_eval (t k : ℝ) (ht : 0 < t) (hk : 1 ≤ t * k) (x : Point 4) :
    (branchANet t k).eval x = Maximum 4 x := by
  rw [branchANet, signedLift_eval]
  norm_num [featureLin]
  have h := residualA t k (x 0 - x 1) (x 1 - x 2) (relu (x 3 - x 2)) ht hk
    (relu_nonneg _)
  have hs := target_shift x
  ring_nf at h hs ⊢
  linarith only [h, hs]

/-- The second complete real-parameter mixed family computes Max4 on every input. -/
theorem branchBNet_eval (t r : ℝ) (ht : 0 < t) (hr : 1 + t ≤ t * r) (x : Point 4) :
    (branchBNet t r).eval x = Maximum 4 x := by
  rw [branchBNet, signedLift_eval]
  norm_num [featureLin]
  have h := residualB t r (x 0 - x 1) (x 1 - x 2) (relu (x 3 - x 2)) ht hr
    (relu_nonneg _)
  have hs := target_shift x
  ring_nf at h hs ⊢
  linarith only [h, hs]

end MaxCaterpillar.Fiber.Mixed65
