import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # A spare physical slot joins signed and split quadrant encodings

The first hidden layer and all appended spectators are arbitrary and fixed.
The third slot starts with zero output. At the split endpoint the second slot
is dormant, including along the boundary where its preactivation is zero.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators Absorption Frontier

variable {N m s : ℕ}

noncomputable def signedSplitNet (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ t : ℝ) : Network N m 3 where
  W₁ := A
  b₁ := β
  W₂ := ![fun j => Q j+(t-1)*R j,fun j => -(Q j+(t-1)*R j),R]
  b₂ := ![q+(t-1)*r,-(q+(t-1)*r),r]
  w₃ := ![1,-1,-t]
  b₃ := θ

theorem signedSplitNet_eval (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ t : ℝ) (hR : ∀ x, 0 ≤ preact A β R r x) (x : Point N) :
    (signedSplitNet A β Q R q r θ t).eval x =
      preact A β Q q x-preact A β R r x+θ := by
  simp only [Network.eval,signedSplitNet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Matrix.head_cons,
    Matrix.tail_cons,Matrix.cons_val_two,one_mul,neg_one_mul,zero_mul,add_zero,
    zero_add,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  change relu (preact A β (fun j => Q j+(t-1)*R j) (q+(t-1)*r) x)+
    (-relu (preact A β (fun j => -(Q j+(t-1)*R j)) (-(q+(t-1)*r)) x)+
      (-t)*relu (preact A β R r x))+θ = _
  rw [preact_neg,preact_addmul]
  have h := relu_sub_relu_neg (preact A β Q q x+(t-1)*preact A β R r x)
  rw [relu_of_nonneg (hR x)]
  linarith only [h]

theorem continuous_signedSplitNet (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ : ℝ) : Continuous (signedSplitNet A β Q R q r θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,?_,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> simp only [signedSplitNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [signedSplitNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [signedSplitNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity

theorem signedSplitNet_endpoint (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ : ℝ) :
    (signedSplitNet A β Q R q r θ 1).W₂ 0 = Q ∧
    (signedSplitNet A β Q R q r θ 1).b₂ 0 = q ∧
    (signedSplitNet A β Q R q r θ 1).W₂ 1 = -Q ∧
    (signedSplitNet A β Q R q r θ 1).b₂ 1 = -q ∧
    (signedSplitNet A β Q R q r θ 1).W₂ 2 = R ∧
    (signedSplitNet A β Q R q r θ 1).b₂ 2 = r ∧
    (signedSplitNet A β Q R q r θ 0).w₃ 2 = 0 := by
  simp [signedSplitNet]
  rfl

theorem signedSplitNet_endpoint_dormant (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ : ℝ) (hQ : ∀ x, 0 ≤ preact A β Q q x) (x : Point N) :
    relu (preact A β ((signedSplitNet A β Q R q r θ 1).W₂ 1)
      ((signedSplitNet A β Q R q r θ 1).b₂ 1) x) = 0 := by
  simp only [signedSplitNet,Matrix.cons_val_one,Matrix.head_cons,
    sub_self,zero_mul,add_zero]
  rw [preact_neg,relu_of_nonpos (neg_nonpos.mpr (hQ x))]

noncomputable def signedSplitWithSpectators (A : Fin m → Point N) (β Q R : Fin m → ℝ)
    (q r θ : ℝ) (rows : Fin s → Fin m → ℝ) (biases weights : Fin s → ℝ)
    (t : ℝ) : Network N m (3+s) :=
  appendSpectators (signedSplitNet A β Q R q r θ t) rows biases weights

theorem signedSplitWithSpectators_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β Q R : Fin m → ℝ) (q r θ : ℝ)
    (rows : Fin s → Fin m → ℝ) (biases weights : Fin s → ℝ)
    (hR : ∀ x, 0 ≤ preact A β R r x)
    (hsource : ∀ x, (signedSplitWithSpectators A β Q R q r θ rows biases weights 0).eval x =
      Maximum N x) :
    JoinedIn (ExactSet N m (3+s))
      (signedSplitWithSpectators A β Q R q r θ rows biases weights 0)
      (signedSplitWithSpectators A β Q R q r θ rows biases weights 1) := by
  apply JoinedIn.ofLine
    (continuous_appendSpectators (signedSplitNet A β Q R q r θ)
      (continuous_signedSplitNet A β Q R q r θ) rows biases weights).continuousOn rfl rfl
  rintro _ ⟨t,_ht,rfl⟩ x
  have h := hsource x
  simp only [signedSplitWithSpectators,appendSpectators_eval] at h ⊢
  rw [signedSplitNet_eval A β Q R q r θ t hR x,
    signedSplitNet_eval A β Q R q r θ 0 hR x] at *
  exact h

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
