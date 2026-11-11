import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Vary comparator orientations through a signed affine baseline

The parameter s may be any real number. Two opposite comparison gates with
outputs 1-s and s, together with a signed baseline pair, compute the same
function for every s. Arbitrary spectator neurons and every first parameter
remain fixed. Setting s=0 frees one comparison slot in the actual network.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption
variable {N m r : ℕ}

noncomputable def comparatorBaselineNet (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ s : ℝ) : Network N m 4 where
  W₁ := A
  b₁ := β
  W₂ := ![D,fun j => -D j,fun j => B j+s*D j,fun j => -(B j+s*D j)]
  b₂ := ![δ,-δ,η+s*δ,-(η+s*δ)]
  w₃ := ![1-s,s,1,-1]
  b₃ := θ

lemma comparatorBaselineNet_eval (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ s : ℝ) (x : Point N) :
    (comparatorBaselineNet A β D B δ η θ s).eval x=
      relu (preact A β D δ x)+preact A β B η x+θ := by
  simp only [Network.eval,comparatorBaselineNet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
    one_mul,neg_one_mul,add_zero]
  change (1-s)*relu (preact A β D δ x)+
    (s*relu (preact A β (fun j => -D j) (-δ) x)+
      (relu (preact A β (fun j => B j+s*D j) (η+s*δ) x)-
        relu (preact A β (fun j => -(B j+s*D j)) (-(η+s*δ)) x)))+θ = _
  rw [preact_neg,preact_neg]
  simp only [preact_addmul]
  change (1-s)*relu (preact A β D δ x)+
    (s*relu (-preact A β D δ x)+
      (relu (preact A β B η x+s*preact A β D δ x)-
        relu (-(preact A β B η x+s*preact A β D δ x))))+θ = _
  have hD := relu_sub_relu_neg (preact A β D δ x)
  have hB := relu_sub_relu_neg (preact A β B η x+s*preact A β D δ x)
  linear_combination hB - s*hD

theorem continuous_comparatorBaselineNet (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ : ℝ) :
    Continuous (comparatorBaselineNet A β D B δ η θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,?_,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> simp only [comparatorBaselineNet,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [comparatorBaselineNet,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [comparatorBaselineNet,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity

noncomputable def comparatorWithSpectators (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ : ℝ)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) (s : ℝ) :
    Network N m (4+r) :=
  appendSpectators (comparatorBaselineNet A β D B δ η θ s) rows biases weights

lemma comparatorWithSpectators_eval (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ : ℝ)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (s z : ℝ) (x : Point N) :
    (comparatorWithSpectators A β D B δ η θ rows biases weights s).eval x=
      (comparatorWithSpectators A β D B δ η θ rows biases weights z).eval x := by
  simp only [comparatorWithSpectators,appendSpectators_eval,comparatorBaselineNet_eval]
  rfl

/-- A concrete coefficient path removes the opposite comparison orientation,
while preserving arbitrary unchanged spectators and all real biases. -/
theorem comparatorWithSpectators_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β D B : Fin m → ℝ) (δ η θ : ℝ)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) (s z : ℝ)
    (hsource : ∀ x,
      (comparatorWithSpectators A β D B δ η θ rows biases weights s).eval x=Maximum N x) :
    JoinedIn (ExactSet N m (4+r))
      (comparatorWithSpectators A β D B δ η θ rows biases weights s)
      (comparatorWithSpectators A β D B δ η θ rows biases weights z) := by
  have hc := continuous_appendSpectators (comparatorBaselineNet A β D B δ η θ)
    (continuous_comparatorBaselineNet A β D B δ η θ) rows biases weights
  have hi : Continuous (fun t : ℝ => (1-t)*s+t*z) := by continuity
  apply JoinedIn.ofLine (hc.comp hi).continuousOn
  · simp [Function.comp_def,comparatorWithSpectators]
  · simp [Function.comp_def,comparatorWithSpectators]
  · rintro _ ⟨t,_,rfl⟩ x
    change (comparatorWithSpectators A β D B δ η θ rows biases weights
      ((1-t)*s+t*z)).eval x=Maximum N x
    rw [comparatorWithSpectators_eval A β D B δ η θ rows biases weights _ s x]
    exact hsource x

lemma comparatorBaselineNet_zero_unused (A : Fin m → Point N)
    (β D B : Fin m → ℝ) (δ η θ : ℝ) :
    (comparatorBaselineNet A β D B δ η θ 0).w₃ 1=0 := rfl

end MaxCaterpillar.Fiber.Count65.Paired
