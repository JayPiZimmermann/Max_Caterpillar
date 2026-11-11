import MaxCaterpillar.Fiber.Connected64.OutputMoves
import MaxCaterpillar.Frontier.Basic

/-! # Bias-aware physical absorption paths for signed pairs

The first matrix and its biases are arbitrary and fixed. A signed second-layer
pair carries an affine function. A globally nonnegative second preactivation,
or another signed pair, can be absorbed into that carrier by a continuous path
of the actual physical parameters, preserving the function on every real input.
These are deformation lemmas, not a classification of all paired completions.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.Absorption
open BigOperators Frontier unitInterval

variable {N m : ℕ}

/-- Evaluation of a second affine preactivation after arbitrary first features. -/
noncomputable def preact (A : Fin m → Point N) (β : Fin m → ℝ)
    (row : Fin m → ℝ) (bias : ℝ) (x : Point N) : ℝ :=
  (∑ j, row j * relu ((∑ i, A j i * x i) + β j)) + bias

lemma preact_neg (A : Fin m → Point N) (β row : Fin m → ℝ) (bias : ℝ) (x : Point N) :
    preact A β (fun j => -row j) (-bias) x = -preact A β row bias x := by
  simp only [preact, neg_mul, Finset.sum_neg_distrib]
  ring

lemma preact_smul (A : Fin m → Point N) (β row : Fin m → ℝ)
    (bias u : ℝ) (x : Point N) :
    preact A β (fun j => u*row j) (u*bias) x = u*preact A β row bias x := by
  simp only [preact, mul_assoc, ← Finset.mul_sum]
  ring

lemma preact_addmul (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π u : ℝ) (x : Point N) :
    preact A β (fun j => H j+u*P j) (η+u*π) x =
      preact A β H η x+u*preact A β P π x := by
  simp only [preact, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- A signed pair absorbs a third neuron whose preactivation is nonnegative. -/
noncomputable def pairPlusNet (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ t : ℝ) : Network N m 3 where
  W₁ := A
  b₁ := β
  W₂ := ![fun j => H j+t*d*P j, fun j => -(H j+t*d*P j), fun j => (1-t)*P j]
  b₂ := ![η+t*d*π, -(η+t*d*π), (1-t)*π]
  w₃ := ![1,-1,d]
  b₃ := θ

lemma pairPlus_formula (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ t : ℝ) (x : Point N) :
    (pairPlusNet A β H P η π d θ t).eval x =
      preact A β H η x+t*d*preact A β P π x+
        d*relu ((1-t)*preact A β P π x)+θ := by
  simp only [Network.eval, pairPlusNet, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, one_mul, neg_one_mul, zero_mul, add_zero, zero_add,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  change relu (preact A β (fun j => H j+t*d*P j) (η+t*d*π) x) +
    (-relu (preact A β (fun j => -(H j+t*d*P j)) (-(η+t*d*π)) x) +
      d*relu (preact A β (fun j => (1-t)*P j) ((1-t)*π) x)) + θ = _
  rw [preact_neg, preact_addmul, preact_smul]
  have h := relu_sub_relu_neg (preact A β H η x+t*d*preact A β P π x)
  linarith only [h]

/-- The function is unchanged throughout the physical absorption. The third
coefficient d may have either sign; positivity is needed only for its input. -/
theorem pairPlus_eval (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ t : ℝ) (ht : t ≤ 1)
    (hP : ∀ x, 0 ≤ preact A β P π x) (x : Point N) :
    (pairPlusNet A β H P η π d θ t).eval x =
      preact A β H η x+d*preact A β P π x+θ := by
  rw [pairPlus_formula, relu_of_nonneg (mul_nonneg (by linarith) (hP x))]
  ring

/-- Coordinatewise continuity in the ordinary physical parameter topology. -/
theorem continuous_pairPlusNet (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ : ℝ) : Continuous (pairPlusNet A β H P η π d θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> simp only [pairPlusNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [pairPlusNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity

/-- The absorbed third neuron has zero incoming row and zero bias. -/
theorem pairPlus_endpoint_unused (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ : ℝ) :
    (pairPlusNet A β H P η π d θ 1).W₂ 2 = 0 ∧
      (pairPlusNet A β H P η π d θ 1).b₂ 2 = 0 := by
  constructor
  · funext j
    simp [pairPlusNet]
  · simp [pairPlusNet]

/-- Two signed pairs can be consolidated without any positivity assumption. -/
noncomputable def pairPairNet (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ t : ℝ) : Network N m 4 where
  W₁ := A
  b₁ := β
  W₂ := ![fun j => H j+t*J j, fun j => -(H j+t*J j),
    fun j => (1-t)*J j, fun j => -((1-t)*J j)]
  b₂ := ![η+t*ι,-(η+t*ι),(1-t)*ι,-((1-t)*ι)]
  w₃ := ![1,-1,1,-1]
  b₃ := θ

/-- Signed-pair absorption is an identity for every real t, including all biases. -/
theorem pairPair_eval (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ t : ℝ) (x : Point N) :
    (pairPairNet A β H J η ι θ t).eval x = preact A β H η x+preact A β J ι x+θ := by
  simp only [Network.eval, pairPairNet, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.tail_cons, one_mul, neg_one_mul, zero_mul, add_zero, zero_add,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  change relu (preact A β (fun j => H j+t*J j) (η+t*ι) x) +
    (-relu (preact A β (fun j => -(H j+t*J j)) (-(η+t*ι)) x) +
      (relu (preact A β (fun j => (1-t)*J j) ((1-t)*ι) x) +
        -relu (preact A β (fun j => -((1-t)*J j)) (-((1-t)*ι)) x)))+θ = _
  rw [preact_neg,preact_neg,preact_addmul,preact_smul]
  have h := relu_sub_relu_neg (preact A β H η x+t*preact A β J ι x)
  have j := relu_sub_relu_neg ((1-t)*preact A β J ι x)
  nlinarith only [h,j]

theorem continuous_pairPairNet (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ : ℝ) : Continuous (pairPairNet A β H J η ι θ) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    fin_cases k <;> simp only [pairPairNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity
  · apply continuous_pi
    intro k
    fin_cases k <;> simp only [pairPairNet,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons] <;> continuity

/-- Both incoming rows and biases of the second pair vanish at the endpoint. -/
theorem pairPair_endpoint_unused (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ : ℝ) :
    (pairPairNet A β H J η ι θ 1).W₂ 2 = 0 ∧
    (pairPairNet A β H J η ι θ 1).b₂ 2 = 0 ∧
    (pairPairNet A β H J η ι θ 1).W₂ 3 = 0 ∧
    (pairPairNet A β H J η ι θ 1).b₂ 3 = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · funext j; simp [pairPairNet]
  · simp [pairPairNet]
  · funext j; simp [pairPairNet]; rfl
  · simp [pairPairNet]; rfl

/-- Append arbitrary unchanged second-neuron spectators to a physical block. -/
def appendSpectators {k r : ℕ} (a : Network N m k)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) : Network N m (k+r) where
  W₁ := a.W₁
  b₁ := a.b₁
  W₂ := Fin.append a.W₂ rows
  b₂ := Fin.append a.b₂ biases
  w₃ := Fin.append a.w₃ weights
  b₃ := a.b₃

lemma appendSpectators_eval {k r : ℕ} (a : Network N m k)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) (x : Point N) :
    (appendSpectators a rows biases weights).eval x = a.eval x+
      ∑ j, weights j*relu (preact a.W₁ a.b₁ (rows j) (biases j) x) := by
  simp only [Network.eval,appendSpectators,Fin.sum_univ_add,
    Fin.append_left,Fin.append_right,preact]
  ring

lemma continuous_appendSpectators {X : Type*} [TopologicalSpace X] {k r : ℕ}
    (f : X → Network N m k) (hf : Continuous f)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ) :
    Continuous (fun t => appendSpectators (f t) rows biases weights) := by
  apply (continuous_network_iff _).mpr
  rcases (continuous_network_iff f).mp hf with ⟨hA,hβ,hR,hυ,hc,hθ⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [appendSpectators] using hA
  · simpa only [appendSpectators] using hβ
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using
        (continuous_apply i).comp hR
    · simp only [appendSpectators,Fin.append_right]
      exact continuous_const
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using
        (continuous_apply i).comp hυ
    · simp only [appendSpectators,Fin.append_right]
      exact continuous_const
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using
        (continuous_apply i).comp hc
    · simp only [appendSpectators,Fin.append_right]
      exact continuous_const
  · simpa only [appendSpectators] using hθ

variable {r : ℕ}

/-- The absorption block inside an otherwise arbitrary physical second layer. -/
noncomputable def pairPlusWithSpectators (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ : ℝ) (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (t : ℝ) : Network N m (3+r) :=
  appendSpectators (pairPlusNet A β H P η π d θ t) rows biases weights

theorem pairPlusWithSpectators_preserves (A : Fin m → Point N) (β H P : Fin m → ℝ)
    (η π d θ : ℝ) (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (hP : ∀ x, 0 ≤ preact A β P π x) (t : ℝ) (ht : t ≤ 1) (x : Point N) :
    (pairPlusWithSpectators A β H P η π d θ rows biases weights t).eval x =
      (pairPlusWithSpectators A β H P η π d θ rows biases weights 0).eval x := by
  simp only [pairPlusWithSpectators,appendSpectators_eval]
  rw [pairPlus_eval A β H P η π d θ t ht hP x,
    pairPlus_eval A β H P η π d θ 0 (by norm_num) hP x]
  rfl

/-- Exact absorption in the full network fiber, with all other second neurons
untouched. The source exactness hypothesis allows arbitrary spectator gates. -/
theorem pairPlusWithSpectators_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β H P : Fin m → ℝ) (η π d θ : ℝ)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (hP : ∀ x, 0 ≤ preact A β P π x)
    (hsource : ∀ x,
      (pairPlusWithSpectators A β H P η π d θ rows biases weights 0).eval x = Maximum N x) :
    JoinedIn (ExactSet N m (3+r))
      (pairPlusWithSpectators A β H P η π d θ rows biases weights 0)
      (pairPlusWithSpectators A β H P η π d θ rows biases weights 1) := by
  have hc := continuous_appendSpectators (pairPlusNet A β H P η π d θ)
    (continuous_pairPlusNet A β H P η π d θ) rows biases weights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,ht,rfl⟩ x
  change (pairPlusWithSpectators A β H P η π d θ rows biases weights t).eval x = Maximum N x
  rw [pairPlusWithSpectators_preserves A β H P η π d θ rows biases weights hP t ht.2 x]
  exact hsource x

/-- Two signed pairs inside a larger arbitrary second layer. -/
noncomputable def pairPairWithSpectators (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ : ℝ) (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (t : ℝ) : Network N m (4+r) :=
  appendSpectators (pairPairNet A β H J η ι θ t) rows biases weights

theorem pairPairWithSpectators_preserves (A : Fin m → Point N) (β H J : Fin m → ℝ)
    (η ι θ : ℝ) (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (t : ℝ) (x : Point N) :
    (pairPairWithSpectators A β H J η ι θ rows biases weights t).eval x =
      (pairPairWithSpectators A β H J η ι θ rows biases weights 0).eval x := by
  simp only [pairPairWithSpectators,appendSpectators_eval,pairPair_eval]
  rfl

theorem pairPairWithSpectators_joinedIn_exact [NeZero N]
    (A : Fin m → Point N) (β H J : Fin m → ℝ) (η ι θ : ℝ)
    (rows : Fin r → Fin m → ℝ) (biases weights : Fin r → ℝ)
    (hsource : ∀ x,
      (pairPairWithSpectators A β H J η ι θ rows biases weights 0).eval x = Maximum N x) :
    JoinedIn (ExactSet N m (4+r))
      (pairPairWithSpectators A β H J η ι θ rows biases weights 0)
      (pairPairWithSpectators A β H J η ι θ rows biases weights 1) := by
  have hc := continuous_appendSpectators (pairPairNet A β H J η ι θ)
    (continuous_pairPairNet A β H J η ι θ) rows biases weights
  apply JoinedIn.ofLine hc.continuousOn rfl rfl
  rintro _ ⟨t,_,rfl⟩ x
  change (pairPairWithSpectators A β H J η ι θ rows biases weights t).eval x = Maximum N x
  rw [pairPairWithSpectators_preserves A β H J η ι θ rows biases weights t x]
  exact hsource x

/-- A zero second preactivation permits erasing its output coefficient. -/
theorem eraseZeroSecond_eval {k : ℕ} (a : Network N m k) (j : Fin k)
    (hrow : a.W₂ j = 0) (hbias : a.b₂ j = 0) (x : Point N) :
    (withOutput a (Function.update a.w₃ j 0) a.b₃).eval x = a.eval x := by
  unfold withOutput Network.eval
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    simp [hrow,hbias,relu]
  · simp [Function.update_noteq hi]

/-- The erasure is a straight path in actual output parameters, within the
full all-input exact fiber. It empties the slot without changing other rows. -/
noncomputable def eraseZeroSecondPath {k : ℕ} [NeZero N]
    (a : ExactFiber N m k) (j : Fin k)
    (hrow : a.val.W₂ j = 0) (hbias : a.val.b₂ j = 0) :
    Path a (⟨withOutput a.val (Function.update a.val.w₃ j 0) a.val.b₃,
      fun x => (eraseZeroSecond_eval a.val j hrow hbias x).trans (a.property x)⟩ :
      ExactFiber N m k) :=
  outputInterpolationPath a (Function.update a.val.w₃ j 0) a.val.b₃
    (fun x => (eraseZeroSecond_eval a.val j hrow hbias x).trans (a.property x))

end MaxCaterpillar.Fiber.Count65.Paired.Absorption
