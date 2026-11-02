import MaxCaterpillar.Fiber.Count65.Paired.Absorption

/-! # Two physical continuous encodings of any affine feature readout

Signed opposite rows and coefficientwise positive/negative split rows both
encode the same affine function. The split rows are globally nonnegative on
natural ReLU features. These explicit encodings allow a changing baseline to
compensate a continuous offset contraction without leaving actual parameters.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier Absorption
variable {N m : ℕ}

lemma preact_positive_coefficients (A : Fin m → Point N) (β H : Fin m → ℝ)
    (η : ℝ) (x : Point N) :
    0≤preact A β (fun j => relu (H j)) (relu η) x := by
  exact add_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (relu_nonneg _) (relu_nonneg _)))
    (relu_nonneg _)

lemma preact_positive_parts_sub (A : Fin m → Point N) (β H : Fin m → ℝ)
    (η : ℝ) (x : Point N) :
    preact A β (fun j => relu (H j)) (relu η) x-
      preact A β (fun j => relu (-H j)) (relu (-η)) x=preact A β H η x := by
  calc
    _ = (∑ j, (relu (H j)-relu (-H j))*relu ((∑ i, A j i*x i)+β j))+
        (relu η-relu (-η)) := by
      simp only [preact,sub_mul,Finset.sum_sub_distrib]
      ring
    _ = _ := by simp only [relu_sub_relu_neg]; rfl

noncomputable def affineHeadRows (split : Bool) (H : Fin m → ℝ) : Fin 2 → Fin m → ℝ :=
  ![if split then (fun j => relu (H j)) else H,
    if split then (fun j => relu (-H j)) else (fun j => -H j)]

noncomputable def affineHeadBiases (split : Bool) (η : ℝ) : Fin 2 → ℝ :=
  ![if split then relu η else η,if split then relu (-η) else -η]

noncomputable def affineHeadNet (A : Fin m → Point N) (β H : Fin m → ℝ)
    (η : ℝ) (split : Bool) : Network N m 2 where
  W₁ := A
  b₁ := β
  W₂ := affineHeadRows split H
  b₂ := affineHeadBiases split η
  w₃ := ![1,-1]
  b₃ := 0

theorem affineHeadNet_eval (A : Fin m → Point N) (β H : Fin m → ℝ)
    (η : ℝ) (split : Bool) (x : Point N) :
    (affineHeadNet A β H η split).eval x=preact A β H η x := by
  cases split <;>
    simp only [Network.eval,affineHeadNet,affineHeadRows,affineHeadBiases,
      Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.head_cons,Matrix.tail_cons,if_true,if_false,one_mul,add_zero]
  · change relu (preact A β H η x)+(-1)*relu (preact A β (fun j => -H j) (-η) x) = _
    rw [preact_neg]
    have hh := relu_sub_relu_neg (preact A β H η x)
    linarith only [hh]
  · change relu (preact A β (fun j => relu (H j)) (relu η) x)+
      (-1)*relu (preact A β (fun j => relu (-H j)) (relu (-η)) x) = _
    rw [relu_of_nonneg (preact_positive_coefficients A β H η x),
      relu_of_nonneg (preact_positive_coefficients A β (fun j => -H j) (-η) x)]
    have hh := preact_positive_parts_sub A β H η x
    linarith only [hh]

theorem continuous_affineHeadNet {X : Type*} [TopologicalSpace X]
    (A : Fin m → Point N) (β : Fin m → ℝ) (H : X → Fin m → ℝ) (η : X → ℝ)
    (hH : Continuous H) (hη : Continuous η) (split : Bool) :
    Continuous (fun t => affineHeadNet A β (H t) (η t) split) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const,continuous_const,?_,?_,continuous_const,continuous_const⟩
  · apply continuous_pi
    intro k
    apply continuous_pi
    intro j
    have hj := (continuous_apply j).comp hH
    cases split <;> fin_cases k
    · change Continuous (fun t => H t j)
      exact hj
    · change Continuous (fun t => -H t j)
      exact hj.neg
    · change Continuous (fun t => relu (H t j))
      exact continuous_relu.comp hj
    · change Continuous (fun t => relu (-H t j))
      exact continuous_relu.comp hj.neg
  · apply continuous_pi
    intro k
    cases split <;> fin_cases k
    · change Continuous η
      exact hη
    · change Continuous (fun t => -η t)
      exact hη.neg
    · change Continuous (fun t => relu (η t))
      exact continuous_relu.comp hη
    · change Continuous (fun t => relu (-η t))
      exact continuous_relu.comp hη.neg

/-- Both blocks may vary continuously; all arrays are ordinary physical
parameters of the concatenated network. -/
theorem continuous_appendSpectators_varying {X : Type*} [TopologicalSpace X]
    {k r : ℕ} (f : X → Network N m k) (hf : Continuous f)
    (rows : X → Fin r → Fin m → ℝ) (biases weights : X → Fin r → ℝ)
    (hrows : Continuous rows) (hbiases : Continuous biases) (hweights : Continuous weights) :
    Continuous (fun t => appendSpectators (f t) (rows t) (biases t) (weights t)) := by
  apply (continuous_network_iff _).mpr
  rcases (continuous_network_iff f).mp hf with ⟨hA,hβ,hR,hυ,hc,hθ⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [appendSpectators] using hA
  · simpa only [appendSpectators] using hβ
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using (continuous_apply i).comp hR
    · simpa only [appendSpectators,Fin.append_right] using (continuous_apply i).comp hrows
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using (continuous_apply i).comp hυ
    · simpa only [appendSpectators,Fin.append_right] using (continuous_apply i).comp hbiases
  · apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [appendSpectators,Fin.append_left] using (continuous_apply i).comp hc
    · simpa only [appendSpectators,Fin.append_right] using (continuous_apply i).comp hweights
  · simpa only [appendSpectators] using hθ

end MaxCaterpillar.Fiber.Count65.Paired
