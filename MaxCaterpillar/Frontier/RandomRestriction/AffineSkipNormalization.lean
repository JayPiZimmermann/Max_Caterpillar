import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization.Homogeneous

/-! # Faithful normalization of arbitrary affine-skip MAX networks

The original first and second hidden indices are preserved. A first row is
retained with its exact original coefficients precisely when its bias and
coordinate sum both vanish; every remaining first-to-second feeding index
comes from an original nonzero first-to-second coefficient.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
open BigOperators
open NormalizedNetwork
variable {N h₁ h₂ : ℕ}

lemma lift_identity (x : Point N) : lift (Function.Embedding.refl (Fin N)) x=x := by
  ext i
  exact lift_selected (Function.Embedding.refl (Fin N)) x i

/-- The all-ones directional model for an arbitrary homogeneous indexed
skip model. This operation never adds, identifies, or rescales a neuron. -/
noncomputable def diagonalModel (net : NormalizedNetwork N h₁ h₂) :
    NormalizedNetwork N h₁ h₂ :=
  net.localize (diag 1) (Function.Embedding.refl (Fin N))

theorem diagonalModel_first_row (net : NormalizedNetwork N h₁ h₂) (j : Fin h₁) :
    (diagonalModel net).A j=if (∑ i,net.A j i)=0 then net.A j else 0 := by
  rw [diagonalModel,localize_first_row,lin_diag,one_mul]
  rfl

lemma diagonalModel_first_zero_sum (net : NormalizedNetwork N h₁ h₂) :
    ∀ j,∑ i,(diagonalModel net).A j i=0 := by
  classical
  intro j
  rw [diagonalModel_first_row]
  split_ifs with h
  · exact h
  · simp

theorem diagonalModel_feeding_original (net : NormalizedNetwork N h₁ h₂)
    (j : Fin h₁) (hj : (diagonalModel net).Feeding j) : net.Feeding j :=
  net.localize_feeding_original _ _ j hj

theorem diagonalModel_computes_max [NeZero N] (net : NormalizedNetwork N h₁ h₂)
    (hnet : ∀ x,net.eval x=Maximum N x) :
    ∀ x,(diagonalModel net).eval x=Maximum N x := by
  intro x
  obtain ⟨ε,hε,he⟩ := net.exists_eval_direction (diag 1)
    (Function.Embedding.refl (Fin N)) x
  rw [lift_identity,hnet,hnet,Maximum_diag] at he
  have hm : Maximum N (diag 1+ε • x)=1+ε*Maximum N x := by
    rw [add_comm,Maximum_add_diag,Maximum_smul hε]
    ring
  rw [hm] at he
  have hd : net.directionalEval (diag 1) (Function.Embedding.refl (Fin N)) x=Maximum N x := by
    apply mul_left_cancel₀ hε.ne'
    linarith only [he]
  rw [diagonalModel,localize_eval,hd]

/-- The actual normalized model associated to the nine unrestricted real
parameter arrays; neither hidden-layer width changes. -/
noncomputable def normalizedModel (net : AffineSkipNetwork N h₁ h₂) :
    NormalizedNetwork N h₁ h₂ :=
  normalizeOuter (diagonalModel (homogeneousModel net))

theorem normalizedModel_computes_max [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,eval net x=Maximum N x) :
    ∀ x,(normalizedModel net).eval x=Maximum N x :=
  normalizeOuter_computes_max _ (diagonalModel_first_zero_sum _)
    (diagonalModel_computes_max _ (homogeneousModel_computes_max net hnet))

theorem normalizedModel_translation_normalized [NeZero N]
    (net : AffineSkipNetwork N h₁ h₂) (hnet : ∀ x,eval net x=Maximum N x) :
    (normalizedModel net).TranslationNormalized :=
  normalizeOuter_translation_normalized _ (diagonalModel_first_zero_sum _)
    (diagonalModel_computes_max _ (homogeneousModel_computes_max net hnet))

/-- Exact coefficient lineage, including arbitrary nonzero original biases. -/
theorem normalizedModel_first_row (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁) :
    (normalizedModel net).A j=
      if net.b j=0 ∧ (∑ i,net.A j i)=0 then net.A j else 0 := by
  classical
  rw [normalizedModel,normalizeOuter_first_row,diagonalModel_first_row,
    homogeneousModel_first_row]
  by_cases hb : net.b j=0
  · simp [hb]
  · simp [hb]

theorem normalizedModel_feeding_original (net : AffineSkipNetwork N h₁ h₂)
    (j : Fin h₁) (hj : (normalizedModel net).Feeding j) : ∃ k,net.W k j≠0 :=
  homogeneousModel_feeding_original net j
    (diagonalModel_feeding_original _ j (normalizeOuter_feeding_original _ j hj))

/-- An actual affine-skip MAX identity yields a faithful normalized model,
without a normal-form, support, weight, bias, or width hypothesis. -/
theorem exists_normalizedModel [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x,eval net x=Maximum N x) :
    ∃ model : NormalizedNetwork N h₁ h₂,
      (∀ x,model.eval x=Maximum N x) ∧ model.TranslationNormalized ∧
      (∀ j,model.A j=if net.b j=0 ∧ (∑ i,net.A j i)=0 then net.A j else 0) ∧
      (∀ j,model.Feeding j→∃ k,net.W k j≠0) :=
  ⟨normalizedModel net,normalizedModel_computes_max net hnet,
    normalizedModel_translation_normalized net hnet,
    normalizedModel_first_row net,normalizedModel_feeding_original net⟩

#check @exists_normalizedModel
#print axioms normalizedModel_computes_max
#print axioms normalizedModel_translation_normalized
#print axioms normalizedModel_first_row
#print axioms normalizedModel_feeding_original
#print axioms exists_normalizedModel
end MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension
