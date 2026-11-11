import research.sN.exponential_push_20261102.ridge_annihilator.NoRidgeSum

/-! Exact public-type consumers and boundary controls. -/
set_option autoImplicit false
noncomputable section
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.ExponentialPush.Ridge

/-- An ordinary real affine remainder, arbitrary real summands, and actual
all-real maximum. The dimension lower bound derives the nonempty-input instance. -/
example {N : ℕ} (hN : 2 ≤ N) {J : Type*} [Fintype J]
    (f : J → (Fin N → ℝ) → ℝ)
    (hf : ∀ k, ∃ v : Fin N → ℝ, (∃ i j, v i ≠ v j) ∧
      ∀ x : Fin N → ℝ, f k (x + v) = f k x)
    (a : (Fin N → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) :
    letI : NeZero N := ⟨by omega⟩
    ¬ ∀ x : Fin N → ℝ, Maximum N x = a x + c + ∑ k, f k x := by
  letI : NeZero N := ⟨by omega⟩
  exact maximum_ne_affine_sum_of_exists_periods hN f hf a.toAddMonoidHom c

/-- Exact nonzero all-coordinate difference and support bound in every arity. -/
example {N : ℕ} [NeZero N] :
    maxCoordinateDifference (0 : Point N) ≠ 0 ∧
      ∀ x : Point N, ∀ i j, 1 ≤ |x i - x j| → maxCoordinateDifference x = 0 := by
  exact ⟨maxCoordinateDifference_ne_zero, maxCoordinateDifference_eq_zero_of_abs_contrast⟩

/-- The hypotheses on an individual summand are satisfiable. -/
example : ∃ f : Point 3 → ℝ, ∃ v : Point 3,
    (∃ i j, v i ≠ v j) ∧ ∀ x, f (x + v) = f x := by
  refine ⟨fun _ => 0, unitVec 0, ⟨0, 1, ?_⟩, ?_⟩
  · norm_num [unitVec]
  · intro x
    rfl

/-- Non-diagonality is essential: the maximum minus one coordinate has a
diagonal period and, together with that affine coordinate, represents MAX3. -/
example : ∃ f : Point 3 → ℝ,
    (∀ x, f (x + diag 1) = f x) ∧
    (∀ x, Maximum 3 x = x 2 + f x) := by
  refine ⟨fun x => Maximum 3 x - x 2, ?_, ?_⟩
  · intro x
    dsimp only
    rw [Maximum_add_diag]
    simp only [Pi.add_apply, diag]
    ring
  · intro x
    ring

/-- Arity one is affine, so the N≥2 restriction in the affine-sum theorem
cannot simply be removed. -/
example (x : Point 1) : Maximum 1 x = x 0 := by
  apply Maximum_eq_of
  · rfl
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    simp [hi]

#check @contrastBounded_periodic_eq_zero
#check @iterDiff_eq_zero_iff_of_contrastBounded
#check @maxCoordinateDifference_eq_tent
#check @iterDiff_maximum_ne_zero
#check @maximum_ne_affine_sum_of_exists_periods
#print axioms contrastBounded_periodic_eq_zero
#print axioms iterDiff_eq_zero_iff_of_contrastBounded
#print axioms maxCoordinateDifference_eq_tent
#print axioms iterDiff_maximum_ne_zero
#print axioms maximum_ne_affine_sum_of_exists_periods
