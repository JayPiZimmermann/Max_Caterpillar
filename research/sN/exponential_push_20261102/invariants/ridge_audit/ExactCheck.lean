import research.sN.exponential_push_20261102.ridge_annihilator.NoRidgeSum

set_option autoImplicit false
noncomputable section
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.ExponentialPush.Ridge

namespace IndependentRidgeAudit

/-- Expanded expected type: each completely arbitrary summand may choose
its own single non-diagonal period. The conclusion supplies a real input
where the proposed exact affine-plus-sum representation fails. -/
theorem actual_input_witness {N : ℕ} [NeZero N] {J : Type} [Fintype J]
    (hN : 2 ≤ N) (f : J → Point N → ℝ)
    (hf : ∀ k, ∃ v : Point N, (∃ i j, v i ≠ v j) ∧
      ∀ x, f k (x + v) = f k x)
    (a : Point N →+ ℝ) (c : ℝ) :
    ∃ x : Point N, Maximum N x ≠ a x + c + ∑ k, f k x := by
  exact not_forall.mp (maximum_ne_affine_sum_of_exists_periods hN f hf a c)

/-- The diagonal exclusion is necessary: one diagonal-invariant residual
and a true linear remainder already give the exact maximum. -/
theorem diagonal_period_countercontrol {N : ℕ} [NeZero N] (j : Fin N) :
    let f : Point N → ℝ := fun x => Maximum N x - x j
    (∀ x, f (x + diag 1) = f x) ∧
      (∀ x, Maximum N x = x j + f x) := by
  dsimp only
  constructor
  · intro x
    rw [Maximum_add_diag]
    simp only [Pi.add_apply, diag]
    ring
  · intro x
    ring

/-- The input-arity-two threshold is substantive. -/
theorem one_input_countercontrol (x : Point 1) : Maximum 1 x = x 0 := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using le_refl (x 0)
  · exact le_Maximum x 0

/-- The support notion in the actual proof is only a contrast bound. It
does not quietly assume continuity, compactness or diagonal invariance. -/
example {ι : Type} (f : (ι → ℝ) → ℝ) : ContrastBounded f ↔
    ∀ i j, ∃ R : ℝ, ∀ x, R < |x i - x j| → f x = 0 := Iff.rfl

#check @actual_input_witness
#print axioms actual_input_witness
#print axioms diagonal_period_countercontrol
#print axioms one_input_countercontrol
end IndependentRidgeAudit
