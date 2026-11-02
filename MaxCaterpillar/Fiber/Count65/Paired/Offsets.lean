import MaxCaterpillar.Fiber.Count65.Paired.Support
import MaxCaterpillar.Fiber.Paired65.RecessionAtoms

/-!
# Four-atom balance and separable offset coefficients

The exact scalar ReLU identity supplies the atom balance. The algebraic
cross-sample lemma then supplies the common support alternative. Neither
statement presupposes a network deformation or component classification.
-/
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Signed atom balance on at most four nonzero-weight atoms allows one
nonzero offset value only. -/
theorem oneLevel_of_atomBalance (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (h : Paired65.AtomBalance j f)
    (hcard : Fintype.card ι ≤ 4) : OneLevel f := by
  intro a b
  by_cases ha : f a = 0
  · exact Or.inl ha
  · by_cases hb : f b = 0
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Paired65.atomBalance_nonzero_offsets_equal j f hj h hcard
        ha hb ⟨a, rfl⟩ ⟨b, rfl⟩))

/-- This bridge starts from the actual all-real hinge identity. -/
theorem oneLevel_of_four_relu_identity (j f : ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (hcard : Fintype.card ι ≤ 4)
    (h : ∀ t : ℝ, (∑ i, j i * relu (t-f i)) = relu t) :
    OneLevel f := by
  exact oneLevel_of_atomBalance j f hj
    (Paired65.atomBalance_of_relu_identity j f h) hcard

/-- Separable offsets in the two signed code coordinates. -/
noncomputable def separableOffsets (a b : Bool → ι → ℝ) (u v : ℝ) : ι → ℝ :=
  fun i => a true i * relu u + a false i * relu (-u) +
    b true i * relu v + b false i * relu (-v)

private def side (b : Bool) (t : ℝ) : ℝ := if b then t else -t

lemma separableOffsets_left_unit (a b : Bool → ι → ℝ) (k : Bool) :
    separableOffsets a b (side k 1) 0 = a k := by
  funext i
  cases k <;> norm_num [separableOffsets, side, relu]

lemma separableOffsets_right_unit (a b : Bool → ι → ℝ) (l : Bool) :
    separableOffsets a b 0 (side l 1) = b l := by
  funext i
  cases l <;> norm_num [separableOffsets, side, relu]

lemma separableOffsets_cross_unit (a b : Bool → ι → ℝ) (k l : Bool) :
    separableOffsets a b (side k 1) (side l 1) = (fun i => a k i + b l i) := by
  funext i
  cases k <;> cases l <;> norm_num [separableOffsets, side, relu]

lemma separableOffsets_cross_double (a b : Bool → ι → ℝ) (k l : Bool) :
    separableOffsets a b (side k 1) (side l 2) = (fun i => a k i + 2 * b l i) := by
  funext i
  cases k <;> cases l <;> norm_num [separableOffsets, side, relu] <;> ring

/-- The actual scalar four-gate identities imply the separable support
alternative. This replaces the finite-union-of-lines proof by eight algebraic
cross samples, and covers all real (including degenerate) coefficients. -/
theorem separable_four_relu_dichotomy (j : ι → ℝ) (a b : Bool → ι → ℝ)
    (hj : ∀ i, j i ≠ 0) (hcard : Fintype.card ι ≤ 4)
    (h : ∀ u v t : ℝ,
      (∑ i, j i * relu (t-separableOffsets a b u v i)) = relu t) :
    (∀ k i, a k i = 0) ∨ (∀ l i, b l i = 0) ∨
      ∃ (S : Set ι) (α β : Bool → ℝ), S.Nonempty ∧
        (∀ k i, a k i = if i ∈ S then α k else 0) ∧
        (∀ l i, b l i = if i ∈ S then β l else 0) := by
  have ha : ∀ k, OneLevel (a k) := by
    intro k
    rw [← separableOffsets_left_unit a b k]
    exact oneLevel_of_four_relu_identity j _ hj hcard (h _ _)
  have hb : ∀ l, OneLevel (b l) := by
    intro l
    rw [← separableOffsets_right_unit a b l]
    exact oneLevel_of_four_relu_identity j _ hj hcard (h _ _)
  have h₁ : ∀ k l, OneLevel (fun i => a k i + b l i) := by
    intro k l
    rw [← separableOffsets_cross_unit a b k l]
    exact oneLevel_of_four_relu_identity j _ hj hcard (h _ _)
  have h₂ : ∀ k l, OneLevel (fun i => a k i + 2 * b l i) := by
    intro k l
    rw [← separableOffsets_cross_double a b k l]
    exact oneLevel_of_four_relu_identity j _ hj hcard (h _ _)
  exact cross_samples_dichotomy a b ha hb h₁ h₂

end MaxCaterpillar.Fiber.Count65.Paired
