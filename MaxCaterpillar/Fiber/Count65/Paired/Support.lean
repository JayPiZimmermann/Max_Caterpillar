import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.PushNeg

/-!
# The separable offset-support step

A four-atom balance allows a vector with only one nonzero value. Two positive
samples suffice to show that two nonzero coefficient vectors must have the
same support. This replaces the finite-union-of-lines argument in the paired
four-recession reduction. It is an algebraic ingredient, not a theorem that
arbitrary paired-network completions are connected.
-/
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace MaxCaterpillar.Fiber.Count65.Paired

variable {ι : Type*}

/-- All nonzero entries of the vector have the same value. -/
def OneLevel (v : ι → ℝ) : Prop :=
  ∀ i j, v i = 0 ∨ v j = 0 ∨ v i = v j

lemma OneLevel.no_left_only (a b : ι → ℝ)
    (ha : OneLevel a)
    (h₁ : OneLevel (fun i => a i + b i))
    (h₂ : OneLevel (fun i => a i + 2 * b i))
    (hb : ∃ j, b j ≠ 0) :
    ∀ i, a i ≠ 0 → b i ≠ 0 := by
  obtain ⟨j, hj⟩ := hb
  intro i hi hbi
  rcases ha i j with hai | haj | haij
  · exact hi hai
  · have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [hbi, haj, add_zero, zero_add, mul_zero] at e₁ e₂
    rcases e₁ with hz | hz | he₁
    · exact hi hz
    · exact hj hz
    · rcases e₂ with hz | hz | he₂
      · exact hi hz
      · exact hj (by linarith only [hz])
      · exact hj (by linarith only [he₁, he₂])
  · have e₁ := h₁ i j
    have e₂ := h₂ i j
    dsimp only at e₁ e₂
    rw [hbi, add_zero, ← haij] at e₁
    rw [hbi, mul_zero, add_zero, ← haij] at e₂
    have z₁ : a i + b j = 0 := by
      rcases e₁ with hz | hz | he
      · exact False.elim (hi hz)
      · exact hz
      · exact False.elim (hj (by linarith only [he]))
    have z₂ : a i + 2 * b j = 0 := by
      rcases e₂ with hz | hz | he
      · exact False.elim (hi hz)
      · exact hz
      · exact False.elim (hj (by linarith only [he]))
    exact hj (by linarith only [z₁, z₂])

lemma OneLevel.no_right_only (a b : ι → ℝ)
    (hb : OneLevel b)
    (h₁ : OneLevel (fun i => a i + b i))
    (h₂ : OneLevel (fun i => a i + 2 * b i))
    (ha : ∃ j, a j ≠ 0) :
    ∀ i, b i ≠ 0 → a i ≠ 0 := by
  obtain ⟨j, hj⟩ := ha
  intro i hi hai
  rcases hb i j with hbi | hbj | hbij
  · exact hi hbi
  · have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [hai, hbj, add_zero, zero_add, mul_zero] at e₁ e₂
    rcases e₁ with hz | hz | he₁
    · exact hi hz
    · exact hj hz
    · rcases e₂ with hz | hz | he₂
      · exact hi (by linarith only [hz])
      · exact hj hz
      · exact hi (by linarith only [he₁, he₂])
  · have e₁ := h₁ i j
    have e₂ := h₂ i j
    dsimp only at e₁ e₂
    rw [hai, zero_add, ← hbij] at e₁
    rw [hai, zero_add, ← hbij] at e₂
    have z₁ : a j + b i = 0 := by
      rcases e₁ with hz | hz | he
      · exact False.elim (hi hz)
      · exact hz
      · exact False.elim (hj (by linarith only [he]))
    have z₂ : a j + 2 * b i = 0 := by
      rcases e₂ with hz | hz | he
      · exact False.elim (hi (by linarith only [hz]))
      · exact hz
      · exact False.elim (hj (by linarith only [he]))
    exact hi (by linarith only [z₁, z₂])

/-- Two positive combinations force the common indicator direction. No
continuity, finite-dimensionality, or generic-position assumption is used. -/
theorem support_eq_of_two_positive_samples (a b : ι → ℝ)
    (ha : OneLevel a) (hb : OneLevel b)
    (h₁ : OneLevel (fun i => a i + b i))
    (h₂ : OneLevel (fun i => a i + 2 * b i))
    (ha₀ : ∃ i, a i ≠ 0) (hb₀ : ∃ i, b i ≠ 0) :
    Function.support a = Function.support b := by
  ext i
  exact ⟨OneLevel.no_left_only a b ha h₁ h₂ hb₀ i,
    OneLevel.no_right_only a b hb h₁ h₂ ha₀ i⟩

/-- The pointwise single-level property gives an actual indicator formula. -/
theorem oneLevel_indicator (v : ι → ℝ) (hv : OneLevel v)
    (i : ι) (hi : v i ≠ 0) :
    ∀ j, v j = if j ∈ Function.support v then v i else 0 := by
  classical
  intro j
  by_cases hj : v j = 0
  · simp [Function.support, hj]
  · have he : v i = v j := (hv i j).resolve_left hi |>.resolve_left hj
    simp [Function.support, hj, he]

/-- A nonzero pair with one common support is a scalar multiple of one
indicator vector, as required by the four-atom normal form. -/
theorem common_indicator_of_two_positive_samples (a b : ι → ℝ)
    (ha : OneLevel a) (hb : OneLevel b)
    (h₁ : OneLevel (fun i => a i + b i))
    (h₂ : OneLevel (fun i => a i + 2 * b i))
    (ha₀ : ∃ i, a i ≠ 0) (hb₀ : ∃ i, b i ≠ 0) :
    ∃ (S : Set ι) (α β : ℝ), S.Nonempty ∧ α ≠ 0 ∧ β ≠ 0 ∧
      (∀ i, a i = if i ∈ S then α else 0) ∧
      (∀ i, b i = if i ∈ S then β else 0) := by
  classical
  obtain ⟨i, hi⟩ := ha₀
  have hs := support_eq_of_two_positive_samples a b ha hb h₁ h₂ ⟨i,hi⟩ hb₀
  have hbi : b i ≠ 0 := by
    have him : i ∈ Function.support a := hi
    rwa [hs] at him
  refine ⟨Function.support a, a i, b i, ⟨i, hi⟩, hi, hbi,
    oneLevel_indicator a ha i hi, ?_⟩
  intro j
  rw [hs]
  exact oneLevel_indicator b hb i hbi j

section CrossFamilies
variable {κ ν : Type*}

/-- In a separable two-coordinate offset map, the occurrence of a nonzero
coefficient on each coordinate forces all coefficient vectors onto one common
indicator line. Coefficients that vanish identically are allowed. -/
theorem common_indicator_of_cross_samples
    (a : κ → ι → ℝ) (b : ν → ι → ℝ)
    (ha : ∀ k, OneLevel (a k)) (hb : ∀ l, OneLevel (b l))
    (h₁ : ∀ k l, OneLevel (fun i => a k i + b l i))
    (h₂ : ∀ k l, OneLevel (fun i => a k i + 2 * b l i))
    (ha₀ : ∃ k i, a k i ≠ 0) (hb₀ : ∃ l i, b l i ≠ 0) :
    ∃ (S : Set ι) (α : κ → ℝ) (β : ν → ℝ), S.Nonempty ∧
      (∀ k i, a k i = if i ∈ S then α k else 0) ∧
      (∀ l i, b l i = if i ∈ S then β l else 0) := by
  classical
  obtain ⟨k₀, i₀, hi₀⟩ := ha₀
  obtain ⟨l₀, j₀, hj₀⟩ := hb₀
  let S := Function.support (a k₀)
  have hab : Function.support (a k₀) = Function.support (b l₀) :=
    support_eq_of_two_positive_samples (a k₀) (b l₀) (ha k₀) (hb l₀)
      (h₁ k₀ l₀) (h₂ k₀ l₀) ⟨i₀, hi₀⟩ ⟨j₀, hj₀⟩
  refine ⟨S, fun k => a k i₀, fun l => b l i₀, ⟨i₀, hi₀⟩, ?_, ?_⟩
  · intro k i
    by_cases hzero : ∀ j, a k j = 0
    · simp [hzero]
    · push_neg at hzero
      have hs : Function.support (a k) = S :=
        (support_eq_of_two_positive_samples (a k) (b l₀) (ha k) (hb l₀)
          (h₁ k l₀) (h₂ k l₀) hzero ⟨j₀, hj₀⟩).trans hab.symm
      have hi : a k i₀ ≠ 0 := by
        have his : i₀ ∈ S := hi₀
        rwa [← hs] at his
      simpa only [hs] using oneLevel_indicator (a k) (ha k) i₀ hi i
  · intro l i
    by_cases hzero : ∀ j, b l j = 0
    · simp [hzero]
    · push_neg at hzero
      have hs : S = Function.support (b l) :=
        support_eq_of_two_positive_samples (a k₀) (b l) (ha k₀) (hb l)
          (h₁ k₀ l) (h₂ k₀ l) ⟨i₀, hi₀⟩ hzero
      have hi : b l i₀ ≠ 0 := by
        have his : i₀ ∈ S := hi₀
        rwa [hs] at his
      simpa only [← hs] using oneLevel_indicator (b l) (hb l) i₀ hi i

/-- The alternatives used by the four-recession proof: either one coordinate
is absent, or every offset coefficient has one globally fixed support. -/
theorem cross_samples_dichotomy
    (a : κ → ι → ℝ) (b : ν → ι → ℝ)
    (ha : ∀ k, OneLevel (a k)) (hb : ∀ l, OneLevel (b l))
    (h₁ : ∀ k l, OneLevel (fun i => a k i + b l i))
    (h₂ : ∀ k l, OneLevel (fun i => a k i + 2 * b l i)) :
    (∀ k i, a k i = 0) ∨ (∀ l i, b l i = 0) ∨
      ∃ (S : Set ι) (α : κ → ℝ) (β : ν → ℝ), S.Nonempty ∧
        (∀ k i, a k i = if i ∈ S then α k else 0) ∧
        (∀ l i, b l i = if i ∈ S then β l else 0) := by
  classical
  by_cases hza : ∀ k i, a k i = 0
  · exact Or.inl hza
  · by_cases hzb : ∀ l i, b l i = 0
    · exact Or.inr (Or.inl hzb)
    · push_neg at hza hzb
      exact Or.inr (Or.inr (common_indicator_of_cross_samples a b ha hb h₁ h₂ hza hzb))

end CrossFamilies

end MaxCaterpillar.Fiber.Count65.Paired
