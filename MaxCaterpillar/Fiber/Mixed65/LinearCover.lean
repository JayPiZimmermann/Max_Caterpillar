import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Infinite
import Mathlib.Tactic.Linarith

/-! # Finite affine covers of a real interval

If finitely many affine functions cover an infinite set by their zero sets,
one of those functions is identically zero. An arbitrary predicate may select
which functions are eligible at a covered point. This lemma retains that
predicate in its conclusion.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

/-- A finite affine zero cover of an infinite set contains an identically zero
eligible function. No regularity or decidability of `Good` is required. -/
theorem exists_zero_affine_of_infinite_cover {ι : Type*}
    (I : Finset ι) (A B : ι → ℝ) (Good : ι → Prop)
    {S : Set ℝ} (hS : S.Infinite)
    (hcover : ∀ x ∈ S, ∃ i ∈ I, Good i ∧ A i + B i * x = 0) :
    ∃ i ∈ I, Good i ∧ A i = 0 ∧ B i = 0 := by
  classical
  obtain ⟨x, hxS, hx⟩ := hS.exists_not_mem_finset (I.image fun i => -A i / B i)
  obtain ⟨i, hi, hGood, hzero⟩ := hcover x hxS
  by_cases hB : B i = 0
  · exact ⟨i, hi, hGood, by simpa only [hB, zero_mul, add_zero] using hzero, hB⟩
  · have he : x = -A i / B i := (eq_div_iff hB).mpr (by nlinarith only [hzero])
    exact (hx (Finset.mem_image.mpr ⟨i, hi, he.symm⟩)).elim

/-- In particular, a cover of a nonempty real open interval forces an
identically zero eligible affine function. -/
theorem exists_zero_affine_of_interval_cover {ι : Type*}
    (I : Finset ι) (A B : ι → ℝ) (Good : ι → Prop)
    {a b : ℝ} (hab : a < b)
    (hcover : ∀ x ∈ Set.Ioo a b, ∃ i ∈ I, Good i ∧ A i + B i * x = 0) :
    ∃ i ∈ I, Good i ∧ A i = 0 ∧ B i = 0 :=
  exists_zero_affine_of_infinite_cover I A B Good (Set.Ioo_infinite hab) hcover

/-- The finite-type formulation used when the eligible functions are network
neurons rather than an explicitly selected finite set. -/
theorem exists_zero_affine_of_interval_cover_fintype {ι : Type*} [Fintype ι]
    (A B : ι → ℝ) (Good : ι → Prop) {a b : ℝ} (hab : a < b)
    (hcover : ∀ x ∈ Set.Ioo a b, ∃ i, Good i ∧ A i + B i * x = 0) :
    ∃ i, Good i ∧ A i = 0 ∧ B i = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := exists_zero_affine_of_interval_cover Finset.univ A B Good hab
    (fun x hx => by
      obtain ⟨i, hGood, hzero⟩ := hcover x hx
      exact ⟨i, Finset.mem_univ i, hGood, hzero⟩)
  exact ⟨i, hi⟩

end MaxCaterpillar.Fiber.Mixed65
