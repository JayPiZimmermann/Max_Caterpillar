import MaxNN.Constructions.Paramid.Caterpillar.Formula.Values
import Mathlib.Algebra.BigOperators.Ring

/-! # A finite inclusion-exclusion identity for root-star units

The alternating sum cancels by toggling any nonnegative coordinate. If no
coordinate is nonnegative, every summand is zero. This is a pointwise scalar
identity; no induction on the number of coordinates is used in its proof.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem alternating_powerset_sum_eq_zero_of_insert
    (E : Finset ι) (j : ι) (hj : j ∈ E) (f : Finset ι → ℝ)
    (hf : ∀ S ⊆ E.erase j, f (insert j S) = f S) :
    ∑ S in E.powerset, (-1 : ℝ) ^ S.card * f S = 0 := by
  calc
    ∑ S in E.powerset, (-1 : ℝ) ^ S.card * f S =
        ∑ S in (insert j (E.erase j)).powerset, (-1 : ℝ) ^ S.card * f S := by
          rw [Finset.insert_erase hj]
    _ = 0 := by
      rw [Finset.sum_powerset_insert (Finset.not_mem_erase j E), ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hjS : j ∉ S := fun h => Finset.not_mem_erase j E (hsub h)
      rw [Finset.card_insert_of_not_mem hjS, pow_succ, hf S hsub]
      ring

theorem rootStarArg_eq (w : ι → ℝ) (S : Finset ι) :
    (∑ i in S, w i) + ∑ i in Finset.univ \ S, relu (w i) =
      (∑ i, relu (w i)) - ∑ i in S, relu (-w i) := by
  have hsum := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => relu (w i))
  have he : ∑ i in S, w i =
      (∑ i in S, relu (w i)) - ∑ i in S, relu (-w i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (relu_sub_relu_neg (w i)).symm
  rw [he]
  linarith

/-- The complete powerset identity, retaining the empty and singleton terms
so that the geometric proof can separate them explicitly. -/
theorem rootStar_alternating_sum (w : ι → ℝ) :
    ∑ S in (Finset.univ : Finset ι).powerset, (-1 : ℝ) ^ S.card *
      relu ((∑ i in S, w i) + ∑ i in Finset.univ \ S, relu (w i)) = 0 := by
  simp_rw [rootStarArg_eq]
  by_cases hp : ∃ j, 0 ≤ w j
  · obtain ⟨j, hj⟩ := hp
    apply alternating_powerset_sum_eq_zero_of_insert Finset.univ j (Finset.mem_univ j)
    intro S hS
    have hjS : j ∉ S := fun h => Finset.not_mem_erase j Finset.univ (hS h)
    rw [Finset.sum_insert hjS, relu_of_nonpos (neg_nonpos.mpr hj), zero_add]
  · have hn : ∀ j, w j < 0 := by
      intro j
      exact lt_of_not_ge (fun hj => hp ⟨j, hj⟩)
    have hzero : ∑ i, relu (w i) = 0 := by
      exact Finset.sum_eq_zero fun i _ => relu_of_nonpos (hn i).le
    rw [hzero]
    apply Finset.sum_eq_zero
    intro S _hS
    rw [relu_of_nonpos (by
      have hh : 0 ≤ ∑ i in S, relu (-w i) :=
        Finset.sum_nonneg fun i _ => relu_nonneg _
      linarith), mul_zero]

end MaxNN.Caterpillar
