import MaxNN.Core.Class
import MaxNN.Core.Max
import Mathlib.Algebra.BigOperators.Order

/-!
# Paramid units: cones over parallelepipeds as two-hidden-layer networks

A *paramid* is the cone from the origin over a parallelepiped
`γ + ∑ᵢ [0, vᵢ]`.  Its support function is

  `y ↦ relu (⟨γ, y⟩ + ∑ᵢ relu ⟨vᵢ, y⟩)`,

one ReLU over a sum of ReLUs of linear forms: a two-hidden-layer network whose
first layer holds the `k` hinges `relu ⟨vᵢ, y⟩` (plus a carrier for `⟨γ, y⟩`)
and whose second layer is the single outer unit.  The Brunck–Stade–Yehudayoff
depth-two construction of `MAX n` is a rational combination of such units,
corrected by maxima of fewer than `n` linear forms.

This file defines the unit, proves that it is the maximum over the vertices of
the paramid (`paramidUnit_eq_max_vertices`), and proves its two-hidden-layer
membership (`paramidUnit_mem_reluClass_two`).  Nothing here depends on any
finite certificate.
-/

namespace MaxNN

open BigOperators

/-- The linear form `y ↦ ⟨v, y⟩`. -/
noncomputable def dot {n : ℕ} (v y : Fin n → ℝ) : ℝ := ∑ i, v i * y i

/-- The paramid unit with apex-offset `γ` and edge vectors `v₁, …, v_k`:
`relu (⟨γ, y⟩ + ∑ᵢ relu ⟨vᵢ, y⟩)`. -/
noncomputable def paramidUnit {n k : ℕ} (γ : Fin n → ℝ) (v : Fin k → Fin n → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  relu (dot γ y + ∑ j, relu (dot (v j) y))

/-! ## The unit is the support function of the paramid -/

/-- `∑ⱼ relu ⟨vⱼ, y⟩` is the maximum of `⟨∑_{j ∈ I} vⱼ, y⟩` over all subsets `I`. -/
theorem sum_relu_dot_eq_sup {n k : ℕ} (v : Fin k → Fin n → ℝ) (y : Fin n → ℝ) :
    (∑ j, relu (dot (v j) y)) =
      (Finset.univ : Finset (Finset (Fin k))).sup'
        Finset.univ_nonempty (fun I => ∑ j in I, dot (v j) y) := by
  apply le_antisymm
  · -- the subset of positive hinges attains the sum
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun I => ∑ j in I, dot (v j) y)
      (Finset.mem_univ (Finset.univ.filter fun j => 0 < dot (v j) y)))
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases h : 0 < dot (v j) y
    · rw [if_pos h, relu_of_nonneg (le_of_lt h)]
    · rw [if_neg h, relu_of_nonpos (le_of_not_lt h)]
  · refine Finset.sup'_le _ _ ?_
    intro I _
    calc
      (∑ j in I, dot (v j) y) ≤ ∑ j in I, relu (dot (v j) y) :=
        Finset.sum_le_sum fun j _ => le_max_right 0 _
      _ ≤ ∑ j, relu (dot (v j) y) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
          fun j _ _ => relu_nonneg _

/-- The paramid unit equals the maximum of `0` and `⟨γ + ∑_{j ∈ I} vⱼ, y⟩` over all
subsets `I`: the support function of the cone over the parallelepiped. -/
theorem paramidUnit_eq_max_vertices {n k : ℕ} (γ : Fin n → ℝ)
    (v : Fin k → Fin n → ℝ) (y : Fin n → ℝ) :
    paramidUnit γ v y =
      max 0 ((Finset.univ : Finset (Finset (Fin k))).sup'
        Finset.univ_nonempty (fun I => dot γ y + ∑ j in I, dot (v j) y)) := by
  have key : dot γ y + (Finset.univ : Finset (Finset (Fin k))).sup'
        Finset.univ_nonempty (fun I => ∑ j in I, dot (v j) y) =
      (Finset.univ : Finset (Finset (Fin k))).sup'
        Finset.univ_nonempty (fun I => dot γ y + ∑ j in I, dot (v j) y) := by
    apply le_antisymm
    · obtain ⟨I, _, hI⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun I : Finset (Fin k) => ∑ j in I, dot (v j) y)
      rw [hI]
      exact Finset.le_sup' (fun I : Finset (Fin k) => dot γ y + ∑ j in I, dot (v j) y)
        (Finset.mem_univ I)
    · refine Finset.sup'_le _ _ ?_
      intro I _
      exact add_le_add_left
        (Finset.le_sup' (fun I : Finset (Fin k) => ∑ j in I, dot (v j) y)
          (Finset.mem_univ I)) _
  rw [paramidUnit, sum_relu_dot_eq_sup, key]
  rfl

/-! ## Two hidden layers suffice -/

theorem dot_mem_reluClass_zero {n : ℕ} (v : Fin n → ℝ) :
    (fun y => dot v y) ∈ ReLUClass n 0 := by
  have h := affine_mem_reluClass v 0
  have e : (fun y : Fin n → ℝ => (∑ j, v j * y j) + 0) = fun y => dot v y := by
    funext y
    rw [add_zero]
    rfl
  rw [e] at h
  exact h

/-- A hinge `relu ⟨v, y⟩` has one hidden layer. -/
theorem relu_dot_mem_reluClass_one {n : ℕ} (v : Fin n → ℝ) :
    (fun y => relu (dot v y)) ∈ ReLUClass n 1 := by
  have h := max_mem_reluClass (const_mem_reluClass (n := n) 0) (dot_mem_reluClass_zero v)
  exact h

/-- **A paramid unit is a two-hidden-layer network.** -/
theorem paramidUnit_mem_reluClass_two {n k : ℕ} (γ : Fin n → ℝ)
    (v : Fin k → Fin n → ℝ) :
    paramidUnit γ v ∈ ReLUClass n 2 := by
  have hinner : (fun y => dot γ y + ∑ j, relu (dot (v j) y)) ∈ ReLUClass n 1 := by
    refine add_mem_reluClass (reluClass_mono (Nat.zero_le 1) (dot_mem_reluClass_zero γ)) ?_
    exact sum_mem_reluClass Finset.univ (fun j y => relu (dot (v j) y))
      fun j _ => relu_dot_mem_reluClass_one (v j)
  have h := max_mem_reluClass
    (reluClass_mono (Nat.zero_le 1) (const_mem_reluClass (n := n) 0)) hinner
  exact h

end MaxNN
