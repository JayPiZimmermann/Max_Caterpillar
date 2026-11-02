import MaxCaterpillar.Fiber.Count65.ThreeRoots
import Mathlib.Data.Nat.Bitwise

/-! # Necessary geometry for all twenty-one three-root patterns

The numbering agrees with the independently checked finite root-graph cover.
The fourth row remains arbitrary real and is not assumed a coordinate root.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots ThreeRoots

noncomputable def pathWithFourth (b₀ b₁ b₂ : Bool) (t : Point 4) :
    Fin 4 → Point 4 :=
  ![![(if b₀ then 1 else -1),(if b₀ then -1 else 1),0,0],
    ![0,(if b₁ then 1 else -1),(if b₁ then -1 else 1),0],
    ![0,0,(if b₂ then 1 else -1),(if b₂ then -1 else 1)],t]

noncomputable def threeRootRows (k : Fin 21) (t : Point 4) : Fin 4 → Point 4 :=
  if k.val = 0 then transitiveTriangleRows t
  else if k.val = 1 then cyclicTriangleRows t
  else if k.val = 2 then oppositeAdjacentRows 1 t
  else if k.val = 3 then oppositeAdjacentRows (-1) t
  else if k.val = 4 then oppositeDisjointRows 1 t
  else if k.val < 13 then
    pathWithFourth (Nat.testBit (k.val-5) 0) (Nat.testBit (k.val-5) 1)
      (Nat.testBit (k.val-5) 2) t
  else starRows (Nat.testBit (k.val-13) 0) (Nat.testBit (k.val-13) 1)
      (Nat.testBit (k.val-13) 2) t

theorem pathWithFourth_eq (b₀ b₁ b₂ : Bool) (t : Point 4)
    (hsum : ∑ i,t i=0) :
    pathWithFourth b₀ b₁ b₂ t =
      ThreeRoots.pathRows b₀ b₁ b₂ (t 0) (t 0+t 1) (-t 3) := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · exact zero_sum_eq_pathFourth t hsum

theorem pathWithFourth_signs (b₀ b₁ b₂ : Bool) (t : Point 4)
    (hsum : ∑ i,t i=0) (ht : Nonroot t)
    (h : Represents (pathWithFourth b₀ b₁ b₂ t)) :
    (b₀=true ∧ b₁=true ∧ b₂=false) ∨
    (b₀=true ∧ b₁=false ∧ b₂=false) := by
  rw [pathWithFourth_eq b₀ b₁ b₂ t hsum] at h
  have htn : Nonroot (pathFourth (t 0) (t 0+t 1) (-t 3)) := by
    rw [←zero_sum_eq_pathFourth t hsum]
    exact ht
  rcases path_orientation_and_span b₀ b₁ b₂ _ _ _ h htn with h | h
  · exact Or.inl ⟨h.1,h.2.1,h.2.2.1⟩
  · exact Or.inr ⟨h.1,h.2.1,h.2.2.1⟩

/-- Only two reversed path patterns and the outward-star pattern survive
the width-independent information obstruction. This is a necessary-kind
theorem, not an assertion of first-matrix normal form. -/
theorem canonical_three_root_branch (k : Fin 21) (t : Point 4)
    (hsum : ∑ i,t i=0) (ht : Nonroot t)
    (hcover : ∀ i,∃ j,threeRootRows k t j i=0)
    (h : Represents (threeRootRows k t)) : k=6 ∨ k=8 ∨ k=13 := by
  fin_cases k
  · exact False.elim (not_represents_transitive_triangle t ht (by simpa [threeRootRows] using h))
  · exact False.elim (not_represents_cyclic_triangle t hsum ht (by simpa [threeRootRows] using h))
  · exact False.elim (opposite_adjacent_excluded 1 t (by norm_num) hsum ht
      (by simpa [threeRootRows] using hcover) (by simpa [threeRootRows] using h))
  · exact False.elim (opposite_adjacent_excluded (-1) t (by norm_num) hsum ht
      (by simpa [threeRootRows] using hcover) (by simpa [threeRootRows] using h))
  · exact False.elim (opposite_disjoint_excluded 1 t hsum ht (by simpa [threeRootRows] using h))
  · have hh := pathWithFourth_signs false false false t hsum ht
      (by exact h)
    simp at hh
  · exact Or.inl rfl
  · have hh := pathWithFourth_signs false true false t hsum ht
      (by exact h)
    simp at hh
  · exact Or.inr (Or.inl rfl)
  · have hh := pathWithFourth_signs false false true t hsum ht
      (by exact h)
    simp at hh
  · have hh := pathWithFourth_signs true false true t hsum ht
      (by exact h)
    simp at hh
  · have hh := pathWithFourth_signs false true true t hsum ht
      (by exact h)
    simp at hh
  · have hh := pathWithFourth_signs true true true t hsum ht
      (by exact h)
    simp at hh
  · exact Or.inr (Or.inr rfl)
  · have hh := star_orientation_forced true false false t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced false true false t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced true true false t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced false false true t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced true false true t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced false true true t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh
  · have hh := star_orientation_forced true true true t hsum ht
      (by exact hcover) (by exact h)
    norm_num at hh

/-- A strict first-state cell on which the canonical path has a unique
winning anchor. This remains valid on the root endpoint b=a. -/
theorem canonical_path_strict_inactive (a b : ℝ) (ha : 0<a) :
    ∃ z : Point 4, z 2=Maximum 4 z ∧
      ∀ j,lin (ThreeRoots.pathRows true true false a b 0 j) z<0 := by
  let z : Point 4 := ![-a-abs b-1,-a,0,-1]
  refine ⟨z,?_,?_⟩
  · rw [Maximum_four]
    change 0 = max (max (-a-abs b-1) (-a)) (max 0 (-1))
    rw [show max (-a-abs b-1) (-a) = -a from max_eq_right (by linarith [abs_nonneg b]),
      show max (0 : ℝ) (-1) = 0 from max_eq_left (by norm_num),
      show max (-a) 0 = 0 from max_eq_right (by linarith only [ha])]
  · intro j
    fin_cases j
    · norm_num [lin_four,ThreeRoots.pathRows,z]
      linarith [abs_nonneg b]
    · simpa [lin_four,ThreeRoots.pathRows,z] using neg_neg_of_pos ha
    · norm_num [lin_four,ThreeRoots.pathRows,z]
    · have hab : 0≤abs b+b := by linarith [neg_abs_le_self b]
      have hp : 0<a*(abs b+b+1) := mul_pos ha (by linarith only [hab])
      norm_num [lin_four,ThreeRoots.pathRows,pathFourth,z]
      nlinarith only [hp]

#print axioms canonical_three_root_branch
#print axioms canonical_path_strict_inactive
end MaxCaterpillar.Fiber.Count65.FrameTransport
