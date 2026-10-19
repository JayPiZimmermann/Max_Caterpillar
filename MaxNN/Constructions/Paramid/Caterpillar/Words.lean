import MaxNN.Constructions.Paramid.Geom.Defs
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Powerset

/-! # Ordered caterpillar spines

A word of `r+1` vertices is cut into nonempty consecutive blocks. The first
vertex of each block belongs to the spine; the remaining vertices are its
ordered pendant leaves. Cuts are indexed by the first position of the new
block, so position zero is never a cut.

For a vertex at position `j>0`, its parent is the last block head strictly
before `j`. This rule covers both a pendant leaf and the next spine vertex.
In particular, inserting a cut at the last position changes the endpoint of
the spine without changing any tree edge.
-/

open BigOperators

namespace MaxNN.Caterpillar

variable {r : ℕ}

/-- Allowed block starts other than the root. -/
def cutPositions (r : ℕ) : Finset (Fin (r + 1)) := Finset.univ.erase 0

/-- The parent of a noninitial position in the ordered caterpillar. -/
def parent (S : Finset (Fin (r + 1))) (j : Fin (r + 1)) : Fin (r + 1) :=
  (insert 0 (S.filter fun i => i < j)).max' (Finset.insert_nonempty _ _)

/-- The last spine vertex. The empty cut set gives the zero-length spine. -/
def lastHead (S : Finset (Fin (r + 1))) : Fin (r + 1) :=
  (insert 0 S).max' (Finset.insert_nonempty _ _)

theorem parent_lt {S : Finset (Fin (r + 1))} {j : Fin (r + 1)} (hj : 0 < j) :
    parent S j < j := by
  have h := Finset.max'_mem (insert 0 (S.filter fun i => i < j)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 h with h | h
  · change parent S j = 0 at h
    rw [h]
    exact hj
  · exact (Finset.mem_filter.1 h).2

theorem parent_insert_last (S : Finset (Fin (r + 1))) (j : Fin (r + 1)) :
    parent (insert (Fin.last r) S) j = parent S j := by
  unfold parent
  have h : ¬ Fin.last r < j := not_lt.2 (Fin.le_last j)
  simp only [Finset.filter_insert, if_neg h]

/-- Support function of the tree zonotope, evaluated at the vertex values `w`. -/
noncomputable def treeMax (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) : ℝ :=
  ∑ j : Fin r, max (w (parent S j.succ)) (w j.succ)

/-- The pointed base on one side of a cut spine edge. Its near endpoint has
already been subtracted, leaving only the far endpoint at position zero. -/
noncomputable def pointedMax (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) : ℝ :=
  treeMax w S - ∑ j, w j + w 0

/-- Support function of the caterpillar base, with both spine endpoints. -/
noncomputable def baseMax (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) : ℝ :=
  pointedMax w S + w (lastHead S)

theorem pointedMax_of_constant (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1)))
    (c : ℝ) (hw : ∀ i, w i = c) : pointedMax w S = 0 := by
  unfold pointedMax treeMax
  simp only [hw, max_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem baseMax_of_constant (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1)))
    (c : ℝ) (hw : ∀ i, w i = c) : baseMax w S = c := by
  rw [baseMax, pointedMax_of_constant w S c hw, zero_add, hw]

theorem treeMax_insert_last (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) :
    treeMax w (insert (Fin.last r) S) = treeMax w S := by
  simp only [treeMax, parent_insert_last]

theorem pointedMax_insert_last (w : Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) :
    pointedMax w (insert (Fin.last r) S) = pointedMax w S := by
  rw [pointedMax, pointedMax, treeMax_insert_last]

end MaxNN.Caterpillar
