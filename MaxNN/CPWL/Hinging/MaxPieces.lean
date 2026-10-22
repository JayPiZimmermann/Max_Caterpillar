import MaxNN.CPWL.Def
import MaxNN.Core.Max
import Mathlib.Topology.Order.Basic

/-!
# `MAX n` is CPWL

Support bricks for the hinging development (`MaxNN/CPWL/Hinging.lean`):

* `coordDominance n i` — the closed polyhedral region `{x | ∀ l, x l ≤ x i}` where
  coordinate `i` dominates;
* `continuous_MAX` — `MAX n` is continuous (nested binary maxima);
* `MAX_mem_cpwl` — `MAX n ∈ CPWL n`: the `n` dominance regions cover `ℝ^n` and on the
  `i`-th one `MAX n` agrees with the coordinate function `x ↦ x i`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- The dominance region of coordinate `i`: `{x | ∀ l, x l ≤ x i}`, as a polyhedron
with the `n` constraints `x l - x i ≤ 0`. -/
noncomputable def coordDominance (n : ℕ) (i : Fin n) : Polyhedron n :=
  ⟨n, fun l j => (if j = l then 1 else 0) - (if j = i then 1 else 0), fun _ => 0⟩

theorem mem_coordDominance {n : ℕ} {i : Fin n} {x : Fin n → ℝ} :
    x ∈ (coordDominance n i).carrier ↔ ∀ l, x l ≤ x i := by
  have key : ∀ l : Fin n, (∑ j, (coordDominance n i).C l j * x j) = x l - x i := by
    intro l
    show (∑ j, ((if j = l then (1 : ℝ) else 0) - (if j = i then 1 else 0)) * x j)
        = x l - x i
    rw [Finset.sum_congr rfl fun j _ =>
        sub_mul (if j = l then (1 : ℝ) else 0) (if j = i then (1 : ℝ) else 0) (x j),
      Finset.sum_sub_distrib, Affine.delta_row_sum l x, Affine.delta_row_sum i x]
  constructor
  · intro h l
    have hl := h l
    rw [key l] at hl
    exact sub_nonpos.mp hl
  · intro h l
    rw [key l]
    exact sub_nonpos.mpr (h l)

-- `continuous_MAX_succ` and `continuous_MAX` now live in `MaxNN/Core/Max.lean`.

/-- **`MAX n` is CPWL**: piece `i` is the dominance region of coordinate `i`, and there
`MAX n` agrees with the coordinate function `x ↦ x i`. -/
theorem MAX_mem_cpwl (n : ℕ) [NeZero n] : MAX n ∈ CPWL n := by
  refine ⟨continuous_MAX n,
    ⟨⟨n, coordDominance n, fun i => ⟨fun j => if j = i then 1 else 0, 0⟩, ?_, ?_⟩⟩⟩
  · intro x
    obtain ⟨i, hi⟩ := exists_forall_le_of_MAX n x
    exact ⟨i, mem_coordDominance.mpr hi⟩
  · intro i x hx
    show MAX n x = (∑ j, (if j = i then (1 : ℝ) else 0) * x j) + 0
    rw [Affine.delta_row_sum i x, add_zero]
    exact MAX_eq_of_forall_le (mem_coordDominance.mp hx)

end MaxNN
