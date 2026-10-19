import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real

/-!
# `MAX n` — the maximum of `n` real coordinates

`MAX n x = max {x 0, …, x (n-1)}`, the function whose exact depth complexity this project
studies.  Defined for positive `n` (`[NeZero n]`); `MAX 0` would be a maximum over the
empty set and stays undefined.

Elementary interface: `le_MAX`, `MAX_le`, `MAX_eq_of_forall_le`, the recursion `MAX_succ`,
and the small cases `MAX_one`, `MAX_two`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- Positive `n` makes `Fin n` nonempty.  (Not an instance in this Mathlib version.) -/
instance {n : ℕ} [NeZero n] : Nonempty (Fin n) :=
  ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩

/-- `MAX n x = max {x 0, …, x (n-1)}`. -/
noncomputable def MAX (n : ℕ) [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

theorem le_MAX (n : ℕ) [NeZero n] (x : Fin n → ℝ) (i : Fin n) : x i ≤ MAX n x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem MAX_le {n : ℕ} [NeZero n] {x : Fin n → ℝ} {c : ℝ} (h : ∀ i, x i ≤ c) :
    MAX n x ≤ c :=
  Finset.sup'_le _ x fun i _ => h i

theorem MAX_eq_of_forall_le {n : ℕ} [NeZero n] {x : Fin n → ℝ} {i : Fin n}
    (h : ∀ j, x j ≤ x i) : MAX n x = x i :=
  le_antisymm (MAX_le h) (le_MAX n x i)

theorem MAX_one (x : Fin 1 → ℝ) : MAX 1 x = x 0 :=
  MAX_eq_of_forall_le fun j => le_of_eq (congrArg x (Fin.eq_zero j))

/-- Recursion in the arity: split off the last coordinate. -/
theorem MAX_succ (n : ℕ) [NeZero n] (x : Fin (n + 1) → ℝ) :
    MAX (n + 1) x = max (MAX n fun i => x i.castSucc) (x (Fin.last n)) := by
  refine le_antisymm (MAX_le fun i => ?_) (max_le (MAX_le fun i => ?_) (le_MAX _ _ _))
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_max_right _ _
    · exact le_trans (le_MAX n (fun i => x i.castSucc) j) (le_max_left _ _)
  · exact le_MAX (n + 1) x i.castSucc

theorem MAX_two (x : Fin 2 → ℝ) : MAX 2 x = max (x 0) (x 1) := by
  rw [MAX_succ 1 x, MAX_one]
  have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  have h1 : Fin.last 1 = (1 : Fin 2) := rfl
  rw [h0, h1]

/-- The maximum is attained at some index. -/
theorem exists_MAX_eq (n : ℕ) [NeZero n] (x : Fin n → ℝ) : ∃ i, MAX n x = x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty) x
  exact ⟨i, hi⟩

/-- The maximum is attained at an index dominating all coordinates. -/
theorem exists_forall_le_of_MAX (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    ∃ i, ∀ j, x j ≤ x i := by
  obtain ⟨i, hi⟩ := exists_MAX_eq n x
  exact ⟨i, fun j => hi ▸ le_MAX n x j⟩

/-- `MAX` is invariant under reindexing by an involution. -/
theorem MAX_comp_involutive {n : ℕ} [NeZero n] (x : Fin n → ℝ) {σ : Fin n → Fin n}
    (hσ : ∀ i, σ (σ i) = i) : MAX n (fun i => x (σ i)) = MAX n x := by
  refine le_antisymm (MAX_le fun i => le_MAX n x (σ i)) (MAX_le fun i => ?_)
  have h : x (σ (σ i)) ≤ MAX n fun j => x (σ j) := le_MAX n (fun j => x (σ j)) (σ i)
  rw [hσ i] at h
  exact h

/-- Peel off any one coordinate: `MAX` over `q+1` coordinates is the `max` of the
coordinate at `t` and the `MAX` over the remaining ones (indexed via `Fin.succAbove`). -/
theorem MAX_succAbove {q : ℕ} [NeZero q] (x : Fin (q + 1) → ℝ) (t : Fin (q + 1)) :
    MAX (q + 1) x = max (x t) (MAX q fun i => x (t.succAbove i)) := by
  refine le_antisymm (MAX_le fun i => ?_) (max_le (le_MAX _ x t) (MAX_le fun i => ?_))
  · rcases eq_or_ne i t with h | h
    · rw [h]
      exact le_max_left _ _
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
      exact le_trans (le_of_eq (congrArg x hj.symm))
        (le_trans (le_MAX q (fun i => x (t.succAbove i)) j) (le_max_right _ _))
  · exact le_MAX (q + 1) x (t.succAbove i)

/-- `MAX` is positively homogeneous. -/
theorem MAX_smul {q : ℕ} [NeZero q] {c : ℝ} (hc : 0 ≤ c) (x : Fin q → ℝ) :
    MAX q (fun i => c * x i) = c * MAX q x := by
  refine le_antisymm (MAX_le fun i => mul_le_mul_of_nonneg_left (le_MAX q x i) hc) ?_
  obtain ⟨i, hi⟩ := exists_MAX_eq q x
  rw [hi]
  exact le_MAX q (fun i => c * x i) i

/-- `MAX (m+1)` is continuous. -/
theorem continuous_MAX_succ : ∀ m : ℕ, Continuous (MAX (m + 1)) := by
  intro m
  induction m with
  | zero =>
      rw [show MAX 1 = fun x : Fin 1 → ℝ => x 0 from funext MAX_one]
      exact continuous_apply 0
  | succ m ih =>
      rw [show MAX (m + 2) = fun x : Fin (m + 2) → ℝ =>
        max (MAX (m + 1) fun i => x i.castSucc) (x (Fin.last (m + 1))) from
        funext fun x => MAX_succ (m + 1) x]
      exact Continuous.max
        (ih.comp (continuous_pi fun i => continuous_apply i.castSucc))
        (continuous_apply (Fin.last (m + 1)))

/-- `MAX` is continuous. -/
theorem continuous_MAX (n : ℕ) [NeZero n] : Continuous (MAX n) := by
  rcases n with _ | m
  · exact absurd rfl (NeZero.ne 0)
  · exact continuous_MAX_succ m

/-- `MAX` is equivariant under adding a common constant to every coordinate. -/
theorem MAX_add_const {n : ℕ} [NeZero n] (x : Fin n → ℝ) (t : ℝ) :
    MAX n (fun i => x i + t) = MAX n x + t := by
  refine le_antisymm (MAX_le fun i => add_le_add_right (le_MAX n x i) t) ?_
  obtain ⟨i, hi⟩ := exists_MAX_eq n x
  rw [hi]
  exact le_MAX n (fun i => x i + t) i

/-- `MAX` over five coordinates, as a nested binary `max`. -/
theorem MAX_five (y : Fin 5 → ℝ) :
    MAX 5 y = max (y 0) (max (y 1) (max (y 2) (max (y 3) (y 4)))) := by
  refine le_antisymm (MAX_le fun i => ?_)
    (max_le (le_MAX 5 y 0) (max_le (le_MAX 5 y 1)
      (max_le (le_MAX 5 y 2) (max_le (le_MAX 5 y 3) (le_MAX 5 y 4)))))
  refine Fin.cases ?_ (fun i1 => ?_) i
  · exact le_max_left _ _
  · refine Fin.cases ?_ (fun i2 => ?_) i1
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · refine Fin.cases ?_ (fun i3 => ?_) i2
      · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
      · refine Fin.cases ?_ (fun i4 => ?_) i3
        · exact le_trans
            (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
            (le_max_right _ _)
        · refine Fin.cases ?_ (fun i5 => ?_) i4
          · exact le_trans
              (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
              (le_max_right _ _)
          · exact Fin.elim0 i5

end MaxNN
