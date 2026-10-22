import MaxNN.Core.Max
import MaxNN.Core.Affine
import MaxNN.CPWL.Pieces.Polyhedra

/-!
# Lifting `max(y, 0)` on `ℝ^d` back to `MAX (d+1)` on `ℝ^{d+1}`

Bricks for the converse direction of the arity transfer
(`MaxNN/CPWL/Representation/Arity.lean`): `MAX (d+1)` is recovered from the CPWL function
`y ↦ max(y₁, …, y_d, 0)` on `ℝ^d` by one affine precomposition and one affine output term,

  `MAX (d+1) x = max(x₁ - x_{d+1}, …, x_d - x_{d+1}, 0) + x_{d+1}`.

* `AffineFn.coordOrZero d t` — the affine function `y ↦ y_i` for `t = castSucc i`, and `0` for
  `t = last d`; so `y ↦ MAX (d+1) (fun t => (coordOrZero d t).eval y)` is `max(y, 0)`.
* `Affine.subLast d : Affine (d+1) d` — the affine map `x ↦ (x_i - x_{d+1})_i`.
* `MAX_sub_const` — `MAX n (x - c) = MAX n x - c`.
* `MAX_succ_eq_coordOrZero_subLast` — the displayed identity.
* `padIndex`, `MAX_eq_MAX_padIndex` — a maximum of `m ≤ N` values is a maximum of `N` values
  (used to turn "at most `d+1`" into "exactly `d+1`" for `HasHingingRep`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-! ## Padding a maximum of `m ≤ N` values to a maximum of `N` values -/

/-- The index map `Fin N → Fin m` (`m ≠ 0`) that is the identity on `{t : t < m}` and sends
every other index to `0`.  Precomposing with it pads a maximum of `m ≤ N` values to a maximum
of `N` values (`MAX_eq_MAX_padIndex`). -/
def padIndex (m N : ℕ) [NeZero m] (t : Fin N) : Fin m :=
  if h : (t : ℕ) < m then ⟨t, h⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

theorem padIndex_of_lt {m N : ℕ} [NeZero m] {t : Fin N} (h : (t : ℕ) < m) :
    padIndex m N t = ⟨t, h⟩ :=
  dif_pos h

/-- A maximum of `m ≤ N` values is a maximum of `N` values (repeat the first value). -/
theorem MAX_eq_MAX_padIndex {m N : ℕ} [NeZero m] [NeZero N] (hmN : m ≤ N) (y : Fin m → ℝ) :
    MAX m y = MAX N fun t => y (padIndex m N t) := by
  refine le_antisymm (MAX_le fun i => ?_) (MAX_le fun t => le_MAX m y _)
  have h := le_MAX N (fun t => y (padIndex m N t)) ⟨i, lt_of_lt_of_le i.2 hmN⟩
  have e : padIndex m N ⟨i, lt_of_lt_of_le i.2 hmN⟩ = i := padIndex_of_lt i.2
  rw [e] at h
  exact h

/-! ## Subtracting a constant -/

/-- `MAX n` commutes with subtracting a constant from every coordinate. -/
theorem MAX_sub_const {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c : ℝ) :
    MAX n (fun i => x i - c) = MAX n x - c := by
  refine le_antisymm (MAX_le fun i => sub_le_sub_right (le_MAX n x i) c) ?_
  obtain ⟨i, hi⟩ := exists_MAX_eq n x
  rw [hi]
  exact le_MAX n (fun i => x i - c) i

namespace AffineFn

/-- The affine function on `ℝ^d` that is the coordinate `y ↦ y i` when `t = castSucc i`, and
the zero function when `t = last d`. -/
noncomputable def coordOrZero (d : ℕ) (t : Fin (d + 1)) : AffineFn d :=
  ⟨fun i => if Fin.castSucc i = t then 1 else 0, 0⟩

end AffineFn

namespace Affine

/-- The affine map `ℝ^{d+1} → ℝ^d`, `x ↦ (x_i - x_{d+1})_{i < d}`. -/
noncomputable def subLast (d : ℕ) : Affine (d + 1) d :=
  ⟨fun i t => (if t = Fin.castSucc i then 1 else 0) - (if t = Fin.last d then 1 else 0),
    fun _ => 0⟩

theorem subLast_eval {d : ℕ} (x : Fin (d + 1) → ℝ) (i : Fin d) :
    (subLast d).eval x i = x (Fin.castSucc i) - x (Fin.last d) := by
  show (∑ t, ((if t = Fin.castSucc i then (1 : ℝ) else 0) - (if t = Fin.last d then 1 else 0))
      * x t) + 0 = _
  rw [add_zero, Finset.sum_congr rfl fun t _ => sub_mul _ _ (x t), Finset.sum_sub_distrib,
    Affine.delta_row_sum, Affine.delta_row_sum]

end Affine

/-- `coordOrZero d t` evaluated at `subLast d x` is `x t - x (last d)`, for every `t`. -/
theorem AffineFn.coordOrZero_eval_subLast {d : ℕ} (x : Fin (d + 1) → ℝ) (t : Fin (d + 1)) :
    (AffineFn.coordOrZero d t).eval ((Affine.subLast d).eval x) = x t - x (Fin.last d) := by
  show (∑ i, (if Fin.castSucc i = t then (1 : ℝ) else 0) * (Affine.subLast d).eval x i) + 0
      = x t - x (Fin.last d)
  rw [add_zero]
  refine Fin.lastCases ?_ (fun i₀ => ?_) t
  · rw [sub_self]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (Fin.castSucc_lt_last i).ne, zero_mul]
  · have e : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (if Fin.castSucc i = Fin.castSucc i₀ then (1 : ℝ) else 0) * (Affine.subLast d).eval x i
          = if i = i₀ then (Affine.subLast d).eval x i else 0 := by
      intro i _
      by_cases h : i = i₀
      · rw [if_pos (congrArg Fin.castSucc h), if_pos h, one_mul]
      · rw [if_neg (fun h' => h (Fin.castSucc_injective d h')), if_neg h, zero_mul]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' Finset.univ i₀, if_pos (Finset.mem_univ i₀),
      Affine.subLast_eval]

/-- **The lift identity.**  `MAX (d+1) x = max(x₁ - x_{d+1}, …, x_d - x_{d+1}, 0) + x_{d+1}`,
with the inner maximum written as `MAX (d+1)` of the `coordOrZero` functions at `subLast x`. -/
theorem MAX_succ_eq_coordOrZero_subLast {d : ℕ} (x : Fin (d + 1) → ℝ) :
    MAX (d + 1) x
      = MAX (d + 1) (fun t => (AffineFn.coordOrZero d t).eval ((Affine.subLast d).eval x))
        + x (Fin.last d) := by
  have e2 : (fun t => (AffineFn.coordOrZero d t).eval ((Affine.subLast d).eval x))
      = fun t => x t - x (Fin.last d) :=
    funext fun t => AffineFn.coordOrZero_eval_subLast x t
  rw [e2, MAX_sub_const, sub_add_cancel]

end MaxNN
