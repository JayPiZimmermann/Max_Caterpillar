import MaxNN.Core.Class
import MaxNN.Core.Max

/-!
# Monotonicity in the arity

`MAX_{m+1} ∈ ReLU_{m+1,k}` implies `MAX_m ∈ ReLU_{m,k}`: precompose with the affine map
duplicating the last coordinate, `(x₀, …, x_{m-1}) ↦ (x₀, …, x_{m-1}, x_{m-1})`, which
costs no hidden layers.

Note it runs *downward* in the arity: an impossibility for `MAX_10` says nothing about
`MAX_6`, while an impossibility for `MAX_5` (in a weight class closed under this
precomposition) transfers to `MAX_6`.  Branch L2 of `work/DFS_LOG.md` needs exactly this.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- The last index of `Fin m`, for positive `m`. -/
def lastIdx (m : ℕ) [NeZero m] : Fin m :=
  ⟨m - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne m)) Nat.one_pos⟩

namespace Affine

/-- The affine map `ℝ^m → ℝ^{m+1}` duplicating the last coordinate:
`(x₀, …, x_{m-1}) ↦ (x₀, …, x_{m-1}, x_{m-1})`. -/
noncomputable def dupLast (m : ℕ) [NeZero m] : Affine m (m + 1) where
  A := Fin.snoc (fun i j => if j = i then 1 else 0)
    fun j => if j = lastIdx m then 1 else 0
  b := fun _ => 0

theorem dupLast_eval_castSucc {m : ℕ} [NeZero m] (x : Fin m → ℝ) (i : Fin m) :
    (dupLast m).eval x i.castSucc = x i := by
  unfold eval dupLast
  show (∑ j, Fin.snoc (α := fun _ => Fin m → ℝ)
      (fun i j => if j = i then 1 else 0)
      (fun j => if j = lastIdx m then 1 else 0) (Fin.castSucc i) j * x j) + (0 : ℝ) = x i
  rw [Fin.snoc_castSucc]
  show (∑ j, (if j = i then (1 : ℝ) else 0) * x j) + 0 = x i
  rw [delta_row_sum i x, add_zero]

theorem dupLast_eval_last {m : ℕ} [NeZero m] (x : Fin m → ℝ) :
    (dupLast m).eval x (Fin.last m) = x (lastIdx m) := by
  unfold eval dupLast
  show (∑ j, Fin.snoc (α := fun _ => Fin m → ℝ)
      (fun i j => if j = i then 1 else 0)
      (fun j => if j = lastIdx m then 1 else 0) (Fin.last m) j * x j) + (0 : ℝ) = x (lastIdx m)
  rw [Fin.snoc_last]
  show (∑ j, (if j = lastIdx m then (1 : ℝ) else 0) * x j) + 0 = x (lastIdx m)
  rw [delta_row_sum (lastIdx m) x, add_zero]

end Affine

/-- Duplicating the last coordinate does not change the maximum. -/
theorem MAX_comp_dupLast {m : ℕ} [NeZero m] (x : Fin m → ℝ) :
    MAX (m + 1) ((Affine.dupLast m).eval x) = MAX m x := by
  rw [MAX_succ]
  have hcast : (fun i : Fin m => (Affine.dupLast m).eval x i.castSucc) = x := by
    funext i
    exact Affine.dupLast_eval_castSucc x i
  rw [hcast, Affine.dupLast_eval_last, max_eq_left (le_MAX m x (lastIdx m))]

/-- **Monotonicity in the arity.**  If `MAX_{m+1}` is computable with `k` hidden layers,
then so is `MAX_m`: precompose with the duplication of the last coordinate, which costs
no hidden layers.  (Contrapositive: a lower bound for `MAX_m` transfers upward to
`MAX_{m+1}`.) -/
theorem MAX_mem_reluClass_of_succ {m k : ℕ} [NeZero m]
    (h : MAX (m + 1) ∈ ReLUClass (m + 1) k) : MAX m ∈ ReLUClass m k := by
  have h2 := comp_affine_mem_reluClass h (Affine.dupLast m)
  have e : (fun x => MAX (m + 1) ((Affine.dupLast m).eval x)) = MAX m := by
    funext x
    exact MAX_comp_dupLast x
  rw [e] at h2
  exact h2

end MaxNN
