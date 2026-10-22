import MaxNN.Core.Monotone

/-!
# Link B5 (iteration) — arity monotonicity packaged for a range

`MAX_mem_reluClass_of_succ` (`Core/Monotone.lean`) drops the arity by one, keeping the number of
hidden layers `k` fixed, by duplicating the last coordinate.  Iterating it packages the whole
downward range: from `MAX N ∈ ReLUClass N k` we obtain `MAX m ∈ ReLUClass m k` for every
`1 ≤ m ≤ N`.

Combined with the critical-arity input `MAX (2D+2) ∈ ReLUClass (2D+2) 2` (for every `D`), this
gives `MAX m ∈ ReLUClass m 2` for every `m`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Bridge

/-- `m + d` is nonzero whenever `m` is; supplies the `NeZero` needed to even state `MAX (m + d)`. -/
instance neZero_add_left {m d : ℕ} [NeZero m] : NeZero (m + d) :=
  ⟨fun h => NeZero.ne m (Nat.eq_zero_of_add_eq_zero_right h)⟩

/-- Downward iteration of `MAX_mem_reluClass_of_succ` by an additive step `d`. -/
theorem MAX_mem_reluClass_of_add {m d k : ℕ} [NeZero m]
    (h : MAX (m + d) ∈ ReLUClass (m + d) k) : MAX m ∈ ReLUClass m k := by
  induction d with
  | zero => exact h
  | succ e ih =>
    -- `m + (e+1)` is definitionally `(m + e) + 1`, so `h` feeds the successor step directly.
    exact ih (MAX_mem_reluClass_of_succ h)

/-- **Link B5 (iteration).**  If `MAX N` is computable with `k` hidden layers, then so is `MAX m`
for every positive `m ≤ N`. -/
theorem MAX_mem_reluClass_of_le {m N k : ℕ} [NeZero m] [NeZero N] (hle : m ≤ N)
    (h : MAX N ∈ ReLUClass N k) : MAX m ∈ ReLUClass m k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact MAX_mem_reluClass_of_add h

end Bridge

end MaxNN
