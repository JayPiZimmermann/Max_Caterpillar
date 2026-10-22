import MaxNN.CPWL.Conditional.Finitary.Bundle
import MaxNN.CPWL.Representation.ConvexMax
import MaxNN.GeneralN.Bridge.Links.ArityIterate

/-!
# Finitary conditional collapse: a depth bound for one `MAX` arity transfers

The arity-graded refinement of `IsMaxOfAffine`: `IsMaxOfAffineArity d m f` says `f` is
the pointwise maximum of exactly `m` (a fixed, positive number of) affine functions.

Two transfer theorems, each conditional on a depth upper bound for a **single** `MAX`
arity:

* `mem_reluClass_of_isMaxOfAffineArity` — a maximum of `m` affine functions inherits any
  depth bound of `MAX m`: it *is* `MAX m` precomposed with one affine layer
  (`Affine.ofRows`), and affine precomposition costs no hidden layers.
* `mem_reluClass_of_diff_isMaxOfAffineArity` — a difference `f = p - q` of maxima of
  `m₁` and `m₂` affine functions inherits any depth bound of `MAX m` for a single
  `m ≥ max m₁ m₂`: arity monotonicity (`Bridge.MAX_mem_reluClass_of_le`) feeds both
  parts, and the output layer absorbs the difference (`sub_mem_reluClass`).

Combined with the difference-of-convex decomposition (`diffConvex_of_mem_cpwl`), these
yield the conditional collapse of the depth hierarchy
(`MaxNN/CPWL/Conditional/Collapse.lean`) and the per-function arity transfer
(`MaxNN/CPWL/Conditional/ArityBound.lean`).

Edge cases are honest: `m = 1` (`f` affine) is included, `m = 0` (an empty maximum) is
excluded by the `NeZero` hypothesis — exactly the hypothesis needed to state `MAX m`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- `f` is the pointwise maximum of exactly `m` affine functions (`m ≥ 1`).  The
arity-graded refinement of `IsMaxOfAffine`. -/
def IsMaxOfAffineArity (d m : ℕ) [NeZero m] (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ g : Fin m → AffineFn d, ∀ x, f x = MAX m fun t => (g t).eval x

/-- `IsMaxOfAffine` is exactly `IsMaxOfAffineArity` at some positive arity. -/
theorem isMaxOfAffine_iff_exists_arity {d : ℕ} {f : (Fin d → ℝ) → ℝ} :
    IsMaxOfAffine d f ↔ ∃ r : ℕ, IsMaxOfAffineArity d (r + 1) f :=
  Iff.rfl

/-- **Single-arity transfer.**  A maximum of `m` affine functions is `MAX m`
precomposed with one affine layer, so it inherits any depth upper bound of `MAX m`:
if `MAX m` is computable with `k` hidden layers, so is `f`. -/
theorem mem_reluClass_of_isMaxOfAffineArity {d m k : ℕ} [NeZero m]
    {f : (Fin d → ℝ) → ℝ} (hf : IsMaxOfAffineArity d m f)
    (hMAX : MAX m ∈ ReLUClass m k) : f ∈ ReLUClass d k := by
  obtain ⟨g, hrep⟩ := hf
  have h := comp_affine_mem_reluClass hMAX (Affine.ofRows g)
  have e : (fun x => MAX m ((Affine.ofRows g).eval x)) = f := by
    funext x
    rw [Affine.ofRows_eval g x]
    exact (hrep x).symm
  rw [e] at h
  exact h

/-- **Finitary conditional collapse.**  If `f = p - q` with `p` a maximum of `m₁` and
`q` a maximum of `m₂` affine functions, then a depth bound for the **single** arity
`MAX m`, for any `m ≥ max m₁ m₂`, forces the same depth bound for `f`: arity
monotonicity feeds both convex parts, and the output layer absorbs the difference. -/
theorem mem_reluClass_of_diff_isMaxOfAffineArity {d k m₁ m₂ m : ℕ}
    [NeZero m₁] [NeZero m₂] [NeZero m] {f p q : (Fin d → ℝ) → ℝ}
    (hp : IsMaxOfAffineArity d m₁ p) (hq : IsMaxOfAffineArity d m₂ q)
    (hf : ∀ x, f x = p x - q x) (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m)
    (hMAX : MAX m ∈ ReLUClass m k) : f ∈ ReLUClass d k := by
  have hpk : p ∈ ReLUClass d k :=
    mem_reluClass_of_isMaxOfAffineArity hp (Bridge.MAX_mem_reluClass_of_le h₁ hMAX)
  have hqk : q ∈ ReLUClass d k :=
    mem_reluClass_of_isMaxOfAffineArity hq (Bridge.MAX_mem_reluClass_of_le h₂ hMAX)
  have h := sub_mem_reluClass hpk hqk
  have e : (fun x => p x - q x) = f := funext fun x => (hf x).symm
  rw [e] at h
  exact h

end MaxNN
