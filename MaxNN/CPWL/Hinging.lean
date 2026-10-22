import MaxNN.CPWL.Hinging.MaxPieces
import MaxNN.Core.Class

/-!
# Hinging representations and the depth-transfer lemma

`HasHingingRep d f`: the function `f : ℝ^d → ℝ` is a finite `±1`-signed sum of hinges
`MAX (d+1) ∘ A_t` with affine `A_t : ℝ^d → ℝ^{d+1}`.

The **transfer lemma** (`mem_reluClass_of_hasHingingRep`): a depth upper bound for
`MAX (d+1)` transfers to every function with a hinging representation on `ℝ^d` —
affine precomposition costs no hidden layers (`comp_affine_mem_reluClass`) and the
signed sum is absorbed into the output layers (`sum_mem_reluClass`,
`smul_mem_reluClass`).  In particular, once every CPWL function on `ℝ^d` is known to
have a hinging representation (the representation theorem, see
`MaxNN/CPWL/Representation/`), any answer to "how many hidden layers does `MAX (d+1)`
need?" answers the same question for all of `CPWL d` at once.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- `f` has a **hinging representation** of arity `d+1`: a finite `±1`-signed sum
`f = ∑ t, ε t * MAX (d+1) (A t ·)` of maxima of `d+1` affine functions. -/
def HasHingingRep (d : ℕ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ (r : ℕ) (ε : Fin r → ℝ) (A : Fin r → Affine d (d + 1)),
    (∀ t, ε t = 1 ∨ ε t = -1) ∧
    ∀ x, f x = ∑ t, ε t * MAX (d + 1) ((A t).eval x)

/-- **Transfer lemma.**  If `MAX (d+1)` is computable with `k` hidden layers, then so
is every function on `ℝ^d` with a hinging representation. -/
theorem mem_reluClass_of_hasHingingRep {d k : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : HasHingingRep d f) (hMAX : MAX (d + 1) ∈ ReLUClass (d + 1) k) :
    f ∈ ReLUClass d k := by
  obtain ⟨r, ε, A, _, hrep⟩ := hf
  have hsum : (fun x => ∑ t, ε t * MAX (d + 1) ((A t).eval x)) ∈ ReLUClass d k :=
    sum_mem_reluClass Finset.univ (fun t => fun x => ε t * MAX (d + 1) ((A t).eval x))
      fun t _ => smul_mem_reluClass (ε t) (comp_affine_mem_reluClass hMAX (A t))
  have e : f = fun x => ∑ t, ε t * MAX (d + 1) ((A t).eval x) := funext hrep
  rw [e]
  exact hsum

end MaxNN
