import MaxNN.CPWL.Closure
import MaxNN.Core.Class

/-!
# ReLU networks compute CPWL functions: `ReLUClass n k ⊆ CPWL n`

The bridge from the network world (`Core/Class.lean`) to the CPWL world: everything a
ReLU network of any depth computes is a continuous piecewise-linear function.

The proof is a structural induction over `ReLUNet` in a strengthened form
(`ReLUNet.eval_comp_mem_cpwl`): if every input line `v l` fed to the network is CPWL,
then every output of the network is CPWL.  A hidden layer turns the CPWL inputs into
`relu (affine combination) = max 0 (affine combination)`, which stays CPWL by the
closure lemmas — no piecewise-cover surgery is needed beyond the binary bricks.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- Structural induction workhorse: feeding CPWL functions into a ReLU network yields
CPWL outputs. -/
theorem ReLUNet.eval_comp_mem_cpwl {d : ℕ} :
    ∀ {m n k : ℕ} (N : ReLUNet m n k) (v : Fin m → (Fin d → ℝ) → ℝ),
      (∀ l, v l ∈ CPWL d) → ∀ i : Fin n,
      (fun x => N.eval (fun l => v l x) i) ∈ CPWL d := by
  intro m n k N
  induction N with
  | affine T =>
    intro v hv i
    exact affineComb_mem_cpwl (T.A i) (T.b i) hv
  | layer T _ ih =>
    intro v hv i
    have hw : ∀ h, (fun x => relu ((∑ l, T.A h l * v l x) + T.b h)) ∈ CPWL d := by
      intro h
      have hmax := max_mem_cpwl (const_mem_cpwl (d := d) 0)
        (affineComb_mem_cpwl (T.A h) (T.b h) hv)
      exact hmax
    exact ih (fun h => fun x => relu ((∑ l, T.A h l * v l x) + T.b h)) hw i

/-- **Every function computed by a ReLU network (any depth) is CPWL.** -/
theorem reluClass_subset_cpwl (n k : ℕ) : ReLUClass n k ⊆ CPWL n := by
  intro f hf
  obtain ⟨N, hN⟩ := hf
  have h : (fun x : Fin n → ℝ => N.eval (fun l => x l) 0) ∈ CPWL n :=
    N.eval_comp_mem_cpwl (fun l => fun x => x l) (fun l => coord_mem_cpwl l) 0
  have e : (fun x : Fin n → ℝ => N.eval (fun l => x l) 0) = f := funext fun x => hN x
  rw [e] at h
  exact h

/-- A ReLU network's scalar output is continuous. -/
theorem continuous_of_mem_reluClass {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) : Continuous f :=
  continuous_of_mem_cpwl (reluClass_subset_cpwl n k hf)

end MaxNN
