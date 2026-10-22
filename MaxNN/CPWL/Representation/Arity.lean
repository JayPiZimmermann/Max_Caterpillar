import MaxNN.CPWL.Representation.Arity.Reduce
import MaxNN.CPWL.Representation.Arity.Lift
import MaxNN.CPWL.Representation.DiffConvex
import MaxNN.CPWL.Hinging
import Mathlib.LinearAlgebra.Finsupp

/-!
# The arity-`(d+1)` decomposition: `CPWL d` is spanned by maxima of `d+1` affine functions

Stage (iii) of the hinging-representation programme, and the input the machine-checked
depth ladder was missing: **every continuous piecewise-linear function on `ℝ^d` is a finite
real combination of maxima of at most `d+1` affine functions** (Wang–Sun 2005; geometrically,
Bakaev–Brunck–Hertrich–Stade–Yehudayoff 2025, Lemma 9 applied to a triangulation).

* `mem_span_maxOfAffineArityLE_of_isMaxOfAffine` — a maximum of finitely many affine
  functions on `ℝ^d` lies in the `ℝ`-span of `MaxOfAffineArityLE d (d+1)`;
* `mem_span_maxOfAffineArityLE_of_mem_cpwl` — so does every `f ∈ CPWL d`, via the
  difference-of-convex decomposition (`diffConvex_of_mem_cpwl`);
* `exists_sum_maxOfAffineArityLE_of_mem_cpwl` — the explicit form
  `f = ∑ t, c t * h t` with each `h t` a maximum of at most `d+1` affine functions;
* `hasHingingRep_of_mem_cpwl` — the Wang–Sun normal form `HasHingingRep d f`: a `±1`-signed
  sum of maxima of exactly `d+1` affine functions (`MaxNN/CPWL/Hinging.lean`), whose
  transfer lemma `mem_reluClass_of_hasHingingRep` was waiting for exactly this input.

The proof is elementary (no Euler characteristic, no valuation theory): among `d+2` affine
functions the gradients are affinely dependent (`Arity/Dependence.lean`), and the resulting
dominating subset makes an inclusion–exclusion identity for maxima hold pointwise
(`Arity/InclusionExclusion.lean`); strong induction on the number of functions finishes
(`Arity/Reduce.lean`).

Consequences for depth — **rung `d+1` is exactly dimension `d`**:

* `cpwl_subset_reluClass_of_MAX_succ_mem` — if `MAX (d+1)` has `k` hidden layers then every
  CPWL function on `ℝ^d` has `k` hidden layers;
* `MAX_succ_mem_reluClass_of_cpwl_subset` — conversely, `MAX (d+1)` inherits any depth bound
  enjoyed by all of `CPWL d` (`Arity/Lift.lean`);
* `cpwl_eq_reluClass_iff_MAX_succ_mem` — `CPWL d = ReLUClass d k ↔ MAX (d+1) ∈ ReLUClass (d+1) k`.

In particular (`MaxNN/CPWL/Targets/LowDimension.lean`), with the flagship
`max_two_hidden_layers_of_le_eight`, `CPWL d = ReLUClass d 2` for every `d ≤ 7`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- A maximum of finitely many affine functions on `ℝ^d` lies in the span of the maxima of
at most `d+1` affine functions. -/
theorem mem_span_maxOfAffineArityLE_of_isMaxOfAffine {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMaxOfAffine d f) : f ∈ Submodule.span ℝ (MaxOfAffineArityLE d (d + 1)) := by
  obtain ⟨r, g, hrep⟩ := hf
  have e : f = fun x => maxOn Finset.univ fun j => (g j).eval x := by
    funext x
    rw [hrep x, maxOn_univ]
  rw [e]
  exact maxOn_mem_span_maxOfAffineArityLE g _ Finset.univ rfl Finset.univ_nonempty

/-- **Arity-`(d+1)` decomposition.**  Every CPWL function on `ℝ^d` lies in the `ℝ`-span of
the maxima of at most `d+1` affine functions. -/
theorem mem_span_maxOfAffineArityLE_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) : f ∈ Submodule.span ℝ (MaxOfAffineArityLE d (d + 1)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := diffConvex_of_mem_cpwl hf
  have e : f = p - q := funext fun x => hpq x
  rw [e]
  exact Submodule.sub_mem _ (mem_span_maxOfAffineArityLE_of_isMaxOfAffine hp)
    (mem_span_maxOfAffineArityLE_of_isMaxOfAffine hq)

/-- **Arity-`(d+1)` decomposition, explicit form.**  Every CPWL function on `ℝ^d` is a finite
real combination `f = ∑ t, c t * h t` of functions `h t`, each a maximum of at most `d+1`
affine functions. -/
theorem exists_sum_maxOfAffineArityLE_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ CPWL d) :
    ∃ (r : ℕ) (c : Fin r → ℝ) (h : Fin r → (Fin d → ℝ) → ℝ),
      (∀ t, ∃ m : ℕ, ∃ _ : NeZero m, m ≤ d + 1 ∧ IsMaxOfAffineArity d m (h t)) ∧
      ∀ x, f x = ∑ t, c t * h t x := by
  obtain ⟨r, c, h, hsum⟩ := mem_span_set'.mp (mem_span_maxOfAffineArityLE_of_mem_cpwl hf)
  refine ⟨r, c, fun t => (h t : (Fin d → ℝ) → ℝ), fun t => (h t).2, fun x => ?_⟩
  rw [← hsum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun t _ => by rw [Pi.smul_apply, smul_eq_mul]

/-- **Wang–Sun hinging representation.**  Every CPWL function on `ℝ^d` is a `±1`-signed sum
of maxima of exactly `d+1` affine functions — `HasHingingRep d f` in the project's
vocabulary (`MaxNN/CPWL/Hinging.lean`).  Real coefficients are absorbed into the affine
functions (`MAX_smul`), and maxima of fewer than `d+1` functions are padded by repetition
(`MAX_eq_MAX_padIndex`). -/
theorem hasHingingRep_of_mem_cpwl {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : f ∈ CPWL d) :
    HasHingingRep d f := by
  obtain ⟨r, c, h, harity, hrep⟩ := exists_sum_maxOfAffineArityLE_of_mem_cpwl hf
  have harity' : ∀ t, ∃ m : ℕ, ∃ _ : NeZero m, m ≤ d + 1 ∧
      ∃ g : Fin m → AffineFn d, ∀ x, h t x = MAX m fun s => (g s).eval x := harity
  choose m hm0 hmle g hg using harity'
  refine ⟨r, fun t => if c t < 0 then -1 else 1,
    fun t => Affine.ofRows fun s : Fin (d + 1) =>
      AffineFn.linComb |c t| 0 (g t (@padIndex (m t) (d + 1) (hm0 t) s))
        (g t (@padIndex (m t) (d + 1) (hm0 t) s)),
    fun t => ?_, fun x => ?_⟩
  · show (if c t < 0 then (-1 : ℝ) else 1) = 1 ∨ (if c t < 0 then (-1 : ℝ) else 1) = -1
    by_cases hc : c t < 0
    · right
      rw [if_pos hc]
    · left
      rw [if_neg hc]
  · rw [hrep x]
    refine Finset.sum_congr rfl fun t _ => ?_
    haveI := hm0 t
    rw [hg t x, Affine.ofRows_eval]
    have e1 : (fun s : Fin (d + 1) =>
        (AffineFn.linComb |c t| 0 (g t (@padIndex (m t) (d + 1) (hm0 t) s))
          (g t (@padIndex (m t) (d + 1) (hm0 t) s))).eval x)
        = fun s => |c t| * (g t (@padIndex (m t) (d + 1) (hm0 t) s)).eval x := by
      funext s
      rw [AffineFn.linComb_eval, zero_mul, add_zero]
    rw [e1, ← MAX_eq_MAX_padIndex (hmle t) (fun s => |c t| * (g t s).eval x),
      MAX_smul (abs_nonneg (c t))]
    show c t * MAX (m t) (fun s => (g t s).eval x)
      = (if c t < 0 then (-1 : ℝ) else 1) * (|c t| * MAX (m t) fun s => (g t s).eval x)
    by_cases hc : c t < 0
    · rw [if_pos hc, abs_of_neg hc]
      ring
    · rw [if_neg hc, abs_of_nonneg (not_lt.mp hc)]
      ring

/-! ## Depth transfer: rung `d+1` is exactly dimension `d` -/

/-- **Wang–Sun transfer.**  If `MAX (d+1)` is computable with `k` hidden layers, then so is
every continuous piecewise-linear function on `ℝ^d`. -/
theorem cpwl_subset_reluClass_of_MAX_succ_mem {d k : ℕ}
    (hMAX : MAX (d + 1) ∈ ReLUClass (d + 1) k) : CPWL d ⊆ ReLUClass d k := by
  intro f hf
  obtain ⟨r, c, h, harity, hrep⟩ := exists_sum_maxOfAffineArityLE_of_mem_cpwl hf
  have hterm : ∀ t ∈ (Finset.univ : Finset (Fin r)),
      (fun x => c t * h t x) ∈ ReLUClass d k := by
    intro t _
    obtain ⟨m, hm0, hmle, hmax⟩ := harity t
    exact smul_mem_reluClass (c t)
      (mem_reluClass_of_isMaxOfAffineArity hmax (Bridge.MAX_mem_reluClass_of_le hmle hMAX))
  have hs := sum_mem_reluClass Finset.univ (fun t x => c t * h t x) hterm
  have e : (fun x => ∑ t in Finset.univ, c t * h t x) = f := funext fun x => (hrep x).symm
  rw [e] at hs
  exact hs

/-- **Converse transfer.**  If every continuous piecewise-linear function on `ℝ^d` is
computable with `k` hidden layers, then so is `MAX (d+1)`: it is `max(x - x_{d+1}, 0) + x_{d+1}`,
one affine precomposition and one affine output term away from the CPWL function
`max(y, 0)` on `ℝ^d`. -/
theorem MAX_succ_mem_reluClass_of_cpwl_subset {d k : ℕ} (h : CPWL d ⊆ ReLUClass d k) :
    MAX (d + 1) ∈ ReLUClass (d + 1) k := by
  have hF : (fun y : Fin d → ℝ => MAX (d + 1) fun t => (AffineFn.coordOrZero d t).eval y)
      ∈ CPWL d :=
    mem_cpwl_of_isMaxOfAffine ⟨d, AffineFn.coordOrZero d, fun _ => rfl⟩
  have e : MAX (d + 1) = fun x : Fin (d + 1) → ℝ =>
      MAX (d + 1) (fun t => (AffineFn.coordOrZero d t).eval ((Affine.subLast d).eval x))
        + ((∑ j, (if j = Fin.last d then (1 : ℝ) else 0) * x j) + 0) := by
    funext x
    rw [Affine.delta_row_sum, add_zero]
    exact MAX_succ_eq_coordOrZero_subLast x
  rw [e]
  exact add_mem_reluClass (comp_affine_mem_reluClass (h hF) (Affine.subLast d))
    (reluClass_mono (Nat.zero_le k)
      (affine_mem_reluClass (fun j => if j = Fin.last d then (1 : ℝ) else 0) 0))

/-- **Rung `d+1` is exactly dimension `d`.**  All of `CPWL d` is computable with `k` hidden
layers if and only if `MAX (d+1)` is.  (The inclusion `ReLUClass d k ⊆ CPWL d` is
`reluClass_subset_cpwl`.) -/
theorem cpwl_eq_reluClass_iff_MAX_succ_mem {d k : ℕ} :
    CPWL d = ReLUClass d k ↔ MAX (d + 1) ∈ ReLUClass (d + 1) k := by
  constructor
  · intro h
    exact MAX_succ_mem_reluClass_of_cpwl_subset (le_of_eq h)
  · intro h
    exact Set.Subset.antisymm (cpwl_subset_reluClass_of_MAX_succ_mem h) (reluClass_subset_cpwl d k)

end MaxNN
