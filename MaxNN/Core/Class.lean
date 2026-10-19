import MaxNN.Core.Network
import Mathlib.Tactic.Linarith

/-!
# `ReLUClass n k` — the functions computable with `k` hidden layers

`ReLUClass n k` (the literature's `ReLU_{n,k}`) is the set of scalar functions on `ℝ^n`
computable *exactly* by a ReLU network with `k` hidden layers, finite (arbitrary) widths
and arbitrary real weights.

The closure lemmas proved here are what make identities such as the paper's nine-term
`MAX_5` certificate legitimate networks:

* `reluClass_mono` — the classes grow with `k` (identity padding);
* `linComb_mem_reluClass` (and `add`/`smul`/`neg`/`sub`/`sum` corollaries) — each class is
  a vector space: networks run in parallel and are combined in the output affine layer;
* `max_mem_reluClass` — a pointwise `max` of two class-`k` functions lies in class `k+1`;
* `comp_affine_mem_reluClass` — affine precomposition costs no hidden layers;
* `affine_mem_reluClass`, `coord_mem_reluClass`, `const_mem_reluClass` — the base cases.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- `ReLUClass n k` (= `ReLU_{n,k}`): the scalar functions on `ℝ^n` computable exactly by
some ReLU network with `k` hidden layers (finite widths, arbitrary real weights).
By `reluClass_mono` these classes grow with `k`, so membership here coincides with
"computable with at most `k` hidden layers". -/
def ReLUClass (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ N : ReLUNet n 1 k, N.Computes f }

theorem mem_reluClass_iff {n k : ℕ} {f : (Fin n → ℝ) → ℝ} :
    f ∈ ReLUClass n k ↔ ∃ N : ReLUNet n 1 k, N.Computes f := Iff.rfl

/-- Deeper classes contain shallower ones, by identity padding (`ReLUNet.padBy`). -/
theorem reluClass_mono {n k l : ℕ} (hkl : k ≤ l) : ReLUClass n k ⊆ ReLUClass n l := by
  intro f hf
  obtain ⟨N, hN⟩ := hf
  obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, (Nat.add_sub_cancel' hkl).symm⟩
  exact ⟨N.padBy d, fun x => by rw [ReLUNet.padBy_eval]; exact hN x⟩

/-! ## Base cases: affine functions need no hidden layer -/

/-- Affine functions lie in `ReLUClass n 0`. -/
theorem affine_mem_reluClass {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    (fun x => (∑ j, a j * x j) + c) ∈ ReLUClass n 0 :=
  ⟨ReLUNet.affine ⟨fun _ => a, fun _ => c⟩, fun _ => rfl⟩

/-- Coordinate functions lie in `ReLUClass n 0`. -/
theorem coord_mem_reluClass {n : ℕ} (i : Fin n) : (fun x => x i) ∈ ReLUClass n 0 := by
  refine ⟨ReLUNet.affine ⟨fun _ j => if j = i then 1 else 0, fun _ => 0⟩, fun x => ?_⟩
  show (∑ j, (if j = i then (1 : ℝ) else 0) * x j) + 0 = x i
  rw [Affine.delta_row_sum i x, add_zero]

/-- Constant functions lie in `ReLUClass n 0`. -/
theorem const_mem_reluClass {n : ℕ} (c : ℝ) : (fun _ => c) ∈ ReLUClass n 0 := by
  refine ⟨ReLUNet.affine ⟨fun _ _ => 0, fun _ => c⟩, fun x => ?_⟩
  show (∑ j, (0 : ℝ) * x j) + c = c
  rw [Finset.sum_congr rfl fun j _ => zero_mul (x j), Finset.sum_const_zero, zero_add]

/-! ## The vector-space structure -/

/-- **`ReLUClass n k` is closed under linear combinations.**  The two networks run in
parallel (`ReLUNet.pair`) and are combined in the output affine layer.  This is what
makes a signed sum of `max`-terms a legitimate network. -/
theorem linComb_mem_reluClass {n k : ℕ} {f g : (Fin n → ℝ) → ℝ} (c₁ c₂ : ℝ)
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => c₁ * f x + c₂ * g x) ∈ ReLUClass n k := by
  obtain ⟨Nf, hNf⟩ := hf
  obtain ⟨Ng, hNg⟩ := hg
  refine ⟨(Nf.pair Ng).postcomp (Affine.row2 c₁ c₂), fun x => ?_⟩
  rw [ReLUNet.postcomp_eval, ReLUNet.pair_eval, Affine.row2_eval,
    Fin.append_left, Fin.append_right, hNf x, hNg x]

theorem add_mem_reluClass {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => f x + g x) ∈ ReLUClass n k := by
  have h := linComb_mem_reluClass 1 1 hf hg
  have e : (fun x => (1 : ℝ) * f x + 1 * g x) = fun x => f x + g x := by
    funext x
    rw [one_mul, one_mul]
  rw [e] at h
  exact h

theorem smul_mem_reluClass {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (c : ℝ)
    (hf : f ∈ ReLUClass n k) : (fun x => c * f x) ∈ ReLUClass n k := by
  have h := linComb_mem_reluClass c 0 hf hf
  have e : (fun x => c * f x + 0 * f x) = fun x => c * f x := by
    funext x
    rw [zero_mul, add_zero]
  rw [e] at h
  exact h

theorem neg_mem_reluClass {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) : (fun x => -(f x)) ∈ ReLUClass n k := by
  have h := smul_mem_reluClass (-1) hf
  have e : (fun x => (-1 : ℝ) * f x) = fun x => -(f x) := by
    funext x
    rw [neg_one_mul]
  rw [e] at h
  exact h

theorem sub_mem_reluClass {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => f x - g x) ∈ ReLUClass n k := by
  have h := linComb_mem_reluClass 1 (-1) hf hg
  have e : (fun x => (1 : ℝ) * f x + (-1) * g x) = fun x => f x - g x := by
    funext x
    rw [one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [e] at h
  exact h

/-- Closure under finite sums. -/
theorem sum_mem_reluClass {ι : Type _} [DecidableEq ι] {n k : ℕ} (s : Finset ι)
    (F : ι → (Fin n → ℝ) → ℝ) (hF : ∀ i ∈ s, F i ∈ ReLUClass n k) :
    (fun x => ∑ i in s, F i x) ∈ ReLUClass n k := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x : Fin n → ℝ => ∑ i in (∅ : Finset ι), F i x) = fun _ => (0 : ℝ) := by
      funext x
      exact Finset.sum_empty
    rw [e]
    exact reluClass_mono (Nat.zero_le k) (const_mem_reluClass 0)
  · intro a s ha ih hF
    have e : (fun x : Fin n → ℝ => ∑ i in insert a s, F i x)
        = fun x => F a x + ∑ i in s, F i x := by
      funext x
      exact Finset.sum_insert ha
    rw [e]
    exact add_mem_reluClass (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-! ## One more layer computes a pointwise maximum -/

/-- **A pointwise `max` of two class-`k` functions lies in class `k+1`**, via
`max a b = relu (b - a) + relu a - relu (-a)`: run the two networks in parallel, form
`(b - a, a, -a)` affinely, `relu`, and recombine in the output layer. -/
theorem max_mem_reluClass {n k : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : f ∈ ReLUClass n k) (hg : g ∈ ReLUClass n k) :
    (fun x => max (f x) (g x)) ∈ ReLUClass n (k + 1) := by
  obtain ⟨Nf, hNf⟩ := hf
  obtain ⟨Ng, hNg⟩ := hg
  refine ⟨((Nf.pair Ng).postcomp
      ((Affine.row2 (-1) 1).stack ((Affine.row2 1 0).stack (Affine.row2 (-1) 0)))).addReluLayer
      (Affine.row3 1 1 (-1)), fun x => ?_⟩
  rw [ReLUNet.addReluLayer_eval, ReLUNet.postcomp_eval, ReLUNet.pair_eval,
    Affine.row3_eval]
  have h1 : ((Affine.row2 (-1) 1).stack ((Affine.row2 1 0).stack (Affine.row2 (-1) 0))).eval
      (Fin.append (Nf.eval x) (Ng.eval x)) (Fin.castAdd (1 + 1) 0) = g x - f x := by
    rw [Affine.stack_eval_castAdd, Affine.row2_eval, Fin.append_left, Fin.append_right,
      hNf x, hNg x, neg_one_mul, one_mul, neg_add_eq_sub]
  have h2 : ((Affine.row2 (-1) 1).stack ((Affine.row2 1 0).stack (Affine.row2 (-1) 0))).eval
      (Fin.append (Nf.eval x) (Ng.eval x)) (Fin.natAdd 1 (Fin.castAdd 1 0)) = f x := by
    rw [Affine.stack_eval_natAdd, Affine.stack_eval_castAdd, Affine.row2_eval,
      Fin.append_left, Fin.append_right, hNf x, hNg x, one_mul, zero_mul, add_zero]
  have h3 : ((Affine.row2 (-1) 1).stack ((Affine.row2 1 0).stack (Affine.row2 (-1) 0))).eval
      (Fin.append (Nf.eval x) (Ng.eval x)) (Fin.natAdd 1 (Fin.natAdd 1 0)) = -(f x) := by
    rw [Affine.stack_eval_natAdd, Affine.stack_eval_natAdd, Affine.row2_eval,
      Fin.append_left, Fin.append_right, hNf x, hNg x, neg_one_mul, zero_mul, add_zero]
  rw [h1, h2, h3, one_mul, one_mul, neg_one_mul]
  show relu (g x - f x) + (relu (f x) + -relu (-f x)) = max (f x) (g x)
  rw [max_eq_relu_add (f x) (g x)]
  have h4 := relu_sub_relu_neg (f x)
  linarith

/-! ## Affine precomposition costs no hidden layers -/

/-- Precomposing a class-`k` function with an affine map stays in class `k`. -/
theorem comp_affine_mem_reluClass {m n k : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hf : f ∈ ReLUClass m k) (T : Affine n m) :
    (fun x => f (T.eval x)) ∈ ReLUClass n k := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨N.precomp T, fun x => by rw [ReLUNet.precomp_eval]; exact hN (T.eval x)⟩

/-! ## General composition: hidden layers add -/

/-- **Composition theorem.**  Feeding `p` class-`j` functions into a class-`k` function
costs `k + j` hidden layers: the inner networks run in parallel (`ReLUNet.pairMany`) and
the outer network is appended (`ReLUNet.seqComp`).

Proof recipe: `rcases p` — for `p = 0` precompose `f`'s network with the empty affine map
`⟨fun i => i.elim0, fun i => i.elim0⟩ : Affine m 0` and lift with
`reluClass_mono (Nat.le_add_right k j)`, using that any two functions `Fin 0 → ℝ` are equal
(`funext fun i => i.elim0`); for `p = p' + 1` take networks `Nf` for `f` and
`Ng i := (hg i).choose` for the `g i`, form `(ReLUNet.pairMany Ng).seqComp Nf`, and compute
with `seqComp_eval`, `pairMany_eval`, the `Computes` facts, and a `congrArg` to rewrite the
inner argument. -/
theorem comp_mem_reluClass {p m j k : ℕ} {f : (Fin p → ℝ) → ℝ}
    {g : Fin p → (Fin m → ℝ) → ℝ}
    (hf : f ∈ ReLUClass p k) (hg : ∀ i, g i ∈ ReLUClass m j) :
    (fun x => f (fun i => g i x)) ∈ ReLUClass m (k + j) := by
  rcases p with _ | p'
  · obtain ⟨N, hN⟩ := hf
    refine reluClass_mono (Nat.le_add_right k j)
      ⟨N.precomp ⟨fun i => i.elim0, fun i => i.elim0⟩, fun x => ?_⟩
    rw [ReLUNet.precomp_eval, hN]
    exact congrArg f (funext fun i => i.elim0)
  · obtain ⟨Nf, hNf⟩ := hf
    choose Ng hNg using hg
    refine ⟨(ReLUNet.pairMany Ng).seqComp Nf, fun x => ?_⟩
    rw [ReLUNet.seqComp_eval, ReLUNet.pairMany_eval,
      show (fun i => (Ng i).eval x 0) = fun i => g i x from funext fun i => hNg i x]
    exact hNf (fun i => g i x)

end MaxNN
