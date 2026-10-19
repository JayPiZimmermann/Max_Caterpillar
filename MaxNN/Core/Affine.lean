import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Affine maps `ℝ^m → ℝ^n` as finite data

An `Affine m n` is a coefficient matrix `A : Fin n → Fin m → ℝ` together with a bias
vector `b : Fin n → ℝ`; it evaluates to `x ↦ A x + b` (`Affine.eval`).  These are the
layers of a ReLU network (`Core/Network.lean`).

Besides evaluation, this file provides exactly the building blocks that network surgery
needs — composition, identity, negation, block stacking, the two block projections, and
the "difference of the two halves" map used to carry a value unchanged through a `relu`
layer — each with its evaluation lemma.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators Finset

/-- An affine map `ℝ^m → ℝ^n` as finite data: a coefficient matrix `A` (output index
first) and a bias vector `b`.  It evaluates to `x ↦ A x + b`; see `Affine.eval`. -/
structure Affine (m n : ℕ) where
  A : Fin n → Fin m → ℝ
  b : Fin n → ℝ

namespace Affine

variable {m m₀ n p : ℕ}

/-- Evaluation: component `i` of `T.eval x` is `(∑ j, T.A i j * x j) + T.b i`. -/
noncomputable def eval (T : Affine m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.b i

/-! ## Identity -/

/-- The identity map, as an affine map. -/
noncomputable def id (m : ℕ) : Affine m m where
  A := fun i j => if j = i then 1 else 0
  b := fun _ => 0

/-- Summing a delta row against `x` picks out one coordinate. -/
theorem delta_row_sum (c : Fin m) (x : Fin m → ℝ) :
    (∑ j, (if j = c then (1 : ℝ) else 0) * x j) = x c := by
  have h : ∀ j : Fin m, (if j = c then (1 : ℝ) else 0) * x j
      = if j = c then x j else 0 := by
    intro j
    rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq' Finset.univ c x,
    if_pos (Finset.mem_univ c)]

theorem id_eval (x : Fin m → ℝ) : (id m).eval x = x := by
  funext i
  unfold eval id
  rw [delta_row_sum i x, add_zero]

/-! ## Negation -/

/-- Componentwise negation. -/
noncomputable def neg (T : Affine m n) : Affine m n where
  A := fun i j => -(T.A i j)
  b := fun i => -(T.b i)

theorem neg_eval (T : Affine m n) (x : Fin m → ℝ) (i : Fin n) :
    T.neg.eval x i = -(T.eval x i) := by
  unfold eval neg
  rw [Finset.sum_congr rfl fun j _ => neg_mul (T.A i j) (x j),
    Finset.sum_neg_distrib, neg_add]

/-! ## Composition -/

/-- Composition, as data: `(S.comp T).eval = S.eval ∘ T.eval` (`comp_eval`). -/
noncomputable def comp (S : Affine n p) (T : Affine m n) : Affine m p where
  A := fun i j => ∑ l, S.A i l * T.A l j
  b := fun i => (∑ l, S.A i l * T.b l) + S.b i

theorem comp_eval (S : Affine n p) (T : Affine m n) (x : Fin m → ℝ) :
    (S.comp T).eval x = S.eval (T.eval x) := by
  funext i
  unfold eval comp
  rw [Finset.sum_congr rfl fun l _ => mul_add (S.A i l) (∑ j, T.A l j * x j) (T.b l),
    Finset.sum_add_distrib,
    Finset.sum_congr rfl fun l _ => Finset.mul_sum,
    Finset.sum_comm,
    Finset.sum_congr rfl fun j _ => (Finset.sum_congr rfl fun l _ =>
      (mul_assoc (S.A i l) (T.A l j) (x j)).symm),
    Finset.sum_congr rfl fun j _ => (Finset.sum_mul).symm,
    add_assoc]

/-! ## Block stacking and block projections -/

/-- Stack two affine maps with a common domain into one with codomain `ℝ^{n+p}`
(block of rows). -/
noncomputable def stack (T : Affine m n) (S : Affine m p) : Affine m (n + p) where
  A := Fin.addCases T.A S.A
  b := Fin.addCases T.b S.b

theorem stack_eval_castAdd (T : Affine m n) (S : Affine m p) (x : Fin m → ℝ) (i : Fin n) :
    (T.stack S).eval x (Fin.castAdd p i) = T.eval x i := by
  show (∑ j, Fin.addCases (motive := fun _ => Fin m → ℝ) T.A S.A (Fin.castAdd p i) j * x j)
      + Fin.addCases (motive := fun _ => ℝ) T.b S.b (Fin.castAdd p i)
    = (∑ j, T.A i j * x j) + T.b i
  rw [Fin.addCases_left, Fin.addCases_left]

theorem stack_eval_natAdd (T : Affine m n) (S : Affine m p) (x : Fin m → ℝ) (i : Fin p) :
    (T.stack S).eval x (Fin.natAdd n i) = S.eval x i := by
  show (∑ j, Fin.addCases (motive := fun _ => Fin m → ℝ) T.A S.A (Fin.natAdd n i) j * x j)
      + Fin.addCases (motive := fun _ => ℝ) T.b S.b (Fin.natAdd n i)
    = (∑ j, S.A i j * x j) + S.b i
  rw [Fin.addCases_right, Fin.addCases_right]

theorem stack_eval (T : Affine m n) (S : Affine m p) (x : Fin m → ℝ) :
    (T.stack S).eval x = Fin.append (T.eval x) (S.eval x) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [stack_eval_castAdd, Fin.append_left]
  · rw [stack_eval_natAdd, Fin.append_right]

/-- Projection onto the first block of coordinates. -/
noncomputable def projFst (n p : ℕ) : Affine (n + p) n where
  A := fun i j => if j = Fin.castAdd p i then 1 else 0
  b := fun _ => 0

theorem projFst_eval (x : Fin (n + p) → ℝ) (i : Fin n) :
    (projFst n p).eval x i = x (Fin.castAdd p i) := by
  unfold eval projFst
  rw [delta_row_sum (Fin.castAdd p i) x, add_zero]

/-- Projection onto the second block of coordinates. -/
noncomputable def projSnd (n p : ℕ) : Affine (n + p) p where
  A := fun i j => if j = Fin.natAdd n i then 1 else 0
  b := fun _ => 0

theorem projSnd_eval (x : Fin (n + p) → ℝ) (i : Fin p) :
    (projSnd n p).eval x i = x (Fin.natAdd n i) := by
  unfold eval projSnd
  rw [delta_row_sum (Fin.natAdd n i) x, add_zero]

/-! ## Difference of the two halves

`diffHalves n` maps `y : ℝ^{n+n}` to the vector of differences
`y (castAdd i) - y (natAdd i)`.  Applied after the layer `x ↦ (relu x, relu (-x))` it
recovers `x` (by `relu_sub_relu_neg`); this is how a value is carried unchanged through
one hidden layer of a network. -/

/-- The affine map `ℝ^{n+n} → ℝ^n`, `y ↦ (y (castAdd i) - y (natAdd i))_i`. -/
noncomputable def diffHalves (n : ℕ) : Affine (n + n) n where
  A := fun i j =>
    (if j = Fin.castAdd n i then 1 else 0) - (if j = Fin.natAdd n i then 1 else 0)
  b := fun _ => 0

theorem diffHalves_eval (y : Fin (n + n) → ℝ) (i : Fin n) :
    (diffHalves n).eval y i = y (Fin.castAdd n i) - y (Fin.natAdd n i) := by
  unfold eval diffHalves
  rw [Finset.sum_congr rfl fun j _ => sub_mul
      (if j = Fin.castAdd n i then (1 : ℝ) else 0)
      (if j = Fin.natAdd n i then (1 : ℝ) else 0) (y j),
    Finset.sum_sub_distrib, delta_row_sum (Fin.castAdd n i) y,
    delta_row_sum (Fin.natAdd n i) y, add_zero]

/-! ## Reindexing -/

/-- The affine map that reindexes coordinates along `φ`: `(reindex φ).eval y i = y (φ i)`.
Generalizes coordinate projections, duplications and permutations. -/
noncomputable def reindex {q q' : ℕ} (φ : Fin q' → Fin q) : Affine q q' where
  A := fun i j => if j = φ i then 1 else 0
  b := fun _ => 0

theorem reindex_eval {q q' : ℕ} (φ : Fin q' → Fin q) (y : Fin q → ℝ) (i : Fin q') :
    (reindex φ).eval y i = y (φ i) := by
  unfold eval reindex
  rw [delta_row_sum (φ i) y, add_zero]

/-! ## Small explicit rows

Output layers that form scalar linear combinations of two or three inputs.  Written with
`Fin.append` so that evaluation against a `Fin.append` of network outputs needs no
numeral-index games. -/

/-- The affine row `(y₁, y₂) ↦ c₁ y₁ + c₂ y₂` on `ℝ^{1+1}`. -/
noncomputable def row2 (c₁ c₂ : ℝ) : Affine (1 + 1) 1 where
  A := fun _ => Fin.append (fun _ : Fin 1 => c₁) fun _ : Fin 1 => c₂
  b := fun _ => 0

theorem row2_eval (c₁ c₂ : ℝ) (y : Fin (1 + 1) → ℝ) :
    (row2 c₁ c₂).eval y 0
      = c₁ * y (Fin.castAdd 1 0) + c₂ * y (Fin.natAdd 1 0) := by
  show (∑ j, Fin.append (fun _ : Fin 1 => c₁) (fun _ : Fin 1 => c₂) j * y j) + (0 : ℝ)
      = c₁ * y (Fin.castAdd 1 0) + c₂ * y (Fin.natAdd 1 0)
  rw [Fin.sum_univ_add, Fin.sum_univ_one, Fin.sum_univ_one,
    Fin.append_left, Fin.append_right, add_zero]

/-- The affine row `(y₁, y₂, y₃) ↦ c₁ y₁ + c₂ y₂ + c₃ y₃` on `ℝ^{1+(1+1)}`. -/
noncomputable def row3 (c₁ c₂ c₃ : ℝ) : Affine (1 + (1 + 1)) 1 where
  A := fun _ => Fin.append (fun _ : Fin 1 => c₁)
    (Fin.append (fun _ : Fin 1 => c₂) fun _ : Fin 1 => c₃)
  b := fun _ => 0

theorem row3_eval (c₁ c₂ c₃ : ℝ) (y : Fin (1 + (1 + 1)) → ℝ) :
    (row3 c₁ c₂ c₃).eval y 0
      = c₁ * y (Fin.castAdd (1 + 1) 0)
        + (c₂ * y (Fin.natAdd 1 (Fin.castAdd 1 0))
          + c₃ * y (Fin.natAdd 1 (Fin.natAdd 1 0))) := by
  show (∑ j, Fin.append (fun _ : Fin 1 => c₁)
        (Fin.append (fun _ : Fin 1 => c₂) fun _ : Fin 1 => c₃) j * y j) + (0 : ℝ)
      = c₁ * y (Fin.castAdd (1 + 1) 0)
        + (c₂ * y (Fin.natAdd 1 (Fin.castAdd 1 0))
          + c₃ * y (Fin.natAdd 1 (Fin.natAdd 1 0)))
  rw [Fin.sum_univ_add, Fin.sum_univ_one, Fin.sum_univ_add, Fin.sum_univ_one,
    Fin.sum_univ_one, Fin.append_left, Fin.append_right, Fin.append_right,
    Fin.append_left, Fin.append_right, add_zero]

end Affine

end MaxNN
