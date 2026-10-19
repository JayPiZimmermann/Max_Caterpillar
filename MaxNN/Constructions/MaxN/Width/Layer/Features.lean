import MaxNN.Core.Class
import MaxNN.Constructions.MaxN.Width.Layer.Pairs

/-!
# The pair-feature first hidden layer, and its width

Every atom of every certificate in the `MaxN` grammar is a `max` of two **sides**, and a side is
a sum of **pairwise maxima** `max (x i) (x j)` (`MaxN/Certificate/Grammar.lean`).  A pairwise
maximum needs exactly one `relu` unit,

  `max (x i) (x j) = x j + relu (x i - x j)`,

whose normal `e i - e j` depends only on the *unordered pair* `{i, j}` — so the SAME unit serves
every atom of every orbit that mentions that pair.  There are only `n.choose 2` pairs.  Adding
`2 * n` units for the identity passthrough `x i = relu (x i) - relu (-(x i))` (needed because the
second layer must see the coordinates themselves, not just their differences) gives a first
hidden layer of

  `W n = n + (n + n.choose 2) = n.choose 2 + 2 * n`

units, **independent of the number of atoms**.  This file builds that layer, and proves the two
recovery lemmas that make it universal: from its post-`relu` output, every coordinate and every
pairwise maximum is recovered by a *linear* form (`coordLin_feat`, `pairMaxLin_feat`), i.e. at
zero further hidden-layer cost.

`Width/Class.lean` turns this into a network statement; `Width/Certificate.lean` applies it to
the grammar.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Width

open BigOperators

variable {n : ℕ}

/-- **The width of the pair-feature first hidden layer**: `n` units `relu (x i)`, `n` units
`relu (-(x i))`, and `n.choose 2` units `relu (x i - x j)`, one per unordered pair `i < j`. -/
def W (n : ℕ) : ℕ := n + (n + n.choose 2)

theorem W_eq (n : ℕ) : W n = n.choose 2 + 2 * n := by
  unfold W
  ring

/-! ## The three blocks of unit indices -/

/-- Index of the unit `relu (x i)`. -/
def posIdx (i : Fin n) : Fin (W n) := Fin.castAdd (n + n.choose 2) i

/-- Index of the unit `relu (-(x i))`. -/
def negIdx (i : Fin n) : Fin (W n) := Fin.natAdd n (Fin.castAdd (n.choose 2) i)

/-- Index of the unit `relu (x (prFst q) - x (prSnd q))`. -/
def prIdx (q : Fin (n.choose 2)) : Fin (W n) := Fin.natAdd n (Fin.natAdd n q)

/-! ## The layer -/

/-- The `n.choose 2` rows `e (prFst q) - e (prSnd q)`. -/
noncomputable def pairRows (n : ℕ) : Affine n (n.choose 2) where
  A := fun q j => (if j = prFst q then (1 : ℝ) else 0) - (if j = prSnd q then (1 : ℝ) else 0)
  b := fun _ => 0

theorem pairRows_eval (n : ℕ) (x : Fin n → ℝ) (q : Fin (n.choose 2)) :
    (pairRows n).eval x q = x (prFst q) - x (prSnd q) := by
  unfold Affine.eval pairRows
  rw [Finset.sum_congr rfl fun j _ => sub_mul
      (if j = prFst q then (1 : ℝ) else 0) (if j = prSnd q then (1 : ℝ) else 0) (x j),
    Finset.sum_sub_distrib, Affine.delta_row_sum (prFst q) x, Affine.delta_row_sum (prSnd q) x,
    add_zero]

/-- **The pair-feature first hidden layer**, as an affine map `ℝ^n → ℝ^(W n)`. -/
noncomputable def featureLayer (n : ℕ) : Affine n (W n) :=
  (Affine.id n).stack ((Affine.id n).neg.stack (pairRows n))

/-- The post-`relu` output of the first hidden layer. -/
noncomputable def feat (n : ℕ) (x : Fin n → ℝ) : Fin (W n) → ℝ :=
  fun k => relu ((featureLayer n).eval x k)

theorem feat_pos (x : Fin n → ℝ) (i : Fin n) : feat n x (posIdx i) = relu (x i) := by
  unfold feat featureLayer posIdx
  rw [Affine.stack_eval_castAdd, Affine.id_eval]

theorem feat_neg (x : Fin n → ℝ) (i : Fin n) : feat n x (negIdx i) = relu (-(x i)) := by
  unfold feat featureLayer negIdx
  rw [Affine.stack_eval_natAdd, Affine.stack_eval_castAdd, Affine.neg_eval, Affine.id_eval]

theorem feat_pr (x : Fin n → ℝ) (q : Fin (n.choose 2)) :
    feat n x (prIdx q) = relu (x (prFst q) - x (prSnd q)) := by
  unfold feat featureLayer prIdx
  rw [Affine.stack_eval_natAdd, Affine.stack_eval_natAdd, pairRows_eval]

/-! ## Recovery: coordinates and pairwise maxima are LINEAR in the layer's output

This is the whole point.  The second hidden layer sees `feat n x`; both recovery maps below are
linear forms on `ℝ^(W n)` (class `0`), so a `max` of two sides costs exactly one further hidden
layer — and the first layer never grows. -/

/-- `x i`, recovered from the layer output: `relu (x i) - relu (-(x i))`. -/
noncomputable def coordLin (i : Fin n) (y : Fin (W n) → ℝ) : ℝ := y (posIdx i) - y (negIdx i)

theorem coordLin_feat (x : Fin n → ℝ) (i : Fin n) : coordLin i (feat n x) = x i := by
  unfold coordLin
  rw [feat_pos, feat_neg, relu_sub_relu_neg]

theorem coordLin_mem (i : Fin n) : (fun y => coordLin i y) ∈ ReLUClass (W n) 0 :=
  sub_mem_reluClass (coord_mem_reluClass (posIdx i)) (coord_mem_reluClass (negIdx i))

/-- `max (x i) (x j)`, recovered from the layer output.  For `i < j` this is
`x j + relu (x i - x j)`: the coordinate passthrough plus **the one shared pair unit**. -/
noncomputable def pairMaxLin (i j : Fin n) (y : Fin (W n) → ℝ) : ℝ :=
  if h : i < j then coordLin j y + y (prIdx (prIdxOf i j h))
  else if h' : j < i then coordLin i y + y (prIdx (prIdxOf j i h'))
  else coordLin i y

theorem pairMaxLin_feat (x : Fin n → ℝ) (i j : Fin n) :
    pairMaxLin i j (feat n x) = max (x i) (x j) := by
  unfold pairMaxLin
  by_cases h : i < j
  · rw [dif_pos h, coordLin_feat, feat_pr, prFst_prIdxOf, prSnd_prIdxOf,
      max_comm (x i) (x j), max_eq_relu_add (x j) (x i)]
    exact add_comm _ _
  · rw [dif_neg h]
    by_cases h' : j < i
    · rw [dif_pos h', coordLin_feat, feat_pr, prFst_prIdxOf, prSnd_prIdxOf,
        max_eq_relu_add (x i) (x j)]
      exact add_comm _ _
    · have hij : i = j := le_antisymm (not_lt.mp h') (not_lt.mp h)
      rw [dif_neg h', coordLin_feat, hij, max_self]

theorem pairMaxLin_mem (i j : Fin n) : (fun y => pairMaxLin i j y) ∈ ReLUClass (W n) 0 := by
  by_cases h : i < j
  · have e : (fun y : Fin (W n) → ℝ => pairMaxLin i j y)
        = fun y => coordLin j y + y (prIdx (prIdxOf i j h)) := by
      funext y
      unfold pairMaxLin
      rw [dif_pos h]
    rw [e]
    exact add_mem_reluClass (coordLin_mem j) (coord_mem_reluClass _)
  · by_cases h' : j < i
    · have e : (fun y : Fin (W n) → ℝ => pairMaxLin i j y)
          = fun y => coordLin i y + y (prIdx (prIdxOf j i h')) := by
        funext y
        unfold pairMaxLin
        rw [dif_neg h, dif_pos h']
      rw [e]
      exact add_mem_reluClass (coordLin_mem i) (coord_mem_reluClass _)
    · have e : (fun y : Fin (W n) → ℝ => pairMaxLin i j y) = fun y => coordLin i y := by
        funext y
        unfold pairMaxLin
        rw [dif_neg h, dif_neg h']
      rw [e]
      exact coordLin_mem i

end Width

end MaxNN
