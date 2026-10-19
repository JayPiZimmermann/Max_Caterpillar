import MaxNN.Constructions.MaxN.Width.Layer.Features

/-!
# Sides as explicit linear forms in the layer-1 output

`Width/Layer/Features.lean` shows that every coordinate and every pairwise maximum is recovered
from the pair-feature layer's output by a linear form.  To bound the **second** layer's width we
need those linear forms as *data* — an explicit coefficient vector in `Fin (W n) → ℝ` — because
the second layer's rows are exactly `side₁ - side₂`.

`PairLin n` collects the functions of `x` that are such a linear form.  It contains the
coordinates and the pairwise maxima, is closed under `+`, scalar `•` and finite sums, and hence
contains every **side** of the grammar (`sideVal_mem_pairLin`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Width

open BigOperators

variable {n : ℕ}

/-- Functions of `x` that are given by an **explicit linear form** in the layer-1 output
`feat n x` (coefficient vector included in the data). -/
def PairLin (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ a : Fin (W n) → ℝ, ∀ x, f x = ∑ k, a k * feat n x k }

/-! ## Two coefficient vectors -/

/-- The coefficient vector of the coordinate `x i`: `+1` on the `relu (x i)` unit, `-1` on the
`relu (-(x i))` unit. -/
noncomputable def coordCoef (i : Fin n) : Fin (W n) → ℝ :=
  fun k => (if k = posIdx i then (1 : ℝ) else 0) - (if k = negIdx i then (1 : ℝ) else 0)

/-- The coefficient vector of a single layer-1 unit. -/
noncomputable def unitCoef (u : Fin (W n)) : Fin (W n) → ℝ :=
  fun k => if k = u then (1 : ℝ) else 0

theorem sum_unitCoef (u : Fin (W n)) (y : Fin (W n) → ℝ) :
    (∑ k, unitCoef u k * y k) = y u := by
  unfold unitCoef
  exact Affine.delta_row_sum u y

theorem sum_coordCoef (i : Fin n) (y : Fin (W n) → ℝ) :
    (∑ k, coordCoef i k * y k) = coordLin i y := by
  unfold coordCoef coordLin
  rw [Finset.sum_congr rfl fun k _ => sub_mul
      (if k = posIdx i then (1 : ℝ) else 0) (if k = negIdx i then (1 : ℝ) else 0) (y k),
    Finset.sum_sub_distrib, Affine.delta_row_sum (posIdx i) y, Affine.delta_row_sum (negIdx i) y]

/-! ## `PairLin` is a vector space containing the coordinates and the pairwise maxima -/

theorem zero_mem_pairLin : (fun _ : Fin n → ℝ => (0 : ℝ)) ∈ PairLin n := by
  refine ⟨fun _ => 0, fun x => ?_⟩
  rw [Finset.sum_congr rfl fun k _ => zero_mul (feat n x k), Finset.sum_const_zero]

theorem add_mem_pairLin {f g : (Fin n → ℝ) → ℝ} (hf : f ∈ PairLin n) (hg : g ∈ PairLin n) :
    (fun x => f x + g x) ∈ PairLin n := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun k => a k + b k, fun x => ?_⟩
  show f x + g x = ∑ k, (a k + b k) * feat n x k
  rw [ha x, hb x, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (add_mul (a k) (b k) (feat n x k)).symm

theorem smul_mem_pairLin {f : (Fin n → ℝ) → ℝ} (c : ℝ) (hf : f ∈ PairLin n) :
    (fun x => c * f x) ∈ PairLin n := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => c * a k, fun x => ?_⟩
  show c * f x = ∑ k, (c * a k) * feat n x k
  rw [ha x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc c (a k) (feat n x k)).symm

theorem coord_mem_pairLin (i : Fin n) : (fun x : Fin n → ℝ => x i) ∈ PairLin n :=
  ⟨coordCoef i, fun x => by rw [sum_coordCoef i (feat n x), coordLin_feat x i]⟩

/-- **A pairwise maximum is an explicit linear form in the layer-1 output.**  For `i < j` its
coefficient vector is `coordCoef j + unitCoef (prIdx {i,j})`: the coordinate passthrough plus
**the single shared pair unit**. -/
theorem pairMax_mem_pairLin (i j : Fin n) :
    (fun x : Fin n → ℝ => max (x i) (x j)) ∈ PairLin n := by
  by_cases h : i < j
  · refine ⟨fun k => coordCoef j k + unitCoef (prIdx (prIdxOf i j h)) k, fun x => ?_⟩
    show max (x i) (x j) = ∑ k, (coordCoef j k + unitCoef (prIdx (prIdxOf i j h)) k) * feat n x k
    rw [← pairMaxLin_feat x i j]
    rw [show pairMaxLin i j (feat n x)
        = coordLin j (feat n x) + feat n x (prIdx (prIdxOf i j h)) from by
      unfold pairMaxLin; rw [dif_pos h]]
    rw [← sum_coordCoef j (feat n x), ← sum_unitCoef (prIdx (prIdxOf i j h)) (feat n x),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ =>
      (add_mul (coordCoef j k) (unitCoef (prIdx (prIdxOf i j h)) k) (feat n x k)).symm
  · by_cases h' : j < i
    · refine ⟨fun k => coordCoef i k + unitCoef (prIdx (prIdxOf j i h')) k, fun x => ?_⟩
      show max (x i) (x j) = ∑ k, (coordCoef i k + unitCoef (prIdx (prIdxOf j i h')) k) * feat n x k
      rw [← pairMaxLin_feat x i j]
      rw [show pairMaxLin i j (feat n x)
          = coordLin i (feat n x) + feat n x (prIdx (prIdxOf j i h')) from by
        unfold pairMaxLin; rw [dif_neg h, dif_pos h']]
      rw [← sum_coordCoef i (feat n x), ← sum_unitCoef (prIdx (prIdxOf j i h')) (feat n x),
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ =>
        (add_mul (coordCoef i k) (unitCoef (prIdx (prIdxOf j i h')) k) (feat n x k)).symm
    · have hij : i = j := le_antisymm (not_lt.mp h') (not_lt.mp h)
      have e : (fun x : Fin n → ℝ => max (x i) (x j)) = fun x => x i := by
        funext x
        rw [hij, max_self]
      rw [e]
      exact coord_mem_pairLin i

end Width

end MaxNN
