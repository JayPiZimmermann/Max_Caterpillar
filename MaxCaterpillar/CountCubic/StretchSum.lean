import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Std.Tactic.Omega

/-! # The stretch weight inequality of the cubic count

Abstract combinatorics for the cubic lower bound on `s_N`
(`research/sN/NOTE.md`, "Cubic claim C", steps 3 and 4, and
`research/sN/stretch_sum.py`).

A stretch `s_1, …, s_k` carries leaf counts `c_j` (`c : ℕ → ℕ`, only
`j ∈ [1, k]` is used).  The admissible triples and their weights are

* a leaf edge at `s_j`, allowed when `c_j = 1`, weight `1/((j-1)! (k-j)!)`;
* a spine edge `s_j s_{j+1}`, allowed when `c_j = c_{j+1} = 0`,
  weight `1/((j-1)! (k-j-1)!)`;
* (vertex type) the vertex `s_j`, allowed when `c_j = 0`,
  weight `1/((j-1)! (k-j)!)`.

We prove the closed forms `Σ_j 1/((j-1)!(k-j)!) = 2^(k-1)/(k-1)!` and
`Σ_j 1/((j-1)!(k-j-1)!) = 2^(k-2)/(k-2)!`, and that both the edge-type sum
(for every leaf pattern) and the vertex-type sum are at most `2`.

Proof of the mixed bound (charging): write `n = k - 1` and use 0-based indices
`i = j - 1`.  The leaf weight is `W_i = C(n,i)/n!` and the spine weight is
`E_i = C(n-1,i)/(n-1)!`.  Split each spine edge half to each end:
`[z_i ∧ z_{i+1}] E_i ≤ ([z_i] E_i + [z_{i+1}] E_i)/2`.  Vertex `i` then
receives either `W_i` (if it is a leaf position) or `(E_{i-1} + E_i)/2 =
C(n,i)/(2 (n-1)!) = (n/2) W_i` (Pascal).  Hence the sum is at most
`max(1, n/2) · 2^n/n!`, which is `2` for `n ≤ 1` and `2^(n-1)/(n-1)! ≤ 2`
for `n ≥ 2`.
-/

open Finset BigOperators Nat

namespace MaxCaterpillar.CountCubic

/-- Weight of a leaf edge (and of a vertex) at position `j` of a stretch of
length `k`: `1/((j-1)! (k-j)!)`. -/
def leafWeight (k j : ℕ) : ℚ := 1 / (((j - 1)! : ℚ) * ((k - j)! : ℚ))

/-- Weight of the spine edge `s_j s_{j+1}` of a stretch of length `k`:
`1/((j-1)! (k-j-1)!)`. -/
def spineWeight (k j : ℕ) : ℚ := 1 / (((j - 1)! : ℚ) * ((k - j - 1)! : ℚ))

/-- Edge-type stretch sum for the leaf pattern `c` (as in `stretch_sum.py`). -/
def stretchEdgeSum (k : ℕ) (c : ℕ → ℕ) : ℚ :=
  (∑ j in Icc 1 k, if c j = 1 then leafWeight k j else 0) +
    ∑ j in Ico 1 k, if c j = 0 ∧ c (j + 1) = 0 then spineWeight k j else 0

/-- Vertex-type stretch sum for the leaf pattern `c`. -/
def stretchVertexSum (k : ℕ) (c : ℕ → ℕ) : ℚ :=
  ∑ j in Icc 1 k, if c j = 0 then leafWeight k j else 0

/-! ### Elementary facts -/

theorem two_pow_le_two_mul_factorial : ∀ m : ℕ, 2 ^ m ≤ 2 * m !
  | 0 => by norm_num
  | 1 => by norm_num
  | (m + 2) => by
    have ih := two_pow_le_two_mul_factorial (m + 1)
    have h1 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    rw [h1, Nat.factorial_succ (m + 1)]
    have : 2 * (m + 1)! ≤ (m + 1 + 1) * (m + 1)! :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- `2^m / m! ≤ 2` for every `m`. -/
theorem two_pow_div_factorial_le_two (m : ℕ) : (2 : ℚ) ^ m / (m ! : ℚ) ≤ 2 := by
  have h := two_pow_le_two_mul_factorial m
  have hpos : (0 : ℚ) < (m ! : ℚ) := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff hpos]
  exact_mod_cast h

theorem inv_factorial_mul_factorial_eq (n i : ℕ) (h : i ≤ n) :
    (1 : ℚ) / ((i ! : ℚ) * ((n - i)! : ℚ)) = (n.choose i : ℚ) / (n ! : ℚ) := by
  have := Nat.choose_mul_factorial_mul_factorial h
  rw [div_eq_div_iff (by positivity) (by positivity), ← this]
  push_cast
  ring

theorem sum_choose_div_factorial (n : ℕ) :
    ∑ i in range (n + 1), (n.choose i : ℚ) / (n ! : ℚ) = (2 : ℚ) ^ n / (n ! : ℚ) := by
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast Nat.sum_range_choose n

/-- 0-based closed form: `Σ_{i ≤ n} 1/(i! (n-i)!) = 2^n/n!`. -/
theorem sum_inv_factorial_mul_factorial (n : ℕ) :
    ∑ i in range (n + 1), (1 : ℚ) / ((i ! : ℚ) * ((n - i)! : ℚ)) =
      (2 : ℚ) ^ n / (n ! : ℚ) := by
  rw [← sum_choose_div_factorial]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact inv_factorial_mul_factorial_eq n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-! ### The 0-based core inequality -/

/-- Core inequality in 0-based form.  `b i`: position `i` is a leaf-edge
position; `z i`: position `i` is leafless; never both. -/
theorem core_le_two (n : ℕ) (b z : ℕ → Prop) [DecidablePred b] [DecidablePred z]
    (hbz : ∀ i, b i → ¬ z i) :
    (∑ i in range (n + 1),
        if b i then (1 : ℚ) / ((i ! : ℚ) * ((n - i)! : ℚ)) else 0) +
      ∑ i in range n,
        (if z i ∧ z (i + 1) then (1 : ℚ) / ((i ! : ℚ) * ((n - 1 - i)! : ℚ)) else 0)
      ≤ 2 := by
  rcases n with _ | m
  · simp only [Nat.zero_eq, zero_add, Finset.sum_range_one, Finset.range_zero,
      Finset.sum_empty, add_zero]
    split_ifs <;> norm_num
  -- n = m + 1; convert to binomial form
  set W : ℕ → ℚ := fun i => ((m + 1).choose i : ℚ) / ((m + 1)! : ℚ) with hW
  set E : ℕ → ℚ := fun i => (m.choose i : ℚ) / (m ! : ℚ) with hE
  set E' : ℕ → ℚ := fun i => if i = 0 then 0 else (m.choose (i - 1) : ℚ) / (m ! : ℚ)
    with hE'
  have hS1 : (∑ i in range (m + 1 + 1),
        if b i then (1 : ℚ) / ((i ! : ℚ) * ((m + 1 - i)! : ℚ)) else 0) =
      ∑ i in range (m + 2), if b i then W i else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inv_factorial_mul_factorial_eq (m + 1) i
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hS2 : (∑ i in range (m + 1),
        if z i ∧ z (i + 1) then (1 : ℚ) / ((i ! : ℚ) * ((m + 1 - 1 - i)! : ℚ)) else 0) =
      ∑ i in range (m + 1), if z i ∧ z (i + 1) then E i else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have : m + 1 - 1 - i = m - i := by omega
    rw [this, inv_factorial_mul_factorial_eq m i
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [hS1, hS2]
  -- charging: split spine edges between their ends
  have hsplit : (∑ i in range (m + 1), if z i ∧ z (i + 1) then E i else 0) ≤
      (∑ i in range (m + 1), if z i then E i / 2 else 0) +
        ∑ i in range (m + 1), if z (i + 1) then E i / 2 else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hEi : 0 ≤ E i := by simp only [hE]; positivity
    split_ifs <;> simp_all <;> linarith
  have hA : (∑ i in range (m + 1), if z i then E i / 2 else 0) =
      ∑ i in range (m + 2), if z i then E i / 2 else 0 := by
    rw [Finset.sum_range_succ _ (m + 1)]
    have : E (m + 1) = 0 := by simp [hE, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)]
    simp [this]
  have hB : (∑ i in range (m + 1), if z (i + 1) then E i / 2 else 0) =
      ∑ i in range (m + 2), if z i then E' i / 2 else 0 := by
    rw [Finset.sum_range_succ' _ (m + 1)]
    simp [hE, hE']
  -- per-vertex bound
  have hX : ∀ i, E i + E' i = ((m + 1).choose i : ℚ) / (m ! : ℚ) := by
    intro i
    rcases i with _ | i
    · simp [hE, hE']
    · simp only [hE, hE', Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
        Nat.choose_succ_succ]
      push_cast
      ring
  have hWX : ∀ i, ((m + 1).choose i : ℚ) / (m ! : ℚ) = ((m : ℚ) + 1) * W i := by
    intro i
    simp only [hW, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  set c : ℚ := if m = 0 then 1 else ((m : ℚ) + 1) / 2 with hc
  have hterm : ∀ i, (if b i then W i else 0) + ((if z i then E i / 2 else 0) +
      (if z i then E' i / 2 else 0)) ≤ c * W i := by
    intro i
    have hWi : 0 ≤ W i := by simp only [hW]; positivity
    have hzi : (if z i then E i / 2 else 0) + (if z i then E' i / 2 else 0) =
        if z i then ((m : ℚ) + 1) / 2 * W i else 0 := by
      split_ifs
      · rw [show E i / 2 + E' i / 2 = (E i + E' i) / 2 by ring, hX, hWX]; ring
      · simp
    rw [hzi]
    by_cases hm : m = 0
    · have hcv : c = 1 := by simp [hc, hm]
      have hm' : ((m : ℚ) + 1) / 2 = 1 / 2 := by simp [hm]
      rw [hcv, hm']
      by_cases hb : b i
      · simp only [hb, hbz i hb, if_true, if_false, add_zero]; linarith
      · simp only [hb, if_false, zero_add]
        split_ifs <;> nlinarith
    · have hcv : c = ((m : ℚ) + 1) / 2 := by simp [hc, hm]
      have h1 : (1 : ℚ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      rw [hcv]
      by_cases hb : b i
      · simp only [hb, hbz i hb, if_true, if_false, add_zero]; nlinarith
      · simp only [hb, if_false, zero_add]
        split_ifs
        · exact le_refl _
        · positivity
  calc (∑ i in range (m + 2), if b i then W i else 0) +
        (∑ i in range (m + 1), if z i ∧ z (i + 1) then E i else 0)
      ≤ (∑ i in range (m + 2), if b i then W i else 0) +
          ((∑ i in range (m + 2), if z i then E i / 2 else 0) +
            ∑ i in range (m + 2), if z i then E' i / 2 else 0) := by
        rw [← hA, ← hB]; linarith
    _ = ∑ i in range (m + 2), ((if b i then W i else 0) +
          ((if z i then E i / 2 else 0) + (if z i then E' i / 2 else 0))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ∑ i in range (m + 2), c * W i := Finset.sum_le_sum fun i _ => hterm i
    _ = c * (2 ^ (m + 1) / ((m + 1)! : ℚ)) := by
        rw [← Finset.mul_sum, hW]
        simp only
        rw [sum_choose_div_factorial]
    _ ≤ 2 := by
        by_cases hm : m = 0
        · subst hm; norm_num [hc]
        · have : c * (2 ^ (m + 1) / ((m + 1)! : ℚ)) = 2 ^ m / (m ! : ℚ) := by
            simp only [hc, hm, if_false, Nat.factorial_succ]
            push_cast
            field_simp
            ring
          rw [this]
          exact two_pow_div_factorial_le_two m

/-! ### Statements in the 1-based form of the note -/

theorem sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℚ) :
    ∑ j in Icc 1 (n + 1), f j = ∑ i in range (n + 1), f (1 + i) := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  rfl

theorem sum_Ico_one_eq_sum_range (n : ℕ) (f : ℕ → ℚ) :
    ∑ j in Ico 1 (n + 1), f j = ∑ i in range n, f (1 + i) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp

/-- Closed form of the leaf (vertex) weights:
`Σ_{j=1}^{k} 1/((j-1)!(k-j)!) = 2^(k-1)/(k-1)!` for `k ≥ 1`. -/
theorem sum_leafWeight (k : ℕ) (hk : 1 ≤ k) :
    ∑ j in Icc 1 k, leafWeight k j = (2 : ℚ) ^ (k - 1) / ((k - 1)! : ℚ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [sum_Icc_one_eq_sum_range, Nat.add_sub_cancel, ← sum_inv_factorial_mul_factorial]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 + i - 1 = i := by omega
  have h2 : n + 1 - (1 + i) = n - i := by omega
  simp only [leafWeight, h1, h2]

/-- Closed form of the spine weights:
`Σ_{j=1}^{k-1} 1/((j-1)!(k-j-1)!) = 2^(k-2)/(k-2)!` for `k ≥ 2`. -/
theorem sum_spineWeight (k : ℕ) (hk : 2 ≤ k) :
    ∑ j in Ico 1 k, spineWeight k j = (2 : ℚ) ^ (k - 2) / ((k - 2)! : ℚ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [show n + 2 = (n + 1) + 1 by rfl, sum_Ico_one_eq_sum_range,
    show n + 1 + 1 - 2 = n by omega, ← sum_inv_factorial_mul_factorial]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 + i - 1 = i := by omega
  have h2 : n + 1 + 1 - (1 + i) - 1 = n - i := by omega
  simp only [spineWeight, h1, h2]

theorem sum_leafWeight_le_two (k : ℕ) : ∑ j in Icc 1 k, leafWeight k j ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [sum_leafWeight k hk]; exact two_pow_div_factorial_le_two _

theorem sum_spineWeight_le_two (k : ℕ) : ∑ j in Ico 1 k, spineWeight k j ≤ 2 := by
  by_cases hk : 2 ≤ k
  · rw [sum_spineWeight k hk]; exact two_pow_div_factorial_le_two _
  · interval_cases k <;> norm_num [spineWeight]

/-- **Edge-type stretch inequality** (NOTE.md cubic step 3): for every stretch
length `k` and every leaf pattern `c`, the sum of the admissible leaf-edge and
spine-edge weights is at most `2`. -/
theorem stretchEdgeSum_le_two (k : ℕ) (c : ℕ → ℕ) : stretchEdgeSum k c ≤ 2 := by
  rcases k with _ | n
  · norm_num [stretchEdgeSum]
  unfold stretchEdgeSum
  rw [sum_Icc_one_eq_sum_range, sum_Ico_one_eq_sum_range]
  have key := core_le_two n (fun i => c (1 + i) = 1) (fun i => c (1 + i) = 0)
    (fun i h1 h0 => by simp only at h1 h0; omega)
  refine le_trans (le_of_eq ?_) key
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : 1 + i - 1 = i := by omega
    have h2 : n + 1 - (1 + i) = n - i := by omega
    simp only [leafWeight, h1, h2]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : 1 + i - 1 = i := by omega
    have h2 : n + 1 - (1 + i) - 1 = n - 1 - i := by omega
    simp only [spineWeight, h1, h2]
    rfl

/-- **Vertex-type stretch inequality** (NOTE.md cubic step 4). -/
theorem stretchVertexSum_le_two (k : ℕ) (c : ℕ → ℕ) : stretchVertexSum k c ≤ 2 := by
  refine le_trans ?_ (sum_leafWeight_le_two k)
  refine Finset.sum_le_sum fun j _ => ?_
  have : 0 ≤ leafWeight k j := by unfold leafWeight; positivity
  split_ifs <;> linarith

end MaxCaterpillar.CountCubic
