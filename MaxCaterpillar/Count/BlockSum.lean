import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Block sums

Two elementary facts for the per-unit count of `research/sN/simplify/exponential.md`
(step S6):

* `sum_powerset_biUnion`: a sum over the subsets `A` of a disjoint union of blocks of a
  product of block terms `g_i (A ∩ B_i)` factorises into the product of the block sums;
* `star_weight_le_one`: the weight of a star block with `1 ≤ s ≤ Δ` leaves,
  `(1/2 + y)(1+y)^s + y^s/2`, is at most `1` at `y = 1/(2Δ+2)`, `Δ ≥ 2`.
-/

open BigOperators Finset

namespace MaxCaterpillar.Count

theorem union_inter_left_eq {α : Type*} [DecidableEq α] {s t b : Finset α} (hs : s ⊆ b)
    (ht : Disjoint t b) : (s ∪ t) ∩ b = s := by
  ext x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨h | h, hb⟩
    · exact h
    · exact absurd hb (disjoint_left.mp ht h)
  · intro h
    exact ⟨Or.inl h, hs h⟩

theorem union_inter_right_eq {α : Type*} [DecidableEq α] {s t b : Finset α}
    (hs : Disjoint s b) : (s ∪ t) ∩ b = t ∩ b := by
  ext x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨h | h, hb⟩
    · exact absurd hb (disjoint_left.mp hs h)
    · exact ⟨h, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨Or.inr h, hb⟩

/-- Factorisation of a sum over subsets of a disjoint union of blocks. -/
theorem sum_powerset_biUnion {α ι : Type*} [DecidableEq α] [DecidableEq ι] (I : Finset ι)
    (B : ι → Finset α) (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (g : ι → Finset α → ℝ) :
    ∑ A in (I.biUnion B).powerset, ∏ i in I, g i (A ∩ B i) =
      ∏ i in I, ∑ S in (B i).powerset, g i S := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I hj ih =>
    have hd' : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → Disjoint (B i) (B i') := fun i hi i' hi' h =>
      hd i (mem_insert_of_mem hi) i' (mem_insert_of_mem hi') h
    have hdisj : Disjoint (B j) (I.biUnion B) := by
      rw [disjoint_biUnion_right]
      intro i hi
      exact hd j (mem_insert_self j I) i (mem_insert_of_mem hi) (fun h => hj (h ▸ hi))
    set U := I.biUnion B
    rw [prod_insert hj, ← ih hd', biUnion_insert, sum_mul_sum]
    symm
    refine sum_bij' (fun p _ => p.1 ∪ p.2) ?_ ?_ (fun A _ => (A ∩ B j, A ∩ U)) ?_ ?_ ?_
    · intro p hp
      rw [mem_product, mem_powerset, mem_powerset] at hp
      exact mem_powerset.mpr (union_subset_union hp.1 hp.2)
    · intro p hp
      rw [mem_product, mem_powerset, mem_powerset] at hp
      have h1 : (p.1 ∪ p.2) ∩ B j = p.1 :=
        union_inter_left_eq hp.1 (disjoint_of_subset_left hp.2 hdisj.symm)
      have h2 : ∀ i ∈ I, (p.1 ∪ p.2) ∩ B i = p.2 ∩ B i := by
        intro i hi
        have hdi : Disjoint (B j) (B i) :=
          hd j (mem_insert_self j I) i (mem_insert_of_mem hi) (fun h => hj (h ▸ hi))
        exact union_inter_right_eq (disjoint_of_subset_left hp.1 hdi)
      rw [prod_insert hj, h1]
      congr 1
      exact prod_congr rfl fun i hi => by rw [h2 i hi]
    · intro A hA
      exact mem_product.mpr ⟨mem_powerset.mpr (inter_subset_right _ _),
        mem_powerset.mpr (inter_subset_right _ _)⟩
    · intro p hp
      rw [mem_product, mem_powerset, mem_powerset] at hp
      have e1 : (p.1 ∪ p.2) ∩ B j = p.1 :=
        union_inter_left_eq hp.1 (disjoint_of_subset_left hp.2 hdisj.symm)
      have e2 : (p.1 ∪ p.2) ∩ U = p.2 := by
        rw [union_comm]
        exact union_inter_left_eq hp.2 (disjoint_of_subset_left hp.1 hdisj)
      change ((p.1 ∪ p.2) ∩ B j, (p.1 ∪ p.2) ∩ U) = p
      rw [e1, e2]
    · intro A hA
      rw [mem_powerset] at hA
      change (A ∩ B j) ∪ (A ∩ U) = A
      rw [← inter_distrib_left, inter_eq_left.mpr hA]

/-- The sum of `y^|S|` over the subsets of a star block `{c} ∪ L`, with factor `1/2` when `c`
and some leaf are outside `S`. -/
theorem star_sum {α : Type*} [DecidableEq α] (c : α) (L : Finset α) (hc : c ∉ L) (y : ℝ) :
    ∑ S in (insert c L).powerset,
        y ^ S.card * (if c ∉ S ∧ ∃ l ∈ L, l ∉ S then (1 / 2 : ℝ) else 1) =
      (1 / 2 + y) * (1 + y) ^ L.card + y ^ L.card / 2 := by
  rw [sum_powerset_insert hc]
  have hpow : ∑ S in L.powerset, y ^ S.card = (1 + y) ^ L.card := by
    have := sum_pow_mul_eq_add_pow y (1 : ℝ) L
    simp only [one_pow, mul_one] at this
    rw [this, add_comm]
  have h1 : ∀ S ∈ L.powerset,
      y ^ S.card * (if c ∉ S ∧ ∃ l ∈ L, l ∉ S then (1 / 2 : ℝ) else 1) =
        y ^ S.card / 2 + if S = L then y ^ L.card / 2 else 0 := by
    intro S hS
    rw [mem_powerset] at hS
    have hcS : c ∉ S := fun h => hc (hS h)
    by_cases hSL : S = L
    · subst hSL
      have : ¬ (c ∉ S ∧ ∃ l ∈ S, l ∉ S) := fun ⟨_, l, hl, hl'⟩ => hl' hl
      rw [if_neg this, if_pos rfl]
      ring
    · have hex : ∃ l ∈ L, l ∉ S := by
        by_contra h
        push_neg at h
        exact hSL (Subset.antisymm hS h)
      rw [if_pos ⟨hcS, hex⟩, if_neg hSL]
      ring
  have h2 : ∀ S ∈ L.powerset,
      y ^ (insert c S).card *
          (if c ∉ insert c S ∧ ∃ l ∈ L, l ∉ insert c S then (1 / 2 : ℝ) else 1) =
        y * y ^ S.card := by
    intro S hS
    rw [mem_powerset] at hS
    have hcS : c ∉ S := fun h => hc (hS h)
    rw [card_insert_of_not_mem hcS, if_neg (fun h => h.1 (mem_insert_self c S)), pow_succ]
    ring
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_add_distrib, ← mul_sum, sum_ite_eq',
    if_pos (mem_powerset_self L), ← sum_div, hpow]
  ring

/-- The weight of a lone spine vertex with a pendant edge: `1/2 + y`. -/
theorem single_sum {α : Type*} [DecidableEq α] (c : α) (y : ℝ) :
    ∑ S in ({c} : Finset α).powerset, y ^ S.card * (if c ∉ S then (1 / 2 : ℝ) else 1) =
      1 / 2 + y := by
  rw [show ({c} : Finset α) = insert c ∅ from rfl, sum_powerset_insert (not_mem_empty c)]
  simp

/-- `e^(1/2) < 33/20`. -/
theorem exp_half_lt : Real.exp (1 / 2) < 33 / 20 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos (1 / 2)
  by_contra hc
  push_neg at hc
  have hm := mul_le_mul hc hc (by norm_num) hpos.le
  rw [hsq] at hm
  norm_num at h hm
  linarith

/-- **Star weight.** For `Δ ≥ 2`, `1 ≤ s ≤ Δ` and `y = 1/(2Δ+2)`:
`(1/2 + y)(1+y)^s + y^s/2 ≤ 1`. -/
theorem star_weight_le_one {Δ s : ℕ} (hΔ : 2 ≤ Δ) (hs1 : 1 ≤ s) (hsΔ : s ≤ Δ) :
    (1 / 2 + 1 / (2 * Δ + 2 : ℝ)) * (1 + 1 / (2 * Δ + 2 : ℝ)) ^ s +
      (1 / (2 * Δ + 2 : ℝ)) ^ s / 2 ≤ 1 := by
  set y : ℝ := 1 / (2 * Δ + 2) with hy
  have hΔr : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy6 : y ≤ 1 / 6 := by
    rw [hy]; apply div_le_div_of_le_left (by norm_num) (by norm_num); linarith
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · have : s = 1 := by omega
    subst this
    rw [pow_one, pow_one]
    nlinarith only [hy0, hy6, sq_nonneg (y - 1 / 6)]
  have hys2 : y ^ s ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le (by linarith) hs2
  -- Keep the dependence between the coefficient and the exponent: Δy = 1/2 - y.
  have hΔy : (Δ : ℝ) * y = 1 / 2 - y := by
    rw [hy]
    field_simp
    <;> ring
  have hexp : (1 + y) ^ s ≤ Real.exp (1 / 2 - y) := by
    calc (1 + y) ^ s ≤ (Real.exp y) ^ s :=
          pow_le_pow_left (by linarith) (by linarith [Real.add_one_le_exp y]) _
      _ = Real.exp (s * y) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Δ * y) := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hsΔ) hy0.le)
      _ = Real.exp (1 / 2 - y) := by rw [hΔy]
  -- A quadratic Taylor bound works uniformly, without special cases for Δ.
  have htaylor : Real.exp (1 / 2 - y) ≤
      1 + (1 / 2 - y) + (1 / 2 - y) ^ 2 * 3 / 4 := by
    convert Real.exp_bound' (x := 1 / 2 - y) (by linarith) (by linarith)
      (show 0 < 2 by decide) using 1 <;> norm_num [sum_range_succ]
  have hprod := mul_le_mul_of_nonneg_left (hexp.trans htaylor)
    (show 0 ≤ 1 / 2 + y by linarith)
  have hcube : y ^ 3 ≤ (1 / 6 : ℝ) ^ 3 := pow_le_pow_left hy0.le hy6 3
  linarith only [hprod, hys2, hcube, hy6, sq_nonneg y]

end MaxCaterpillar.Count
