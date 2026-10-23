import MaxCaterpillar.Trees.RootedStars

/-!
# Pass conditions for general unit descriptions

`CountExp.W1Functional` and `CountExp.W2Digits` prove, for normalized caterpillar keys,
that a nonzero `k`-th mixed difference forces conditions (a) and (s).  The proofs use
only an integer head and ordered pairs `i < j`.  This file repeats them for an arbitrary
description `D = (h, M)` of `CountLower.Descr` with `m.1 < m.2` for all `m ∈ M`.
-/

open BigOperators Finset

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

variable {N : ℕ}

/-- `(o, x)` or `(x, o)` is a pair of `D`. -/
def DAdj (D : Descr N) (o x : Fin N) : Prop := (o, x) ∈ D.M ∨ (x, o) ∈ D.M

/-- `κ_o = h_o + #{(o, x) ∈ M}`. -/
noncomputable def DKappa (D : Descr N) (o : Fin N) : ℝ :=
  (D.h o : ℝ) + ((D.M.filter fun m => m.1 = o).card : ℝ)

/-- `D` passes the locality of `π`. -/
def DPasses (D : Descr N) (k : ℕ) (π : Equiv.Perm (Fin N)) : Prop :=
  Balanced (DAdj D) (DKappa D) k π ∧ Active (DAdj D) (DKappa D) k π

section Box

variable {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

theorem abs_boxPt_sub_le' (hδ : 0 ≤ δ) (S : Finset (Fin N)) (o : Fin N) :
    |boxPt k B δ π S o - basePtR k B π o| ≤ δ := by
  unfold boxPt
  rw [add_sub_cancel']
  split_ifs
  · rw [abs_of_nonneg hδ]
  · rw [abs_zero]
    exact hδ

end Box

section Units

theorem abs_relu_sub_le' (a b : ℝ) : |MaxNN.relu a - MaxNN.relu b| ≤ |a - b| := by
  unfold MaxNN.relu
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

theorem descr_arg_base_isInt (D : Descr N) (k B : ℕ) (π : Equiv.Perm (Fin N)) :
    ∃ z : ℤ, D.arg (basePtR k B π) = z :=
  ⟨D.argZ (basePt k B π), by
    have := Descr.arg_intCast D (basePt k B π)
    exact this⟩

theorem abs_descr_arg_boxPt_sub_le (D : Descr N) {k B : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (π : Equiv.Perm (Fin N)) (S : Finset (Fin N)) :
    |D.arg (boxPt k B δ π S) - D.arg (basePtR k B π)| ≤
      δ * (∑ o, |(D.h o : ℝ)| + 2 * (D.M.card : ℝ)) := by
  have he := abs_boxPt_sub_le' (k := k) (B := B) (π := π) hδ S
  unfold Descr.arg
  have h1 : |∑ o, (D.h o : ℝ) * boxPt k B δ π S o - ∑ o, (D.h o : ℝ) * basePtR k B π o| ≤
      δ * ∑ o, |(D.h o : ℝ)| := by
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun o _ => ?_)
    rw [← mul_sub, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (he o) (abs_nonneg _)
  have h2 : |∑ p in D.M, MaxNN.relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
      ∑ p in D.M, MaxNN.relu (basePtR k B π p.1 - basePtR k B π p.2)| ≤
      δ * (2 * (D.M.card : ℝ)) := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hp : ∀ p ∈ D.M, |MaxNN.relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
        MaxNN.relu (basePtR k B π p.1 - basePtR k B π p.2)| ≤ 2 * δ := by
      intro p _
      refine (abs_relu_sub_le' _ _).trans ?_
      have e1 := abs_le.mp (he p.1)
      have e2 := abs_le.mp (he p.2)
      rw [abs_le]
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
    refine (sum_le_sum hp).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]
    ring
  calc _ = |(∑ o, (D.h o : ℝ) * boxPt k B δ π S o - ∑ o, (D.h o : ℝ) * basePtR k B π o) +
        (∑ p in D.M, MaxNN.relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) -
          ∑ p in D.M, MaxNN.relu (basePtR k B π p.1 - basePtR k B π p.2))| := by
          congr 1
          ring
    _ ≤ _ := (abs_add _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

theorem mixedDiff_descr_arg (D : Descr N) {k B : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkN : k ≤ N)
    (π : Equiv.Perm (Fin N)) : mixedDiff k B δ π D.arg = 0 := by
  have he : D.arg = (∑ o, (D.h o : ℝ) • (fun y : Fin N → ℝ => y o)) +
      ∑ p in D.M, (fun y : Fin N → ℝ => MaxNN.relu (y p.1 - y p.2)) := by
    funext y
    unfold Descr.arg
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [he, map_add, map_sum, map_sum]
  rw [sum_eq_zero fun o _ => ?_, sum_eq_zero fun p _ => ?_, add_zero]
  · exact mixedDiff_eq_zero_of_two' hk hkN p.1 p.2 fun x x' h1 h2 => by
      show MaxNN.relu (x p.1 - x p.2) = MaxNN.relu (x' p.1 - x' p.2)
      rw [h1, h2]
  · rw [map_smul, mixedDiff_eq_zero_of_two' hk hkN o o fun x x' h _ => h, smul_zero]

theorem descr_arg_boxPt_insert (D : Descr N) {k B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    {π : Equiv.Perm (Fin N)} {t : Fin N} (ht : t ∈ tieSet k π)
    (hnb : ∀ x, ((π x : Fin N) : ℕ) < k → ¬ DAdj D t x)
    (hκ : DKappa D t = 0) {S : Finset (Fin N)} (hS : S ⊆ tieSet k π) (htS : t ∉ S) :
    D.arg (boxPt k B δ π (insert t S)) = D.arg (boxPt k B δ π S) := by
  have hS' : insert t S ⊆ tieSet k π := insert_subset_iff.mpr ⟨ht, hS⟩
  have hy't : boxPt k B δ π (insert t S) t = δ := by
    rw [boxPt_of_mem' ht, if_pos (mem_insert_self t S)]
  have hyt : boxPt k B δ π S t = 0 := by
    rw [boxPt_of_mem' ht, if_neg htS]
  have hout : ∀ x, DAdj D t x → x ∉ tieSet k π := fun x hx hxT =>
    hnb x (mem_tieSet'.mp hxT) hx
  have hlin : ∑ o, (D.h o : ℝ) * boxPt k B δ π (insert t S) o =
      ∑ o, (D.h o : ℝ) * boxPt k B δ π S o + (D.h t : ℝ) * δ := by
    have hd : ∀ o, (D.h o : ℝ) * boxPt k B δ π (insert t S) o =
        (D.h o : ℝ) * boxPt k B δ π S o + if o = t then (D.h t : ℝ) * δ else 0 := by
      intro o
      by_cases hot : o = t
      · subst hot
        rw [hy't, hyt, if_pos rfl]
        ring
      · rw [boxPt_insert_of_ne' hot, if_neg hot, add_zero]
    rw [sum_congr rfl fun o _ => hd o, sum_add_distrib, sum_ite_eq', if_pos (mem_univ t)]
  have hpair : ∑ p in D.M,
        MaxNN.relu (boxPt k B δ π (insert t S) p.1 - boxPt k B δ π (insert t S) p.2) =
      ∑ p in D.M, MaxNN.relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) +
        δ * ((D.M.filter fun p => p.1 = t).card : ℝ) := by
    have hd : ∀ p ∈ D.M,
        MaxNN.relu (boxPt k B δ π (insert t S) p.1 - boxPt k B δ π (insert t S) p.2) =
          MaxNN.relu (boxPt k B δ π S p.1 - boxPt k B δ π S p.2) + if p.1 = t then δ else 0 := by
      intro p hp
      by_cases h1 : p.1 = t
      · have h2T : p.2 ∉ tieSet k π := hout p.2 (Or.inl (by rw [← h1]; exact hp))
        rw [if_pos h1, h1, hy't, hyt, boxPt_of_not_mem' hS' h2T, boxPt_of_not_mem' hS h2T]
        have hb := basePtR_le_neg_one' (k := k) (π := π) hB h2T
        rw [MaxNN.relu_of_nonneg (by linarith), MaxNN.relu_of_nonneg (by linarith)]
        ring
      · rw [if_neg h1, add_zero]
        by_cases h2 : p.2 = t
        · have h1T : p.1 ∉ tieSet k π := hout p.1 (Or.inr (by rw [← h2]; exact hp))
          rw [h2, hy't, hyt, boxPt_of_not_mem' hS' h1T, boxPt_of_not_mem' hS h1T]
          have hb := basePtR_le_neg_one' (k := k) (π := π) hB h1T
          rw [MaxNN.relu_of_nonpos (by linarith), MaxNN.relu_of_nonpos (by linarith)]
        · rw [boxPt_insert_of_ne' h1, boxPt_insert_of_ne' h2]
    rw [sum_congr rfl hd, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  unfold Descr.arg
  rw [hlin, hpair]
  have : (D.h t : ℝ) * δ + δ * ((D.M.filter fun p => p.1 = t).card : ℝ) = δ * DKappa D t := by
    unfold DKappa
    ring
  rw [hκ, mul_zero] at this
  linarith

/-- **Steps 2–3 for descriptions.** -/
theorem descr_pass_of_mixedDiff_ne (D : Descr N) {k B : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkN : k ≤ N) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hδb : δ * (∑ o, |(D.h o : ℝ)| + 2 * (D.M.card : ℝ)) < 1)
    (π : Equiv.Perm (Fin N)) (hne : mixedDiff k B δ π D.unit ≠ 0) :
    D.arg (basePtR k B π) = 0 ∧ Active (DAdj D) (DKappa D) k π := by
  obtain ⟨z, hz⟩ := descr_arg_base_isInt D k B π
  have hb : ∀ S, |D.arg (boxPt k B δ π S) - z| < 1 := fun S => by
    rw [← hz]
    exact (abs_descr_arg_boxPt_sub_le D hδ.le π S).trans_lt hδb
  rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
  · exfalso
    apply hne
    rw [mixedDiff_congr' (g' := 0) fun S _ => ?_, map_zero]
    have h := abs_lt.mp (hb S)
    have hz1 : (z : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hz0
    unfold Descr.unit
    rw [MaxNN.relu_of_nonpos (by linarith [h.2]), Pi.zero_apply]
  · refine ⟨by rw [hz, hz0, Int.cast_zero], ?_⟩
    intro t htk hnb hκ
    apply hne
    have ht : t ∈ tieSet k π := mem_tieSet'.mpr htk
    refine mixedDiff_eq_zero_of_insert' ht fun S hS htS => ?_
    unfold Descr.unit
    rw [descr_arg_boxPt_insert D hB hδ.le ht hnb hκ hS htS]
  · exfalso
    apply hne
    rw [mixedDiff_congr' (g' := D.arg) fun S _ => ?_, mixedDiff_descr_arg D hk hkN π]
    have h := abs_lt.mp (hb S)
    have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz0
    unfold Descr.unit
    rw [MaxNN.relu_of_nonneg (by linarith [h.1])]

/-! ## The digit argument -/

theorem descr_balanced_of_arg_eq_zero (D : Descr N) {k B : ℕ}
    (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hB : ∑ o, |(D.h o : ℝ)| + (D.M.card : ℝ) < B)
    (π : Equiv.Perm (Fin N)) (h : D.arg (basePtR k B π) = 0) :
    Balanced (DAdj D) (DKappa D) k π := by
  classical
  have hsumh : 0 ≤ ∑ o, |(D.h o : ℝ)| := Finset.sum_nonneg (fun o _ => abs_nonneg _)
  have hBpos : (0 : ℝ) < B := by
    have : (0 : ℝ) ≤ (D.M.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hBpos)
  obtain ⟨ai, hai⟩ : ∃ ai : Fin N → Fin N → ℤ,
      ∀ i j, ai i j = if (i, j) ∈ D.M ∧ π i < π j then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨z, hz_def⟩ : ∃ z : Fin N → ℤ,
      ∀ o, z o = D.h o + ∑ x, (ai o x - ai x o) := ⟨_, fun _ => rfl⟩
  have hnoself : ∀ o, (o, o) ∉ D.M := fun o h => lt_irrefl o (hlt _ h)
  have hsumM : ∀ g : Fin N → Fin N → ℝ, ∑ p in D.M, g p.1 p.2 =
      ∑ i, ∑ j, if (i, j) ∈ D.M then g i j else 0 := by
    intro g
    rw [← Finset.sum_product', ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp
  have hpair : ∀ i j, (if (i, j) ∈ D.M then
      MaxNN.relu (basePtR k B π i - basePtR k B π j) else 0) =
        (ai i j : ℝ) * basePtR k B π i - (ai i j : ℝ) * basePtR k B π j := by
    intro i j
    rw [hai]
    by_cases hp : (i, j) ∈ D.M
    · have hr : MaxNN.relu (basePtR k B π i - basePtR k B π j) =
          if π i < π j then basePtR k B π i - basePtR k B π j else 0 :=
        relu_basePtR hB1 π (ne_of_lt (hlt _ hp))
      rw [if_pos hp, hr]
      by_cases hl : π i < π j
      · simp [hp, hl]
      · simp [hp, hl]
    · simp [hp]
  have hA : D.arg (basePtR k B π) = ∑ o, (z o : ℝ) * basePtR k B π o := by
    unfold Descr.arg
    rw [hsumM (fun i j => MaxNN.relu (basePtR k B π i - basePtR k B π j))]
    simp only [hpair]
    have hswap : ∑ i, ∑ j, (ai i j : ℝ) * basePtR k B π j =
        ∑ o, ∑ x, (ai x o : ℝ) * basePtR k B π o := Finset.sum_comm
    simp only [Finset.sum_sub_distrib, hswap, hz_def]
    push_cast
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
  have hZ : ∑ o, z o * basePt k B π o = 0 := by
    have : ((∑ o, z o * basePt k B π o : ℤ) : ℝ) = 0 := by
      push_cast; rw [← h, hA]; rfl
    exact_mod_cast this
  have hS : ∑ o in univ.filter (fun o => k ≤ ((π o : Fin N) : ℕ)),
      z o * (B : ℤ) ^ ((π o : Fin N) : ℕ) = 0 := by
    have : ∑ o, z o * basePt k B π o = -∑ o in univ.filter (fun o => k ≤ ((π o : Fin N) : ℕ)),
        z o * (B : ℤ) ^ ((π o : Fin N) : ℕ) := by
      rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro o _
      unfold basePt
      split_ifs with h1 h2 h2 <;> first | omega | ring
    linarith
  have hdeg : ∀ o, ∑ x, |(ai o x : ℝ) - ai x o| ≤ D.M.card := by
    intro o
    have h1 : (D.M.card : ℝ) = ∑ i, ∑ j, if (i, j) ∈ D.M then (1 : ℝ) else 0 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact hsumM (fun _ _ => (1 : ℝ))
    have h2 : ∀ x, |(ai o x : ℝ) - ai x o| ≤
        (if (o, x) ∈ D.M then (1 : ℝ) else 0) + (if (x, o) ∈ D.M then 1 else 0) := by
      intro x
      rw [hai, hai]
      by_cases hp1 : (o, x) ∈ D.M <;> by_cases hp2 : (x, o) ∈ D.M <;>
        by_cases hl1 : π o < π x <;> by_cases hl2 : π x < π o <;> simp [hp1, hp2, hl1, hl2]
    have e1 : ∑ x, (if (o, x) ∈ D.M then (1 : ℝ) else 0) =
        ∑ i, ∑ j, if i = o then (if (i, j) ∈ D.M then (1 : ℝ) else 0) else 0 := by
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq']
    have e2 : ∑ x, (if (x, o) ∈ D.M then (1 : ℝ) else 0) =
        ∑ i, ∑ j, if j = o then (if (i, j) ∈ D.M then (1 : ℝ) else 0) else 0 := by
      simp [Finset.sum_ite_eq']
    calc ∑ x, |(ai o x : ℝ) - ai x o|
        ≤ ∑ x, ((if (o, x) ∈ D.M then (1 : ℝ) else 0) + (if (x, o) ∈ D.M then 1 else 0)) :=
          Finset.sum_le_sum fun x _ => h2 x
      _ = ∑ i, ∑ j, ((if i = o then (if (i, j) ∈ D.M then (1 : ℝ) else 0) else 0) +
            (if j = o then (if (i, j) ∈ D.M then (1 : ℝ) else 0) else 0)) := by
          rw [Finset.sum_add_distrib, e1, e2, ← Finset.sum_add_distrib]
          simp only [Finset.sum_add_distrib]
      _ ≤ ∑ i, ∑ j, if (i, j) ∈ D.M then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          by_cases hp : (i, j) ∈ D.M
          · have hij := hlt _ hp
            by_cases hi : i = o
            · have hj : j ≠ o := fun hj => by subst hi; subst hj; exact lt_irrefl _ hij
              simp [hp, hi, hj]
            · simp only [hp, hi, if_true, if_false, zero_add]
              split_ifs <;> norm_num
          · simp [hp]
      _ = D.M.card := h1.symm
  have hbound : ∀ o, |z o| < (B : ℤ) := by
    intro o
    have hr : |((z o : ℤ) : ℝ)| < B := by
      rw [hz_def]
      push_cast
      calc |(D.h o : ℝ) + ∑ x, ((ai o x : ℝ) - ai x o)|
          ≤ |(D.h o : ℝ)| + ∑ x, |(ai o x : ℝ) - ai x o| :=
            (abs_add _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
        _ ≤ ∑ o', |(D.h o' : ℝ)| + D.M.card := by
            apply add_le_add
            · exact Finset.single_le_sum (f := fun o' => |(D.h o' : ℝ)|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ o)
            · exact hdeg o
        _ < B := hB
    have : ((|z o| : ℤ) : ℝ) < ((B : ℤ) : ℝ) := by push_cast; exact hr
    exact_mod_cast this
  intro o ho
  have hinj : Set.InjOn (fun o : Fin N => ((π o : Fin N) : ℕ))
      ↑(univ.filter (fun o => k ≤ ((π o : Fin N) : ℕ))) :=
    fun a _ b _ hab => π.injective (Fin.ext hab)
  have hz0 : z o = 0 :=
    digits_eq_zero (B := (B : ℤ)) (by exact_mod_cast hB1) _ z _ hinj (fun o _ => hbound o) hS o
      (by simp [ho])
  have hk : DKappa D o - upCount (DAdj D) π o = (z o : ℝ) := by
    have hfil : ((D.M.filter fun m => m.1 = o).card : ℝ) =
        ∑ x, if (o, x) ∈ D.M then (1 : ℝ) else 0 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
      rw [hsumM (fun i _ => if i = o then (1 : ℝ) else 0)]
      rw [Finset.sum_eq_single o]
      · simp only [if_true]
      · intro b _ hb
        simp [hb]
      · simp
    unfold DKappa upCount
    rw [hfil, Finset.natCast_card_filter, hz_def]
    push_cast
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [hai, hai]
    unfold DAdj
    by_cases hxo : x = o
    · subst hxo
      simp [hnoself]
    · have hπ : π x ≠ π o := fun h => hxo (π.injective h)
      by_cases hp1 : (o, x) ∈ D.M
      · have hox := hlt _ hp1
        have hp2 : (x, o) ∉ D.M := fun h => absurd (hlt _ h) (not_lt.mpr hox.le)
        rcases lt_or_gt_of_ne hπ with hl | hl
        · simp [hp1, hp2, hl, hl.not_lt]
        · simp [hp1, hp2, hl, hl.not_lt]
      · by_cases hp2 : (x, o) ∈ D.M
        · simp [hp1, hp2]
        · simp [hp1, hp2]
  have : (z o : ℝ) = 0 := by exact_mod_cast hz0
  linarith

end Units

end MaxCaterpillar.Trees
