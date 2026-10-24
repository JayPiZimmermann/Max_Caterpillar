import MaxCaterpillar.Count.Defs
import MaxCaterpillar.Count.Locality

/-!
# The pass conditions for unit descriptions

A description `D = (h, M)` (`CountLower.Descr`, pairs `m.1 < m.2`) *passes* the locality of
`π` (`DPasses`) if every coordinate outside the tie set has exactly `κ_o` hinge neighbours
above it (balanced) and every tie coordinate without a tied hinge neighbour has `κ ≠ 0`
(active).  A unit whose mixed difference is nonzero passes (`descr_pass_of_mixedDiff_ne`),
so every locality is passed by some unit of an expansion (`exists_dpasses`).  Balanced
orders are determined on the forest by its orientation (`orient_eq_of_balanced`), and a
matching of untied edges halves the balanced fiber (`card_balanced_fiber_of_matching`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower Count

variable {N : ℕ}

variable {N : ℕ}

/-- `D` passes the locality of `π`. -/
def DPasses (D : Descr N) (k : ℕ) (π : Equiv.Perm (Fin N)) : Prop :=
  Balanced (DAdj D) (DKappa D) k π ∧ Active (DAdj D) (DKappa D) k π

section Box

variable {k B : ℕ} {δ : ℝ} {π : Equiv.Perm (Fin N)}

theorem abs_boxPt_sub_le (hδ : 0 ≤ δ) (S : Finset (Fin N)) (o : Fin N) :
    |boxPt k B δ π S o - basePtR k B π o| ≤ δ := by
  unfold boxPt
  rw [add_sub_cancel']
  split_ifs
  · rw [abs_of_nonneg hδ]
  · rw [abs_zero]
    exact hδ

end Box

section Units

theorem abs_relu_sub_le (a b : ℝ) : |MaxNN.relu a - MaxNN.relu b| ≤ |a - b| := by
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
  have he := abs_boxPt_sub_le (k := k) (B := B) (π := π) hδ S
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
      refine (abs_relu_sub_le _ _).trans ?_
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
  · exact mixedDiff_eq_zero_of_two hk hkN p.1 p.2 fun x x' h1 h2 => by
      show MaxNN.relu (x p.1 - x p.2) = MaxNN.relu (x' p.1 - x' p.2)
      rw [h1, h2]
  · rw [map_smul, mixedDiff_eq_zero_of_two hk hkN o o fun x x' h _ => h, smul_zero]

theorem descr_arg_boxPt_insert (D : Descr N) {k B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    {π : Equiv.Perm (Fin N)} {t : Fin N} (ht : t ∈ tieSet k π)
    (hnb : ∀ x, ((π x : Fin N) : ℕ) < k → ¬ DAdj D t x)
    (hκ : DKappa D t = 0) {S : Finset (Fin N)} (hS : S ⊆ tieSet k π) (htS : t ∉ S) :
    D.arg (boxPt k B δ π (insert t S)) = D.arg (boxPt k B δ π S) := by
  have hS' : insert t S ⊆ tieSet k π := insert_subset_iff.mpr ⟨ht, hS⟩
  have hy't : boxPt k B δ π (insert t S) t = δ := by
    rw [boxPt_of_mem ht, if_pos (mem_insert_self t S)]
  have hyt : boxPt k B δ π S t = 0 := by
    rw [boxPt_of_mem ht, if_neg htS]
  have hout : ∀ x, DAdj D t x → x ∉ tieSet k π := fun x hx hxT =>
    hnb x (mem_tieSet.mp hxT) hx
  have hlin : ∑ o, (D.h o : ℝ) * boxPt k B δ π (insert t S) o =
      ∑ o, (D.h o : ℝ) * boxPt k B δ π S o + (D.h t : ℝ) * δ := by
    have hd : ∀ o, (D.h o : ℝ) * boxPt k B δ π (insert t S) o =
        (D.h o : ℝ) * boxPt k B δ π S o + if o = t then (D.h t : ℝ) * δ else 0 := by
      intro o
      by_cases hot : o = t
      · subst hot
        rw [hy't, hyt, if_pos rfl]
        ring
      · rw [boxPt_insert_of_ne hot, if_neg hot, add_zero]
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
        rw [if_pos h1, h1, hy't, hyt, boxPt_of_not_mem hS' h2T, boxPt_of_not_mem hS h2T]
        have hb := basePtR_le_neg_one (k := k) (π := π) hB h2T
        rw [MaxNN.relu_of_nonneg (by linarith), MaxNN.relu_of_nonneg (by linarith)]
        ring
      · rw [if_neg h1, add_zero]
        by_cases h2 : p.2 = t
        · have h1T : p.1 ∉ tieSet k π := hout p.1 (Or.inr (by rw [← h2]; exact hp))
          rw [h2, hy't, hyt, boxPt_of_not_mem hS' h1T, boxPt_of_not_mem hS h1T]
          have hb := basePtR_le_neg_one (k := k) (π := π) hB h1T
          rw [MaxNN.relu_of_nonpos (by linarith), MaxNN.relu_of_nonpos (by linarith)]
        · rw [boxPt_insert_of_ne h1, boxPt_insert_of_ne h2]
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
    rw [mixedDiff_congr (g' := 0) fun S _ => ?_, map_zero]
    have h := abs_lt.mp (hb S)
    have hz1 : (z : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hz0
    unfold Descr.unit
    rw [MaxNN.relu_of_nonpos (by linarith [h.2]), Pi.zero_apply]
  · refine ⟨by rw [hz, hz0, Int.cast_zero], ?_⟩
    intro t htk hnb hκ
    apply hne
    have ht : t ∈ tieSet k π := mem_tieSet.mpr htk
    refine mixedDiff_eq_zero_of_insert ht fun S hS htS => ?_
    unfold Descr.unit
    rw [descr_arg_boxPt_insert D hB hδ.le ht hnb hκ hS htS]
  · exfalso
    apply hne
    rw [mixedDiff_congr (g' := D.arg) fun S _ => ?_, mixedDiff_descr_arg D hk hkN π]
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

/-! ## Matchings in graphs of bounded degree -/

/-- Pairwise vertex-disjoint pairs. -/
def VDisj {N : ℕ} (P : Finset (Fin N × Fin N)) : Prop :=
  ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2

/-! ## Orientation and isolated vertices -/

section Orient

variable {N : ℕ}

/-- Every nonempty set of pairs of `M` has a vertex met by exactly one of its pairs. -/
def LeafProp (M : Finset (Fin N × Fin N)) : Prop :=
  ∀ E ⊆ M, E.Nonempty → ∃ m ∈ E, ∃ u, (u = m.1 ∨ u = m.2) ∧
    ∀ m' ∈ E, (m'.1 = u ∨ m'.2 = u) → m' = m

theorem upCount_lt_of_mem {k : ℕ} {π : Equiv.Perm (Fin N)} {x u : Fin N}
    (hx : x ∈ tieSet k π) (hu : u ∉ tieSet k π) : π x < π u := by
  rw [mem_tieSet] at hx
  rw [mem_tieSet] at hu
  exact Fin.lt_iff_val_lt_val.mpr (by omega)

theorem ord_swap (π : Equiv.Perm (Fin N)) {a b : Fin N} (h : a ≠ b) :
    π a < π b ↔ ¬ π b < π a := by
  have hne : π a ≠ π b := fun e => h (π.injective e)
  constructor
  · intro h1 h2; exact lt_asymm h1 h2
  · intro h1; exact lt_of_le_of_ne (not_lt.mp h1) hne

/-- The up-counts of `u` differ when exactly one neighbour `w` changes side. -/
theorem upCount_ne (D : Descr N) {π π' : Equiv.Perm (Fin N)} {u w : Fin N}
    (hadjw : DAdj D u w) (hdiff : ¬ ((π w < π u) ↔ (π' w < π' u)))
    (hother : ∀ x, x ≠ w → DAdj D u x → (π x < π u ↔ π' x < π' u)) :
    upCount (DAdj D) π u ≠ upCount (DAdj D) π' u := by
  classical
  unfold upCount
  set S := univ.filter fun x => DAdj D u x ∧ π x < π u
  set S' := univ.filter fun x => DAdj D u x ∧ π' x < π' u
  have hErase : S.erase w = S'.erase w := by
    ext x
    simp only [S, S', mem_erase, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, ha, ho⟩; exact ⟨hx, ha, (hother x hx ha).mp ho⟩
    · rintro ⟨hx, ha, ho⟩; exact ⟨hx, ha, (hother x hx ha).mpr ho⟩
  have hmemS : w ∈ S ↔ π w < π u := by simp [S, hadjw]
  have hmemS' : w ∈ S' ↔ π' w < π' u := by simp [S', hadjw]
  by_cases hwS : w ∈ S
  · have hwS' : w ∉ S' := fun h => hdiff ⟨fun _ => hmemS'.mp h, fun _ => hmemS.mp hwS⟩
    have e1 := card_erase_add_one hwS
    have e2 : (S'.erase w).card = S'.card := by rw [erase_eq_of_not_mem hwS']
    rw [hErase] at e1
    omega
  · have hwS' : w ∈ S' := by
      by_contra h
      exact hdiff ⟨fun h' => absurd (hmemS.mpr h') hwS, fun h' => absurd (hmemS'.mpr h') h⟩
    have e1 := card_erase_add_one hwS'
    have e2 : (S.erase w).card = S.card := by rw [erase_eq_of_not_mem hwS]
    rw [← hErase] at e1
    omega

/-- Two balanced orders with the same tie set orient every pair outside it alike. -/
theorem orient_eq_of_balanced (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hleaf : LeafProp D.M) {k : ℕ} {π π' : Equiv.Perm (Fin N)}
    (hT : tieSet k π' = tieSet k π)
    (hb : Balanced (DAdj D) (DKappa D) k π) (hb' : Balanced (DAdj D) (DKappa D) k π')
    {m : Fin N × Fin N} (hm : m ∈ D.M) (h1 : m.1 ∉ tieSet k π) (h2 : m.2 ∉ tieSet k π) :
    (π m.1 < π m.2 ↔ π' m.1 < π' m.2) := by
  classical
  set T := tieSet k π
  set bad := D.M.filter fun m => m.1 ∉ T ∧ m.2 ∉ T ∧ ¬ (π m.1 < π m.2 ↔ π' m.1 < π' m.2)
  by_contra hcon
  have hne : bad.Nonempty := ⟨m, mem_filter.mpr ⟨hm, h1, h2, hcon⟩⟩
  obtain ⟨b, hb_bad, u, hu, huniq⟩ := hleaf bad (filter_subset _ _) hne
  obtain ⟨hbM, hb1, hb2, hbdis⟩ := mem_filter.mp hb_bad
  have hb12 : b.1 ≠ b.2 := ne_of_lt (hlt b hbM)
  have huT : u ∉ T := by rcases hu with rfl | rfl <;> assumption
  have huT' : u ∉ tieSet k π' := by rw [hT]; exact huT
  have huk : k ≤ ((π u : Fin N) : ℕ) := by
    by_contra h; exact huT (mem_tieSet.mpr (by omega))
  have huk' : k ≤ ((π' u : Fin N) : ℕ) := by
    by_contra h; exact huT' (mem_tieSet.mpr (by omega))
  have hcount : upCount (DAdj D) π u = upCount (DAdj D) π' u := by
    have := (hb u huk).trans (hb' u huk').symm
    exact_mod_cast this
  -- every other neighbour keeps its side
  have hother_gen : ∀ w, (b = (u, w) ∨ b = (w, u)) →
      ∀ x, x ≠ w → DAdj D u x → (π x < π u ↔ π' x < π' u) := by
    intro w hbw x hxw hadj
    by_cases hxT : x ∈ T
    · exact iff_of_true (upCount_lt_of_mem hxT huT)
        (upCount_lt_of_mem (by rw [hT]; exact hxT) huT')
    have hxu : x ≠ u := by
      rintro rfl
      rcases hadj with h | h <;> exact lt_irrefl _ (hlt _ h)
    have hgood : ∀ m' ∈ D.M, (m' = (u, x) ∨ m' = (x, u)) →
        (π m'.1 < π m'.2 ↔ π' m'.1 < π' m'.2) := by
      intro m' hm'M hm'
      by_contra hc
      have hmbad : m' ∈ bad := by
        refine mem_filter.mpr ⟨hm'M, ?_, ?_, hc⟩ <;>
          rcases hm' with rfl | rfl <;> assumption
      have := huniq m' hmbad (by rcases hm' with rfl | rfl <;> simp)
      apply hxw
      rcases hm' with rfl | rfl <;> rcases hbw with hbw | hbw <;> rw [hbw] at this <;>
        simp only [Prod.mk.injEq] at this
      all_goals first
        | exact this.2 | exact this.1 | exact absurd this.2 hxu | exact absurd this.1 hxu
    rcases hadj with h | h
    · have := hgood _ h (Or.inl rfl)
      simp only at this
      rw [ord_swap π hxu, ord_swap π' hxu]
      exact this.not
    · have := hgood _ h (Or.inr rfl)
      simpa using this
  rcases hu with rfl | rfl
  · -- `u = b.1`, `w = b.2`
    apply upCount_ne D (u := b.1) (w := b.2) (Or.inl hbM) _ (hother_gen b.2 (Or.inl rfl)) hcount
    rw [ord_swap π hb12.symm, ord_swap π' hb12.symm]
    intro h
    exact hbdis (not_iff_not.mp h)
  · apply upCount_ne D (u := b.2) (w := b.1) (Or.inr hbM) hbdis
      (hother_gen b.1 (Or.inr rfl)) hcount

end Orient

/-! ## Every locality is passed by some unit -/

theorem exists_dpasses (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ i ∈ K, DPasses (D i) k π := by
  classical
  set c : ι → ℝ := fun i => ∑ o, |((D i).h o : ℝ)| + 2 * ((D i).M.card : ℝ) with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  set C : ℝ := ∑ i in K, c i
  have hcC : ∀ i ∈ K, c i ≤ C := fun i hi => Finset.single_le_sum (fun i _ => hc0 i) hi
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => hc0 i
  set δ : ℝ := 1 / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set B : ℕ := ⌈C⌉₊ + 1 with hB
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hCB : C < B := by
    rw [hB]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil C) (lt_add_one _)
  have hfun : Maximum (r + 1 + 1) = (∑ i in K, d i • (D i).unit) + auxiliary a := by
    funext x
    rw [h x, Pi.add_apply, Finset.sum_apply]
    rfl
  have hval := congrArg (mixedDiff k B δ π) hfun
  rw [mixedDiff_maximum (le_trans (by norm_num) hk) hkN hB1 hδ0.le, map_add,
    mixedDiff_auxiliary hk hkN B δ π a, add_zero, map_sum] at hval
  have hne : ∑ i in K, mixedDiff k B δ π (d i • (D i).unit) ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hδ0.ne'
  obtain ⟨i, hi, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [map_smul, smul_eq_mul] at hi0
  have hU : mixedDiff k B δ π (D i).unit ≠ 0 := right_ne_zero_of_mul hi0
  have hδb : δ * c i < 1 := by
    calc δ * c i ≤ δ * C := mul_le_mul_of_nonneg_left (hcC i hi) hδ0.le
      _ < δ * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ0
      _ = 1 := by rw [hδ, one_div, inv_mul_cancel (by linarith)]
  obtain ⟨h0, hact⟩ := descr_pass_of_mixedDiff_ne (D i) hk hkN hB1 hδ0 hδb π hU
  have hBk : ∑ o, |((D i).h o : ℝ)| + ((D i).M.card : ℝ) < B := by
    have : ∑ o, |((D i).h o : ℝ)| + ((D i).M.card : ℝ) ≤ c i := by
      simp only [hc]
      have : (0 : ℝ) ≤ ((D i).M.card : ℝ) := Nat.cast_nonneg _
      linarith
    linarith [hcC i hi]
  exact ⟨i, hi, descr_balanced_of_arg_eq_zero (D i) (hlt i hi) hBk π h0, hact⟩

/-! ## Matchings halve the balanced fiber -/

section Matching

open Classical

variable {N : ℕ}

/-- Prescribing a vertex-disjoint set of pairs outside `T` divides the balanced orders
by `2^|P0|`. -/
theorem card_balanced_fiber_of_matching (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2)
    (hleaf : LeafProp D.M) {k : ℕ} {T : Finset (Fin N)} (hT : T.card = k)
    (P0 : Finset (Fin N × Fin N)) (hP0sub : P0 ⊆ D.M) (hP0disj : VDisj P0)
    (hP0out : ∀ m ∈ P0, m.1 ∉ T ∧ m.2 ∉ T) :
    ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ P0.card ≤
      k ! * (N - k)! := by
  by_cases hex : ∃ π₀, π₀ ∈ (fiber k T).filter (Balanced (DAdj D) (DKappa D) k)
  swap
  · rw [not_exists] at hex
    rw [card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr hex), zero_mul]
    exact Nat.zero_le _
  obtain ⟨π₀, hπ₀⟩ := hex
  simp only [fiber, mem_filter, mem_univ, true_and] at hπ₀
  obtain ⟨hπ₀T, hπ₀b⟩ := hπ₀
  let f : Fin N × Fin N → Fin N × Fin N := fun m => if π₀ m.1 < π₀ m.2 then m else (m.2, m.1)
  have hf : ∀ m, f m = m ∨ f m = (m.2, m.1) := fun m => by
    simp only [f]; split_ifs <;> simp
  have hP0M : ∀ m ∈ P0, m ∈ D.M := fun m hm => hP0sub hm
  have hinj : Set.InjOn f P0 := by
    intro m hm m' hm' he
    have l1 := hlt m (hP0M m (mem_coe.mp hm))
    have l2 := hlt m' (hP0M m' (mem_coe.mp hm'))
    rcases hf m with h1 | h1 <;> rcases hf m' with h2 | h2 <;> rw [h1, h2] at he
    · exact he
    · have e1 : m.1 = m'.2 := congrArg Prod.fst he
      have e2 : m.2 = m'.1 := congrArg Prod.snd he
      exfalso; rw [e1, e2] at l1; exact lt_asymm l1 l2
    · have e1 : m.2 = m'.1 := congrArg Prod.fst he
      have e2 : m.1 = m'.2 := congrArg Prod.snd he
      exfalso; rw [← e1, ← e2] at l2; exact lt_asymm l1 l2
    · have e1 : m.2 = m'.2 := congrArg Prod.fst he
      have e2 : m.1 = m'.1 := congrArg Prod.snd he
      exact Prod.ext e2 e1
  set P := P0.image f
  have hPcard : P.card = P0.card := card_image_of_injOn hinj
  have hne : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have := ne_of_lt (hlt m (hP0M m hm))
    rcases hf m with h | h <;> rw [h]
    · exact this
    · exact this.symm
  have hdisj : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
      p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2 := by
    intro p hp p' hp' hpp'
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    obtain ⟨m', hm', rfl⟩ := mem_image.mp hp'
    have hmm' : m ≠ m' := fun h => hpp' (by rw [h])
    have := hP0disj m hm m' hm' hmm'
    rcases hf m with h | h <;> rcases hf m' with h' | h' <;> rw [h, h'] <;> (try dsimp only) <;>
      tauto
  have hout : ∀ p ∈ P, p.1 ∉ T ∧ p.2 ∉ T := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have := hP0out m hm
    rcases hf m with h | h <;> rw [h]
    · exact this
    · exact ⟨this.2, this.1⟩
  have hcount := card_fiber_pairsOrdered hT P hne hdisj hout
  have hsubF : (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) ⊆
      (fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2 := by
    intro π hπ
    simp only [fiber, mem_filter, mem_univ, true_and] at hπ ⊢
    obtain ⟨hπT, hπb⟩ := hπ
    refine ⟨hπT, ?_⟩
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    have hmO := hP0out m hm
    have hTeq : tieSet k π = tieSet k π₀ := hπT.trans hπ₀T.symm
    have hiff := orient_eq_of_balanced D hlt hleaf hTeq hπ₀b hπb (hP0M m hm)
      (by rw [hπ₀T]; exact hmO.1) (by rw [hπ₀T]; exact hmO.2)
    have hm12 : m.1 ≠ m.2 := ne_of_lt (hlt m (hP0M m hm))
    by_cases h : π₀ m.1 < π₀ m.2
    · rw [if_pos h]
      exact hiff.mp h
    · rw [if_neg h]
      show π m.2 < π m.1
      have hn : ¬ π m.1 < π m.2 := fun h' => h (hiff.mpr h')
      have hπne : π m.1 ≠ π m.2 := fun h' => hm12 (π.injective h')
      exact lt_of_le_of_ne (not_lt.mp hn) hπne.symm
  rw [← hPcard]
  calc ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ P.card
      ≤ ((fiber k T).filter fun π => ∀ p ∈ P, π p.1 < π p.2).card * 2 ^ P.card :=
        Nat.mul_le_mul_right _ (card_le_of_subset hsubF)
    _ = k ! * (N - k)! := hcount

theorem dadj_symm {D : Descr N} {u v : Fin N} (h : DAdj D u v) : DAdj D v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

end Matching

end MaxCaterpillar.Trees
