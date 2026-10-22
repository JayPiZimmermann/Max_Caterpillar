import MaxCaterpillar.CountLower.Functional

/-! # Base-`B` digits and the three-sets passed by one face function

Steps 4 and 5 of the count.  At the base point of a three-set `T`, the integer
preactivation is a base-`B` expansion whose digits are the coefficients
`coeffZ`; it vanishes only if all digits outside `T` vanish.  Combined with the
apex and the sum of the head, this confines `T` to at most `N - 2` three-sets
per face function.
-/

open BigOperators

namespace MaxCaterpillar.CountLower

open MaxNN

variable {N : ℕ}

/-! ## Expansion of the preactivation by coordinates -/

/-- The coefficient of `z o` in the preactivation at the integer point `z`. -/
def coeffZ (D : Descr N) (z : Fin N → ℤ) (o : Fin N) : ℤ :=
  D.h o + (∑ m in D.M, if m.1 = o ∧ z m.2 < z o then 1 else 0)
    - ∑ m in D.M, if m.2 = o ∧ z o < z m.1 then 1 else 0

theorem sum_fiber (s : Finset (Fin N × Fin N)) (f : Fin N × Fin N → Fin N)
    (P : Fin N × Fin N → Fin N → Prop) [∀ m o, Decidable (P m o)] (g : Fin N → ℤ) :
    ∑ o, g o * (∑ m in s, if f m = o ∧ P m o then (1 : ℤ) else 0) =
      ∑ m in s, if P m (f m) then g (f m) else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [ite_and]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem argZ_eq_sum_coeffZ (D : Descr N) (z : Fin N → ℤ) :
    D.argZ z = ∑ o, z o * coeffZ D z o := by
  unfold Descr.argZ coeffZ
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_fiber D.M (fun m => m.1) (fun m o => z m.2 < z o) z,
    sum_fiber D.M (fun m => m.2) (fun m o => z o < z m.1) z]
  have hmax : ∀ m ∈ D.M, max 0 (z m.1 - z m.2) =
      (if z m.2 < z m.1 then z m.1 else 0) - (if z m.2 < z m.1 then z m.2 else 0) := by
    intro m _
    split_ifs with h
    · rw [max_eq_right (by omega)]
    · rw [max_eq_left (by omega)]
      ring
  rw [Finset.sum_congr rfl hmax, Finset.sum_sub_distrib]
  simp only [mul_comm (D.h _) (z _)]
  ring

/-- K1 makes the digits sum to zero, at every integer point. -/
theorem sum_coeffZ (D : Descr N) (hsum : ∑ o, D.h o = 0) (z : Fin N → ℤ) :
    ∑ o, coeffZ D z o = 0 := by
  unfold coeffZ
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]
  have h1 := sum_fiber D.M (fun m => m.1) (fun m o => z m.2 < z o) (fun _ => 1)
  have h2 := sum_fiber D.M (fun m => m.2) (fun m o => z o < z m.1) (fun _ => 1)
  simp only [one_mul] at h1 h2
  rw [h1, h2]
  ring

theorem abs_coeffZ_le (D : Descr N) (z : Fin N → ℤ) (o : Fin N) :
    |coeffZ D z o| ≤ |D.h o| + D.M.card := by
  unfold coeffZ
  have hle : ∀ P : Fin N × Fin N → Prop, ∀ [DecidablePred P],
      0 ≤ (∑ m in D.M, if P m then (1 : ℤ) else 0) ∧
        (∑ m in D.M, if P m then (1 : ℤ) else 0) ≤ D.M.card := by
    intro P _
    constructor
    · exact Finset.sum_nonneg fun m _ => by split_ifs <;> norm_num
    · calc (∑ m in D.M, if P m then (1 : ℤ) else 0) ≤ ∑ _m in D.M, (1 : ℤ) :=
            Finset.sum_le_sum fun m _ => by split_ifs <;> norm_num
        _ = D.M.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  obtain ⟨h1, h2⟩ := hle (fun m => m.1 = o ∧ z m.2 < z o)
  obtain ⟨h3, h4⟩ := hle (fun m => m.2 = o ∧ z o < z m.1)
  rw [abs_le]
  constructor
  · linarith [(abs_le.mp (le_refl |D.h o|)).1]
  · linarith [le_abs_self (D.h o)]

/-! ## Base-`B` digits (step 4) -/

theorem abs_digits_lt {B : ℤ} (hB : 0 < B) :
    ∀ (n : ℕ) (g : ℕ → ℤ), (∀ i < n, |g i| < B) →
      |∑ i in Finset.range n, g i * B ^ i| < B ^ n := by
  intro n
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    have h1 := ih g fun i hi => hg i (Nat.lt_succ_of_lt hi)
    have h2 : |g n| ≤ B - 1 := by linarith [hg n (Nat.lt_succ_self n)]
    have hp : 0 < B ^ n := pow_pos hB n
    rw [Finset.sum_range_succ, pow_succ]
    calc |∑ i in Finset.range n, g i * B ^ i + g n * B ^ n|
        ≤ |∑ i in Finset.range n, g i * B ^ i| + |g n * B ^ n| := abs_add _ _
      _ = |∑ i in Finset.range n, g i * B ^ i| + |g n| * B ^ n := by
          rw [abs_mul, abs_of_pos hp]
      _ ≤ (B ^ n - 1) + (B - 1) * B ^ n := by
          have := mul_le_mul_of_nonneg_right h2 hp.le
          linarith
      _ < B * B ^ n := by ring_nf; linarith

theorem digits_eq_zero {B : ℤ} (hB : 0 < B) :
    ∀ (n : ℕ) (g : ℕ → ℤ), (∀ i < n, |g i| < B) →
      ∑ i in Finset.range n, g i * B ^ i = 0 → ∀ i < n, g i = 0 := by
  intro n
  induction n with
  | zero => intro g _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro g hg hsum
    have hlow := abs_digits_lt hB n g fun i hi => hg i (Nat.lt_succ_of_lt hi)
    rw [Finset.sum_range_succ] at hsum
    have hp : 0 < B ^ n := pow_pos hB n
    have hgn : g n = 0 := by
      by_contra hne
      have h1 : 1 ≤ |g n| := Int.one_le_abs hne
      have h2 : |g n * B ^ n| = |∑ i in Finset.range n, g i * B ^ i| := by
        rw [show g n * B ^ n = -∑ i in Finset.range n, g i * B ^ i by linarith, abs_neg]
      rw [abs_mul, abs_of_pos hp] at h2
      nlinarith
    have hrest : ∑ i in Finset.range n, g i * B ^ i = 0 := by
      rw [hgn, zero_mul, add_zero] at hsum
      exact hsum
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih g (fun j hj => hg j (Nat.lt_succ_of_lt hj)) hrest i hi
    · rw [hi]; exact hgn

theorem fin_digits_eq_zero {B : ℤ} (hB : 0 < B) (f : Fin N → ℤ) (hf : ∀ o, |f o| < B)
    (h : ∑ o, f o * B ^ (o.val + 1) = 0) (o : Fin N) : f o = 0 := by
  let g : ℕ → ℤ := fun i => if hi : i < N then f ⟨i, hi⟩ else 0
  have hg : ∀ o : Fin N, g o = f o := fun o => by
    simp only [g, dif_pos o.isLt, Fin.eta]
  have hsum : ∑ i in Finset.range N, g i * B ^ i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => g i * B ^ i) N]
    have : B * ∑ o : Fin N, g o * B ^ (o : ℕ) = 0 := by
      rw [Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hg, pow_succ]
      ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hB.ne'
    · exact h0
  have := digits_eq_zero hB N g (fun i hi => by
    have := hf ⟨i, hi⟩
    simpa only [g, dif_pos hi] using this) hsum o.val o.isLt
  rw [hg] at this
  exact this

/-- **Step 4.** A vanishing preactivation at the base point forces every digit
outside `T` to vanish. -/
theorem coeffZ_eq_zero (D : Descr N) {T : Finset (Fin N)} {B : ℕ}
    (hB : ∑ o, |D.h o| + D.M.card < B) (hA : D.argZ (baseZ T B) = 0)
    {o : Fin N} (ho : o ∉ T) : coeffZ D (baseZ T B) o = 0 := by
  let f : Fin N → ℤ := fun o => if o ∈ T then 0 else coeffZ D (baseZ T B) o
  have hpos : (0 : ℤ) < B := by
    have : (0 : ℤ) ≤ ∑ o, |D.h o| := Finset.sum_nonneg fun o _ => abs_nonneg _
    have : (0 : ℤ) ≤ D.M.card := Nat.cast_nonneg _
    linarith
  have hf : ∀ o, |f o| < B := by
    intro o
    simp only [f]
    split_ifs
    · rw [abs_zero]; exact hpos
    · have h1 := abs_coeffZ_le D (baseZ T B) o
      have h2 : |D.h o| ≤ ∑ o, |D.h o| :=
        Finset.single_le_sum (fun o _ => abs_nonneg (D.h o)) (Finset.mem_univ o)
      linarith
  have hsum : ∑ o, f o * (B : ℤ) ^ (o.val + 1) = 0 := by
    rw [argZ_eq_sum_coeffZ] at hA
    rw [← neg_eq_zero, ← hA, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [f, baseZ]
    split_ifs <;> ring
  have := fin_digits_eq_zero hpos f hf hsum o
  simpa only [f, if_neg ho] using this

/-! ## The three-sets passed by one face function (step 5) -/

/-- The key facts: K1 (`∑ h = 0`), K2 (an apex with head `-1` met by no
pair), oriented pairs, and K4 (`|M| ≤ N - 2`). -/
def Good (D : Descr N) (apex : Fin N) : Prop :=
  ∑ o, D.h o = 0 ∧ D.h apex = -1 ∧
    (∀ m ∈ D.M, m.1 < m.2 ∧ m.1 ≠ apex ∧ m.2 ≠ apex) ∧ D.M.card + 2 ≤ N

/-- `κ_o = h_o + #{j : (o, j) ∈ M}`. -/
def kappa (D : Descr N) (o : Fin N) : ℤ := D.h o + ∑ m in D.M, if m.1 = o then 1 else 0

/-- The admissible three-sets of a face function: those containing the apex
and a second vertex of negative `κ` if there is one, and otherwise the apex
together with a pair of `M`. -/
noncomputable def allowed (D : Descr N) (apex : Fin N) : Finset (Finset (Fin N)) := by
  classical
  exact if h : ∃ n, n ≠ apex ∧ kappa D n < 0 then
    ((Finset.univ.erase apex).erase h.choose).image fun x => {apex, h.choose, x}
  else D.M.image fun m => {apex, m.1, m.2}

theorem card_allowed {D : Descr N} {apex : Fin N} (hG : Good D apex) :
    (allowed D apex).card ≤ N - 2 := by
  classical
  unfold allowed
  split_ifs with h
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h.choose_spec.1, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rfl
  · have h1 := hG.2.2.2
    have h2 : D.M.card ≤ N - 2 := by omega
    exact Finset.card_image_le.trans h2

theorem exists_third {T : Finset (Fin N)} (hT : T.card = 3) (x y : Fin N) :
    ∃ z ∈ T, z ≠ x ∧ z ≠ y := by
  by_contra h
  push_neg at h
  have hsub : T ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · rw [hzx]; exact Finset.mem_insert_self _ _
    · rw [h z hz hzx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := Finset.card_le_of_subset hsub
  have h2 := Finset.card_insert_le x ({y} : Finset (Fin N))
  rw [Finset.card_singleton] at h2
  omega

theorem eq_triple {T : Finset (Fin N)} (hT : T.card = 3) {x y z : Fin N}
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    T = {x, y, z} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  · rw [hT, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_singleton]
    · simpa using hyz
    · simp [hxy, hxz]

theorem coeffZ_mem {D : Descr N} {T : Finset (Fin N)} {B : ℕ} (hB : 1 ≤ B)
    {t : Fin N} (ht : t ∈ T) : coeffZ D (baseZ T B) t = vZ D T t := by
  unfold coeffZ vZ outZ
  have hneg : ∀ o, baseZ T B o < 0 ↔ o ∉ T := by
    intro o
    unfold baseZ
    split_ifs with h
    · simp [h]
    · simp only [h, not_false_eq_true, iff_true, Left.neg_neg_iff]
      exact pow_pos (by exact_mod_cast hB) _
  have hnp : ∀ o, ¬ (0 < baseZ T B o) := by
    intro o
    unfold baseZ
    split_ifs
    · exact lt_irrefl 0
    · simp only [Left.neg_pos_iff, not_lt]
      exact (pow_pos (by exact_mod_cast hB) _).le
  rw [baseZ_of_mem ht]
  have h2 : (∑ m in D.M, if m.2 = t ∧ (0 : ℤ) < baseZ T B m.1 then (1 : ℤ) else 0) = 0 :=
    Finset.sum_eq_zero fun m _ => if_neg fun h => hnp _ h.2
  rw [h2, sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hneg]

/-- **Step 5.** Every three-set passed by a face function is admissible. -/
theorem mem_allowed {D : Descr N} {apex : Fin N} (hG : Good D apex)
    {T : Finset (Fin N)} {a b c : Fin N} (hT : T = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {B : ℕ}
    (hB : ∑ o, |D.h o| + D.M.card < B)
    (hpass : D.argZ (baseZ T B) = 0 ∧
      (PairIn D T ∨ (vZ D T a ≠ 0 ∧ vZ D T b ≠ 0 ∧ vZ D T a + vZ D T b ≠ 0))) :
    T ∈ allowed D apex := by
  classical
  obtain ⟨hK1, hK2, hpairs, _⟩ := hG
  have hB1 : 1 ≤ B := by
    have : (0 : ℤ) ≤ ∑ o, |D.h o| := Finset.sum_nonneg fun o _ => abs_nonneg _
    have : (0 : ℤ) ≤ D.M.card := Nat.cast_nonneg _
    have : (1 : ℤ) ≤ B := by linarith
    exact_mod_cast this
  have hcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_singleton]
    · simpa using hbc
    · simp [hab, hac]
  have haT : a ∈ T := by rw [hT]; simp
  have hbT : b ∈ T := by rw [hT]; simp
  have hcT : c ∈ T := by rw [hT]; simp
  have hzero := fun o (ho : o ∉ T) => coeffZ_eq_zero D hB hpass.1 ho
  -- the apex lies in `T`
  have hapex : apex ∈ T := by
    by_contra hn
    have h := hzero apex hn
    unfold coeffZ at h
    rw [Finset.sum_eq_zero fun m hm => if_neg fun h => (hpairs m hm).2.1 h.1,
      Finset.sum_eq_zero fun m hm => if_neg fun h => (hpairs m hm).2.2 h.1, hK2] at h
    norm_num at h
  -- vertices outside `T` have `κ ≥ 0`
  have hkappa : ∀ o, o ∉ T → 0 ≤ kappa D o := by
    intro o ho
    have h := hzero o ho
    unfold coeffZ at h
    unfold kappa
    have h1 : (∑ m in D.M, if m.1 = o ∧ baseZ T B m.2 < baseZ T B o then (1 : ℤ) else 0) ≤
        ∑ m in D.M, if m.1 = o then (1 : ℤ) else 0 :=
      Finset.sum_le_sum fun m _ => by
        by_cases h1 : m.1 = o
        · simp only [h1, true_and]
          split_ifs <;> norm_num
        · simp [h1]
    have h2 : 0 ≤ (∑ m in D.M, if m.2 = o ∧ baseZ T B o < baseZ T B m.1 then (1 : ℤ) else 0) :=
      Finset.sum_nonneg fun m _ => by split_ifs <;> norm_num
    linarith
  -- the local heads sum to zero
  have hsumv : vZ D T a + vZ D T b + vZ D T c = 0 := by
    have hs := sum_coeffZ D hK1 (baseZ T B)
    have hs' : ∑ o, coeffZ D (baseZ T B) o =
        ∑ o, if o ∈ T then coeffZ D (baseZ T B) o else 0 :=
      Finset.sum_congr rfl fun o _ => by
        split_ifs with ho
        · rfl
        · exact hzero o ho
    rw [hs', Finset.sum_ite_mem, Finset.univ_inter] at hs
    have hs3 : ∑ t in ({a, b, c} : Finset (Fin N)), coeffZ D (baseZ T B) t = 0 := by
      rw [← hT]; exact hs
    rw [Finset.sum_insert (by simp [hab, hac]),
      Finset.sum_insert (by simpa using hbc), Finset.sum_singleton] at hs3
    rw [coeffZ_mem hB1 haT, coeffZ_mem hB1 hbT, coeffZ_mem hB1 hcT] at hs3
    linarith
  unfold allowed
  by_cases hneg : ∃ n, n ≠ apex ∧ kappa D n < 0
  · rw [dif_pos hneg]
    obtain ⟨hn1, hn2⟩ := hneg.choose_spec
    have hnT : hneg.choose ∈ T := by
      by_contra h
      exact absurd (hkappa _ h) (not_le.mpr hn2)
    obtain ⟨x, hxT, hx1, hx2⟩ := exists_third hcard apex hneg.choose
    refine Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr
      ⟨hx1, Finset.mem_univ _⟩⟩, ?_⟩
    exact (eq_triple hcard hapex hnT hxT (Ne.symm hn1) (Ne.symm hx1) (Ne.symm hx2)).symm
  · rw [dif_neg hneg]
    by_cases hP : PairIn D T
    · obtain ⟨m, hm, h1, h2⟩ := hP
      obtain ⟨hlt, hm1, hm2⟩ := hpairs m hm
      refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
      exact (eq_triple hcard hapex h1 h2 (Ne.symm hm1) (Ne.symm hm2) (ne_of_lt hlt)).symm
    · exfalso
      have hv := hpass.2.resolve_left hP
      push_neg at hneg
      -- inside `T` the local head is `κ`
      have hvk : ∀ t ∈ T, vZ D T t = kappa D t := by
        intro t ht
        unfold vZ outZ kappa
        congr 1
        refine Finset.sum_congr rfl fun m hm => ?_
        by_cases h1 : m.1 = t
        · have h2 : m.2 ∉ T := fun h2 => hP ⟨m, hm, h1 ▸ ht, h2⟩
          simp [h1, h2]
        · simp [h1]
      have hka : kappa D apex = -1 := by
        unfold kappa
        rw [Finset.sum_eq_zero fun m hm => if_neg (hpairs m hm).2.1, hK2]
        rfl
      have hval : ∀ t ∈ T, (t = apex → vZ D T t = -1) ∧ (t ≠ apex → 0 ≤ vZ D T t) := by
        intro t ht
        refine ⟨fun h => by rw [hvk t ht, h, hka], fun h => ?_⟩
        rw [hvk t ht]
        exact hneg t h
      obtain ⟨ha1, ha2⟩ := hval a haT
      obtain ⟨hb1, hb2⟩ := hval b hbT
      obtain ⟨hc1, hc2⟩ := hval c hcT
      have happ : apex = a ∨ apex = b ∨ apex = c := by
        rw [hT] at hapex
        simpa using hapex
      obtain ⟨hva, hvb, hvab⟩ := hv
      rcases lt_or_gt_of_ne hva with h1 | h1 <;> rcases lt_or_gt_of_ne hvb with h2 | h2 <;>
        rcases lt_or_gt_of_ne hvab with h3 | h3 <;> rcases happ with rfl | rfl | rfl
      all_goals first
        | (have := ha1 rfl; have := hb2 hab.symm; have := hc2 hac.symm; omega)
        | (have := hb1 rfl; have := ha2 hab; have := hc2 hbc.symm; omega)
        | (have := hc1 rfl; have := ha2 hac; have := hb2 hbc; omega)

end MaxCaterpillar.CountLower
