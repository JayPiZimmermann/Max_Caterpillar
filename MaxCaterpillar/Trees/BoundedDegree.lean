import MaxCaterpillar.Trees.DescrPass
import MaxCaterpillar.Trees.Quadratic
import Mathlib.Data.Complex.ExponentialBounds

/-!
# An exponential count for trees of bounded hinge degree

Let every unit of an expansion of `max_N` be a face function of a pyramid over an
arbitrary tree whose *hinge forest* (the edges kept as hinges) has maximum degree at
most `Δ`.  Then `C(N, k) ≤ 2 (12Δ - 6)^k |K|` for `3 ≤ k ≤ N`, hence
`(12Δ - 5)^N ≤ 2 (N + 1) (12Δ - 6)^N |K|`.

Per unit (`A = 2Δ - 1`, `e = |M|`):
* isolated vertices of the hinge forest are in the tie set `T` iff `κ ≠ 0`
  (conditions (a) and (s)), so `T` is determined by `T ∩ V(M)`, a `j`-subset of the
  at most `2e` non-isolated vertices, `j ≤ k`;
* two balanced orders with the same tie set orient every hinge edge outside `T`
  alike (a forest orientation is determined by its in-degrees; leaf argument);
* at most `Δ k` hinge edges meet `T`, and the remaining ones contain a matching `P`
  with `A |P| ≥ e - Δ k`; prescribing the order of `|P|` disjoint pairs divides the
  count of orders by `2^|P|`;
* `C(2e, j) ≤ 2^p (6A)^k` whenever `2e ≤ 2(A p + Δ k)` (from `(1 + 1/(3A))^(2A) ≤ 2`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

/-! ## The analytic inequality -/

theorem one_add_pow_le_two (A : ℕ) (hA : 1 ≤ A) :
    (1 + 1 / (3 * (A : ℝ))) ^ (2 * A) ≤ 2 := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have h1 : 1 + 1 / (3 * (A : ℝ)) ≤ Real.exp (1 / (3 * (A : ℝ))) := by
    have := Real.add_one_le_exp (1 / (3 * (A : ℝ)))
    linarith
  have h2 : (1 + 1 / (3 * (A : ℝ))) ^ (2 * A) ≤ Real.exp (1 / (3 * (A : ℝ))) ^ (2 * A) :=
    pow_le_pow_left (by positivity) h1 _
  rw [← Real.exp_nat_mul] at h2
  have h3 : ((2 * A : ℕ) : ℝ) * (1 / (3 * (A : ℝ))) = 2 / 3 := by
    push_cast
    field_simp
    ring
  rw [h3] at h2
  have h4 : Real.exp (2 / 3) ≤ 2 := by
    rw [← Real.le_log_iff_exp_le (by norm_num)]
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  linarith

theorem choose_le_aux {n j p k A Δ : ℕ} (hA : 1 ≤ A) (hΔ : Δ ≤ A) (hj : j ≤ k)
    (hn : n ≤ 2 * (A * p + Δ * k)) :
    (n.choose j : ℝ) ≤ 2 ^ p * (6 * A) ^ k := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (3 * (A : ℝ)) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : (1 : ℝ) ≤ 1 + y := by linarith
  have h2A := one_add_pow_le_two A hA
  rw [← hy] at h2A
  -- `C(n, j) y^j ≤ (1 + y)^n`
  have hbin : (n.choose j : ℝ) * y ^ j ≤ (1 + y) ^ n := by
    by_cases hjn : j ≤ n
    · rw [add_comm, add_pow]
      simp only [one_pow, mul_one]
      have hmem : j ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hjn)
      rw [mul_comm]
      exact single_le_sum (f := fun m => y ^ m * (n.choose m : ℝ))
        (fun m _ => by positivity) hmem
    · rw [Nat.choose_eq_zero_of_lt (not_le.mp hjn)]
      simp only [Nat.cast_zero, zero_mul]
      positivity
  -- `(1 + y)^n ≤ 2^p 2^k`
  have hpow : (1 + y) ^ n ≤ 2 ^ p * 2 ^ k := by
    calc (1 + y) ^ n ≤ (1 + y) ^ (2 * A * p + 2 * Δ * k) :=
          pow_le_pow_right hy1 (by nlinarith)
      _ = ((1 + y) ^ (2 * A)) ^ p * ((1 + y) ^ (2 * Δ)) ^ k := by
          rw [pow_add, ← pow_mul, ← pow_mul]
      _ ≤ 2 ^ p * 2 ^ k := by
          apply mul_le_mul (pow_le_pow_left (by positivity) h2A _) _ (by positivity)
            (by positivity)
          apply pow_le_pow_left (by positivity)
          exact (pow_le_pow_right hy1 (by omega)).trans h2A
  have hyj : y ^ j * (3 * (A : ℝ)) ^ j = 1 := by
    rw [← mul_pow, hy, one_div, inv_mul_cancel (by positivity), one_pow]
  have h3 : (n.choose j : ℝ) ≤ 2 ^ p * 2 ^ k * (3 * (A : ℝ)) ^ j := by
    have := mul_le_mul_of_nonneg_right (hbin.trans hpow) (by positivity : (0 : ℝ) ≤ (3 * (A : ℝ)) ^ j)
    rw [mul_assoc, hyj, mul_one] at this
    exact this
  have h4 : (3 * (A : ℝ)) ^ j ≤ (3 * (A : ℝ)) ^ k :=
    pow_le_pow_right (by have : (1 : ℝ) ≤ A := by exact_mod_cast hA
                         linarith) hj
  calc (n.choose j : ℝ) ≤ 2 ^ p * 2 ^ k * (3 * (A : ℝ)) ^ j := h3
    _ ≤ 2 ^ p * 2 ^ k * (3 * (A : ℝ)) ^ k := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 ^ p * (6 * A) ^ k := by rw [mul_assoc, ← mul_pow]; ring

/-! ## Matchings in graphs of bounded degree -/

/-- The pairs of `E` incident with `o`. -/
def incid {N : ℕ} (E : Finset (Fin N × Fin N)) (o : Fin N) : Finset (Fin N × Fin N) :=
  E.filter fun m => m.1 = o ∨ m.2 = o

/-- Pairwise vertex-disjoint pairs. -/
def VDisj {N : ℕ} (P : Finset (Fin N × Fin N)) : Prop :=
  ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p.1 ≠ p'.1 ∧ p.1 ≠ p'.2 ∧ p.2 ≠ p'.1 ∧ p.2 ≠ p'.2

theorem exists_matching {N Δ : ℕ} (hΔ : 1 ≤ Δ) :
    ∀ n (E : Finset (Fin N × Fin N)), E.card = n → (∀ o, (incid E o).card ≤ Δ) →
      ∃ P ⊆ E, VDisj P ∧ E.card ≤ (2 * Δ - 1) * P.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hEn hdeg
    rcases E.eq_empty_or_nonempty with hE | ⟨m, hm⟩
    · exact ⟨∅, empty_subset _, fun p hp => absurd hp (not_mem_empty p), by simp [hE]⟩
    set E' := E.filter fun m' => ¬ (m'.1 = m.1 ∨ m'.2 = m.1 ∨ m'.1 = m.2 ∨ m'.2 = m.2) with hE'
    have hsub : E \ E' ⊆ incid E m.1 ∪ incid E m.2 := by
      intro x hx
      rw [mem_sdiff, hE', mem_filter] at hx
      push_neg at hx
      have hxE := hx.1
      have := hx.2 hxE
      simp only [incid, mem_union, mem_filter]
      tauto
    have hmin : m ∈ incid E m.1 ∩ incid E m.2 :=
      mem_inter.mpr ⟨mem_filter.mpr ⟨hm, Or.inl rfl⟩, mem_filter.mpr ⟨hm, Or.inr rfl⟩⟩
    have hcard1 : (E \ E').card ≤ 2 * Δ - 1 := by
      have h1 := card_le_of_subset hsub
      have h2 := card_union_add_card_inter (incid E m.1) (incid E m.2)
      have h3 : 1 ≤ (incid E m.1 ∩ incid E m.2).card := card_pos.mpr ⟨m, hmin⟩
      have h4 := hdeg m.1
      have h5 := hdeg m.2
      have h6 : (E \ E').card + 1 ≤ 2 * Δ := by linarith
      exact Nat.le_sub_of_add_le h6
    have hmE' : m ∉ E' := by
      rw [hE', mem_filter]
      push_neg
      intro _
      exact Or.inl rfl
    have hE'sub : E' ⊆ E := filter_subset _ _
    have hlt : E'.card < n := by
      rw [← hEn]
      exact card_lt_card ⟨hE'sub, fun h => hmE' (h hm)⟩
    have hdeg' : ∀ o, (incid E' o).card ≤ Δ := fun o =>
      (card_le_of_subset (filter_subset_filter _ hE'sub)).trans (hdeg o)
    obtain ⟨P', hP'sub, hP'disj, hP'card⟩ := ih _ hlt E' rfl hdeg'
    have hmP' : m ∉ P' := fun h => hmE' (hP'sub h)
    refine ⟨insert m P', insert_subset_iff.mpr ⟨hm, hP'sub.trans hE'sub⟩, ?_, ?_⟩
    · intro p hp p' hp' hpp'
      have far : ∀ q ∈ P', q.1 ≠ m.1 ∧ q.2 ≠ m.1 ∧ q.1 ≠ m.2 ∧ q.2 ≠ m.2 := by
        intro q hq
        have := (mem_filter.mp (hP'sub hq)).2
        push_neg at this
        exact this
      rcases mem_insert.mp hp with h1 | h1 <;> rcases mem_insert.mp hp' with h2 | h2
      · exact absurd (h1.trans h2.symm) hpp'
      · rw [h1]
        have := far p' h2
        exact ⟨this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm⟩
      · rw [h2]
        have := far p h1
        exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2⟩
      · exact hP'disj p h1 p' h2 hpp'
    · rw [card_insert_of_not_mem hmP']
      have hsplit : E.card = E'.card + (E \ E').card := by
        rw [add_comm, card_sdiff_add_card_eq_card hE'sub]
      rw [hsplit, mul_add, mul_one]
      linarith

/-! ## Orientation and isolated vertices -/

section Orient

variable {N : ℕ}

/-- Every nonempty set of pairs of `M` has a vertex met by exactly one of its pairs. -/
def LeafProp (M : Finset (Fin N × Fin N)) : Prop :=
  ∀ E ⊆ M, E.Nonempty → ∃ m ∈ E, ∃ u, (u = m.1 ∨ u = m.2) ∧
    ∀ m' ∈ E, (m'.1 = u ∨ m'.2 = u) → m' = m

theorem upCount_lt_of_mem {k : ℕ} {π : Equiv.Perm (Fin N)} {x u : Fin N}
    (hx : x ∈ tieSet k π) (hu : u ∉ tieSet k π) : π x < π u := by
  rw [mem_tieSet'] at hx
  rw [mem_tieSet'] at hu
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
    by_contra h; exact huT (mem_tieSet'.mpr (by omega))
  have huk' : k ≤ ((π' u : Fin N) : ℕ) := by
    by_contra h; exact huT' (mem_tieSet'.mpr (by omega))
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

/-! ## Counting the passed localities of one unit -/

section Count

open Classical

variable {N : ℕ}

/-- The isolated vertices of the pairs of `D`. -/
noncomputable def isoSet (D : Descr N) : Finset (Fin N) := by
  classical
  exact univ.filter fun o => ∀ x, ¬ DAdj D o x

/-- The isolated vertices with `κ ≠ 0`. -/
noncomputable def isoForced (D : Descr N) : Finset (Fin N) := by
  classical
  exact (isoSet D).filter fun o => DKappa D o ≠ 0

theorem mem_isoSet {D : Descr N} {o : Fin N} : o ∈ isoSet D ↔ ∀ x, ¬ DAdj D o x := by
  classical
  unfold isoSet
  simp

theorem tieSet_inter_isoSet {D : Descr N} {k : ℕ} {π : Equiv.Perm (Fin N)}
    (hp : DPasses D k π) : tieSet k π ∩ isoSet D = isoForced D := by
  classical
  obtain ⟨hbal, hact⟩ := hp
  ext o
  simp only [mem_inter, isoForced, mem_filter]
  constructor
  · rintro ⟨hoT, hoI⟩
    refine ⟨hoI, hact o (mem_tieSet'.mp hoT) fun x _ => mem_isoSet.mp hoI x⟩
  · rintro ⟨hoI, hκ⟩
    refine ⟨?_, hoI⟩
    by_contra hoT
    have hk : k ≤ ((π o : Fin N) : ℕ) := by
      by_contra h; exact hoT (mem_tieSet'.mpr (by omega))
    have h0 := hbal o hk
    have hup : upCount (DAdj D) π o = 0 := by
      unfold upCount
      rw [card_eq_zero, filter_eq_empty_iff]
      intro x _ hx
      exact mem_isoSet.mp hoI x hx.1
    rw [hup, Nat.cast_zero] at h0
    exact hκ h0.symm

theorem card_nonIso_le (D : Descr N) : (univ \ isoSet D).card ≤ 2 * D.M.card := by
  classical
  have hsub : univ \ isoSet D ⊆ D.M.image Prod.fst ∪ D.M.image Prod.snd := by
    intro o ho
    rw [mem_sdiff, mem_isoSet] at ho
    push_neg at ho
    obtain ⟨x, hx⟩ := ho.2
    rw [mem_union, mem_image, mem_image]
    rcases hx with hx | hx
    · exact Or.inl ⟨_, hx, rfl⟩
    · exact Or.inr ⟨_, hx, rfl⟩
  calc (univ \ isoSet D).card ≤ (D.M.image Prod.fst ∪ D.M.image Prod.snd).card :=
        card_le_of_subset hsub
    _ ≤ (D.M.image Prod.fst).card + (D.M.image Prod.snd).card := card_union_le _ _
    _ ≤ D.M.card + D.M.card := add_le_add card_image_le card_image_le
    _ = 2 * D.M.card := by ring

/-- The balanced orders with tie set `T`: a matching outside `T` halves the count. -/
theorem card_balanced_fiber (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2) (hleaf : LeafProp D.M)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ o, (incid D.M o).card ≤ Δ) {k : ℕ} {T : Finset (Fin N)}
    (hT : T.card = k) :
    ∃ p, D.M.card ≤ (2 * Δ - 1) * p + Δ * k ∧
      ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ p ≤ k ! * (N - k)! := by
  classical
  set EO := D.M.filter fun m => m.1 ∉ T ∧ m.2 ∉ T with hEO
  have hrest : D.M \ EO ⊆ T.biUnion (incid D.M) := by
    intro m hm
    rw [mem_sdiff, hEO, mem_filter] at hm
    push_neg at hm
    rw [mem_biUnion]
    by_cases h1 : m.1 ∈ T
    · exact ⟨m.1, h1, mem_filter.mpr ⟨hm.1, Or.inl rfl⟩⟩
    · exact ⟨m.2, hm.2 hm.1 h1, mem_filter.mpr ⟨hm.1, Or.inr rfl⟩⟩
  have hrestc : (D.M \ EO).card ≤ Δ * k := by
    calc (D.M \ EO).card ≤ (T.biUnion (incid D.M)).card := card_le_of_subset hrest
      _ ≤ ∑ t in T, (incid D.M t).card := card_biUnion_le
      _ ≤ ∑ _t in T, Δ := sum_le_sum fun t _ => hdeg t
      _ = Δ * k := by rw [sum_const, hT, smul_eq_mul, mul_comm]
  have hdegO : ∀ o, (incid EO o).card ≤ Δ := fun o =>
    (card_le_of_subset (filter_subset_filter _ (filter_subset _ _))).trans (hdeg o)
  obtain ⟨P0, hP0sub, hP0disj, hP0card⟩ := exists_matching hΔ _ EO rfl hdegO
  have hEOsub : EO ⊆ D.M := filter_subset _ _
  refine ⟨P0.card, ?_, ?_⟩
  · have := card_sdiff_add_card_eq_card hEOsub
    linarith
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
  have hP0M : ∀ m ∈ P0, m ∈ D.M := fun m hm => hEOsub (hP0sub hm)
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
    have := (mem_filter.mp (hP0sub hm)).2
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
    have hmO := (mem_filter.mp (hP0sub hm)).2
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

/-- **Per-unit bound.** A unit whose hinge pairs form a forest of maximum degree `Δ`
passes at most `2 (6(2Δ - 1))^k k! (N - k)!` localities of order `k`. -/
theorem card_passes_le (D : Descr N) (hlt : ∀ m ∈ D.M, m.1 < m.2) (hleaf : LeafProp D.M)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ o, (incid D.M o).card ≤ Δ) {k : ℕ} (hk : k ≤ N) :
    (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) ≤
      2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * (k ! * (N - k)! : ℕ) := by
  classical
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * Δ - 1 := ⟨_, rfl⟩
  rw [← hA]
  have hA1 : 1 ≤ A := by omega
  have hΔA : Δ ≤ A := by omega
  set e := D.M.card
  set F := k ! * (N - k)!
  set pstar := (e - Δ * k) / A
  set iso := isoSet D
  set I0 := isoForced D
  set 𝒯 := ((univ : Finset (Fin N)).powersetCard k).filter fun T => T ∩ iso = I0
  have hcover : (univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k) ⊆
      𝒯.biUnion fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k) := by
    intro π hπ
    have hp := (mem_filter.mp hπ).2
    refine mem_biUnion.mpr ⟨tieSet k π, ?_, ?_⟩
    · refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, card_tieSet hk π⟩, ?_⟩
      exact tieSet_inter_isoSet hp
    · simp only [fiber, mem_filter, mem_univ, true_and]
      exact hp.1
  -- each tie set
  have hper : ∀ T ∈ 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ pstar ≤ F := by
    intro T hT
    have hTk : T.card = k := (mem_powersetCard.mp (mem_filter.mp hT).1).2
    obtain ⟨p, hp, hc⟩ := card_balanced_fiber D hlt hleaf hΔ hdeg hTk
    rw [← hA] at hp
    have hpp : pstar ≤ p := by
      apply Nat.div_le_of_le_mul
      have : e - Δ * k ≤ A * p := by
        generalize A * p = X at hp ⊢; generalize Δ * k = Y at hp ⊢; omega
      linarith [mul_comm A p]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hpp)) hc
  -- the number of tie sets
  obtain ⟨j, hj⟩ : ∃ j, j = k - I0.card := ⟨_, rfl⟩
  have hTcard : 𝒯.card ≤ (univ \ iso).card.choose j := by
    rw [← card_powersetCard]
    apply card_le_card_of_inj_on (fun T => T ∩ (univ \ iso))
    · intro T hT
      obtain ⟨hT1, hT2⟩ := mem_filter.mp hT
      have hTk := (mem_powersetCard.mp hT1).2
      refine mem_powersetCard.mpr ⟨inter_subset_right _ _, ?_⟩
      have hsplit := card_inter_add_card_sdiff T iso
      have hsd : T \ iso = T ∩ (univ \ iso) := by
        ext x; simp [mem_sdiff, mem_inter]
      rw [hT2, hsd, hTk] at hsplit
      show (T ∩ (univ \ iso)).card = j
      omega
    · intro T hT T' hT' he
      have h1 := (mem_filter.mp hT).2
      have h2 := (mem_filter.mp hT').2
      have eT : T = (T ∩ (univ \ iso)) ∪ (T ∩ iso) := by
        ext x; by_cases hx : x ∈ iso <;> simp [hx]
      have eT' : T' = (T' ∩ (univ \ iso)) ∪ (T' ∩ iso) := by
        ext x; by_cases hx : x ∈ iso <;> simp [hx]
      simp only at he
      rw [eT, eT', he, h1, h2]
  have hchoose : ((univ \ iso).card.choose j : ℝ) ≤ 2 ^ (pstar + 1) * (6 * A) ^ k := by
    apply choose_le_aux hA1 hΔA (by rw [hj]; exact Nat.sub_le _ _)
    have h1 := card_nonIso_le D
    have h2 : e - Δ * k < A * (pstar + 1) := by
      have := Nat.lt_mul_div_succ (e - Δ * k) (show 0 < A by omega)
      simpa [pstar, mul_comm] using this
    have h3 : e ≤ A * (pstar + 1) + Δ * k := by
      generalize A * (pstar + 1) = X at h2 ⊢; generalize Δ * k = Y at h2 ⊢; omega
    calc (univ \ iso).card ≤ 2 * e := h1
      _ ≤ 2 * (A * (pstar + 1) + Δ * k) := Nat.mul_le_mul_left _ h3
  -- assemble
  have hsum : (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) *
      2 ^ pstar ≤ 𝒯.card * F := by
    have h1 := card_le_of_subset hcover
    have h2 := (card_biUnion_le (s := 𝒯)
      (t := fun T => (fiber k T).filter (Balanced (DAdj D) (DKappa D) k)))
    have h3 : (∑ T in 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card) *
        2 ^ pstar ≤ 𝒯.card * F := by
      rw [sum_mul]
      calc ∑ T in 𝒯, ((fiber k T).filter (Balanced (DAdj D) (DKappa D) k)).card * 2 ^ pstar
          ≤ ∑ _T in 𝒯, F := sum_le_sum hper
        _ = 𝒯.card * F := by rw [sum_const, smul_eq_mul]
    have h4 : ((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card * 2 ^ pstar ≤
        𝒯.card * F :=
      le_trans (Nat.mul_le_mul_right _ (h1.trans h2)) h3
    exact_mod_cast h4
  have hpos : (0 : ℝ) < 2 ^ pstar := by positivity
  have hT' : (𝒯.card : ℝ) ≤ 2 ^ (pstar + 1) * (6 * A) ^ k :=
    le_trans (by exact_mod_cast hTcard) hchoose
  have : (((univ : Finset (Equiv.Perm (Fin N))).filter (DPasses D k)).card : ℝ) * 2 ^ pstar ≤
      (2 * (6 * A) ^ k * F) * 2 ^ pstar := by
    calc _ ≤ (𝒯.card : ℝ) * F := hsum
      _ ≤ 2 ^ (pstar + 1) * (6 * A) ^ k * F := by
          apply mul_le_mul_of_nonneg_right hT' (by positivity)
      _ = (2 * (6 * A) ^ k * F) * 2 ^ pstar := by rw [pow_succ]; ring
  have := le_of_mul_le_mul_right this hpos
  push_cast at this ⊢
  exact this

end Count

end MaxCaterpillar.Trees
