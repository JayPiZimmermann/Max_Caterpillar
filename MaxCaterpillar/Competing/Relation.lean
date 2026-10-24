import MaxCaterpillar.Competing.Defs

/-! # The pyramids of Brunck et al., Sec. 7.1, are caterpillar polytopes or rooted stars

For `N = r + 2` inputs, an apex `v`, an ordering `π` of `[N] ∖ {v}`, and marked positions
`M ⊆ {2, …, N-1}` (Brunck–Hertrich–Rueß–Stade–Yehudayoff, arXiv:2610.28587v1, Eq. (3)):

* `parallelepiped_eq_zonotope`: `B_{v,π,M} = e_{π_q} + ∑_{i=2}^{N-1} [0, e_{π_{r(i)}} - e_{π_i}]`
  with `q = max ({1} ∪ M)` and `r(i) = max ({1} ∪ {j ∈ M : j < i})`;
* `paramidSupport_eq`: `h_{pyr_{e_v}(B_{v,π,M})}(y) =
  y_v + σ(y_{π_q} - y_v + ∑_{i=2}^{N-1} σ(y_{π_{r(i)}} - y_{π_i}))`;
* `paramidSupport_eq_word`: this is `y_v + U_{π',S}` for the word `π' = (v, π₁, …, π_{N-1})`
  and the cut set `S = M - 1`; for `M ≠ ∅` it is a caterpillar function
  (`exists_caterpillarDescription`), for `M = ∅` the rooted star `S_{v,π₁}`
  (`paramidSupport_empty`), which is no caterpillar function (`rootedStar_ne_caterpillarFunction`).
-/

open BigOperators

namespace MaxCaterpillar.BHRSY

open MaxNN.Caterpillar MaxNN.Caterpillar.Corrections

variable {r : ℕ} {v : Fin (r + 1 + 1)} (π : Ordering (r + 1 + 1) v)

/-! ## Positions -/

theorem pos_succ (j : ℕ) (hj : j < r + 1) : π.pos (j + 1) = (π ⟨j, hj⟩).1 := by
  unfold Ordering.pos
  have h : j + 1 - 1 < r + 1 + 1 - 1 := by simpa using hj
  rw [dif_pos h]
  congr 2

theorem word_zero : π.word 0 = v := rfl

theorem word_succ (j : Fin (r + 1)) : π.word j.succ = π.pos ((j : ℕ) + 1) := by
  rw [pos_succ π j j.isLt]
  rfl

theorem pos_eq_word {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r + 1) :
    π.pos i = π.word ⟨i, by omega⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← word_succ π ⟨j, by omega⟩]
  rfl

theorem pos_ne {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r + 1) : π.pos i ≠ v := by
  rw [pos_eq_word π h1 h2]
  intro h
  have := congrArg Fin.val (π.word.injective (h.trans (word_zero π).symm))
  simp only [Fin.val_zero] at this
  omega

theorem pos_inj {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ r + 1) (hj1 : 1 ≤ j) (hj2 : j ≤ r + 1)
    (h : π.pos i = π.pos j) : i = j := by
  rw [pos_eq_word π hi1 hi2, pos_eq_word π hj1 hj2] at h
  exact congrArg Fin.val (π.word.injective h)

theorem pos_surj {k : Fin (r + 1 + 1)} (hk : k ≠ v) :
    ∃ i, 1 ≤ i ∧ i ≤ r + 1 ∧ π.pos i = k := by
  obtain ⟨m, hmk⟩ : ∃ m, π.word m = k := ⟨π.word.symm k, π.word.apply_symm_apply k⟩
  have hm : (m : ℕ) ≠ 0 := by
    intro h
    apply hk
    have : m = 0 := Fin.ext h
    rw [← hmk, this]
    rfl
  have hlt : (m : ℕ) < r + 1 + 1 := m.isLt
  have h1 : 1 ≤ (m : ℕ) := Nat.pos_of_ne_zero hm
  have h2 : (m : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp hlt
  refine ⟨m, h1, h2, ?_⟩
  rw [pos_eq_word π h1 h2, ← hmk]

theorem single_pos_apply {x j : ℕ} (hx1 : 1 ≤ x) (hx2 : x ≤ r + 1) (hj1 : 1 ≤ j)
    (hj2 : j ≤ r + 1) :
    (Pi.single (π.pos x) (1 : ℝ) : Fin (r + 1 + 1) → ℝ) (π.pos j) = if x = j then 1 else 0 := by
  by_cases h : x = j
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (fun he => h (pos_inj π hx1 hx2 hj1 hj2 he.symm)), if_neg h]

theorem single_pos_v {x : ℕ} (hx1 : 1 ≤ x) (hx2 : x ≤ r + 1) :
    (Pi.single (π.pos x) (1 : ℝ) : Fin (r + 1 + 1) → ℝ) v = 0 :=
  Pi.single_eq_of_ne (pos_ne π hx1 hx2).symm _

/-- `∑_k f_k = f_v + ∑_{i=1}^{N-1} f_{π_i}`. -/
theorem sum_univ_split (f : Fin (r + 1 + 1) → ℝ) :
    ∑ k, f k = f v + ∑ i in Finset.Ico 1 (r + 1 + 1), f (π.pos i) := by
  rw [← Equiv.sum_comp π.word f, Fin.sum_univ_succ]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    ← Fin.sum_univ_eq_sum_range (fun i => f (π.pos (1 + i))) (r + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [word_succ]
  exact congrArg (fun i => f (π.pos i)) (add_comm _ _)

/-- `∑_{i=2}^{N-1} F(i) = ∑_{j < r} F(j + 2)`. -/
theorem sum_Icc_eq_fin (F : ℕ → ℝ) :
    ∑ i in Finset.Icc 2 (r + 1), F i = ∑ j : Fin r, F ((j : ℕ) + 2) := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range,
    Fin.sum_univ_eq_sum_range (fun j => F (j + 2)) r]
  have : (r + 1).succ - 2 = r := by omega
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

/-! ## The marked positions -/

section Marked

variable {M : Finset ℕ}

theorem lastMarked_mem (M : Finset ℕ) : lastMarked M ∈ insert 1 M := Finset.max'_mem _ _

theorem le_lastMarked {i : ℕ} (hi : i ∈ M) : i ≤ lastMarked M :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hi)

theorem markedParent_mem (M : Finset ℕ) (i : ℕ) : markedParent M i ∈ insert 1 M := by
  have h := Finset.max'_mem (insert 1 (M.filter fun j => j < i)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_filter _ h)

theorem markedParent_lt (M : Finset ℕ) {i : ℕ} (hi : 2 ≤ i) : markedParent M i < i := by
  have h := Finset.max'_mem (insert 1 (M.filter fun j => j < i)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · change markedParent M i = 1 at h
    rw [h]
    exact lt_of_lt_of_le (by norm_num) hi
  · exact (Finset.mem_filter.mp h).2

theorem le_markedParent {i j : ℕ} (hj : j ∈ M) (hji : j < i) : j ≤ markedParent M i :=
  Finset.le_max' (insert 1 (M.filter fun x => x < i)) j
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hj, hji⟩))

theorem one_le_markedParent (M : Finset ℕ) (i : ℕ) : 1 ≤ markedParent M i :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem one_le_lastMarked (M : Finset ℕ) : 1 ≤ lastMarked M :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem bounds_of_mem_insert (hM : M ⊆ Finset.Icc 2 (r + 1)) {x : ℕ} (hx : x ∈ insert 1 M) :
    1 ≤ x ∧ x ≤ r + 1 := by
  rcases Finset.mem_insert.mp hx with h | h
  · subst h
    exact ⟨le_refl 1, Nat.succ_le_succ (Nat.zero_le r)⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hM h)
    exact ⟨by omega, h2⟩

theorem lastMarked_empty : lastMarked ∅ = 1 := by
  unfold lastMarked
  simp

theorem markedParent_empty (i : ℕ) : markedParent ∅ i = 1 := by
  unfold markedParent
  simp

/-- For `M ≠ ∅`, `q = max M`. -/
theorem lastMarked_eq_max' (hM : M ⊆ Finset.Icc 2 (r + 1)) (hne : M.Nonempty) :
    lastMarked M = M.max' hne := by
  apply le_antisymm
  · rcases Finset.mem_insert.mp (lastMarked_mem M) with h | h
    · rw [h]
      obtain ⟨h2, -⟩ := Finset.mem_Icc.mp (hM (Finset.max'_mem M hne))
      omega
    · exact Finset.le_max' _ _ h
  · exact le_lastMarked (Finset.max'_mem M hne)

end Marked

/-! ## The zonotope points -/

section Zonotope

variable {M : Finset ℕ}

/-- The point `e_{π_q} + ∑_{i=2}^{N-1} t_i (e_{π_{r(i)}} - e_{π_i})`. -/
noncomputable def zvec (M : Finset ℕ) (t : ℕ → ℝ) : Fin (r + 1 + 1) → ℝ :=
  Pi.single (π.pos (lastMarked M)) 1 +
    ∑ i in Finset.Icc 2 (r + 1),
      t i • (Pi.single (π.pos (markedParent M i)) 1 - Pi.single (π.pos i) 1)

theorem zvec_v (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) : zvec π M t v = 0 := by
  have hq := bounds_of_mem_insert hM (lastMarked_mem M)
  have := hq.1
  have := hq.2
  unfold zvec
  rw [Pi.add_apply, Finset.sum_apply, single_pos_v π hq.1 hq.2, zero_add]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' := Finset.mem_Icc.mp hl
  have := hl'.1
  have := hl'.2
  have hp := bounds_of_mem_insert hM (markedParent_mem M l)
  have := hp.1
  have := hp.2
  rw [Pi.smul_apply, Pi.sub_apply, single_pos_v π hp.1 hp.2, single_pos_v π (by omega) hl'.2,
    sub_zero, smul_zero]

theorem zvec_pos (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r + 1) :
    zvec π M t (π.pos j) = (if lastMarked M = j then 1 else 0) +
      ∑ l in Finset.Icc 2 (r + 1), t l * ((if markedParent M l = j then 1 else 0) -
        (if l = j then 1 else 0)) := by
  have hq := bounds_of_mem_insert hM (lastMarked_mem M)
  have := hq.1
  have := hq.2
  unfold zvec
  rw [Pi.add_apply, Finset.sum_apply, single_pos_apply π hq.1 hq.2 hj1 hj2]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_Icc.mp hl
  have := hl'.1
  have := hl'.2
  have hp := bounds_of_mem_insert hM (markedParent_mem M l)
  have := hp.1
  have := hp.2
  rw [Pi.smul_apply, Pi.sub_apply, single_pos_apply π hp.1 hp.2 hj1 hj2,
    single_pos_apply π (by omega) hl'.2 hj1 hj2, smul_eq_mul]

theorem zvec_sum_pos (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) {J : Finset ℕ} (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ r + 1) :
    ∑ j in J, zvec π M t (π.pos j) = (if lastMarked M ∈ J then 1 else 0) +
      ∑ l in Finset.Icc 2 (r + 1), t l * ((if markedParent M l ∈ J then 1 else 0) -
        (if l ∈ J then 1 else 0)) := by
  rw [Finset.sum_congr rfl fun j hj => zvec_pos π hM t (hJ j hj).1 (hJ j hj).2,
    Finset.sum_add_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq]

theorem prefixSum_zvec (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) {i : ℕ} (hi : i ∈ M) : prefixSum π (zvec π M t) i = t i := by
  have hi' := Finset.mem_Icc.mp (hM hi)
  have := hi'.1
  have := hi'.2
  unfold prefixSum
  rw [zvec_sum_pos π hM t (fun j hj => by
    have := Finset.mem_Ico.mp hj
    obtain ⟨_, _⟩ := this
    exact ⟨by omega, by omega⟩)]
  have hq : lastMarked M ∉ Finset.Ico 1 i := by
    have := le_lastMarked hi
    rw [Finset.mem_Ico]
    omega
  rw [if_neg hq, zero_add, Finset.sum_eq_single i]
  · have h1 : markedParent M i ∈ Finset.Ico 1 i :=
      Finset.mem_Ico.mpr ⟨one_le_markedParent M i, markedParent_lt M hi'.1⟩
    have h2 : i ∉ Finset.Ico 1 i := by
      rw [Finset.mem_Ico]
      omega
    rw [if_pos h1, if_neg h2]
    ring
  · intro l hl hli
    have hl' := Finset.mem_Icc.mp hl
    have := hl'.1
    have := hl'.2
    rcases Nat.lt_or_gt_of_ne hli with h | h
    · have h1 : markedParent M l ∈ Finset.Ico 1 i := by
        have := markedParent_lt M hl'.1
        exact Finset.mem_Ico.mpr ⟨one_le_markedParent M l, by omega⟩
      have h2 : l ∈ Finset.Ico 1 i := Finset.mem_Ico.mpr ⟨by omega, h⟩
      rw [if_pos h1, if_pos h2]
      ring
    · have h1 : markedParent M l ∉ Finset.Ico 1 i := by
        have := le_markedParent hi h
        rw [Finset.mem_Ico]
        omega
      have h2 : l ∉ Finset.Ico 1 i := by
        rw [Finset.mem_Ico]
        omega
      rw [if_neg h1, if_neg h2]
      ring
  · intro h
    exact absurd (hM hi) h

theorem zvec_unmarked (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) {i : ℕ} (hi : i ∈ Finset.Icc 2 (r + 1)) (hiM : i ∉ M) :
    zvec π M t (π.pos i) = - t i := by
  have hi' := Finset.mem_Icc.mp hi
  have := hi'.1
  have := hi'.2
  rw [zvec_pos π hM t (by omega) hi'.2]
  have hq : lastMarked M ≠ i := by
    intro h
    rcases Finset.mem_insert.mp (lastMarked_mem M) with h' | h'
    · omega
    · exact hiM (h ▸ h')
  rw [if_neg hq, zero_add, Finset.sum_eq_single i]
  · have hp : markedParent M i ≠ i := (ne_of_lt (markedParent_lt M hi'.1))
    rw [if_neg hp, if_pos rfl]
    ring
  · intro l _ hli
    have hp : markedParent M l ≠ i := by
      intro h
      rcases Finset.mem_insert.mp (markedParent_mem M l) with h' | h'
      · omega
      · exact hiM (h ▸ h')
    rw [if_neg hp, if_neg hli]
    ring
  · intro h
    exact absurd hi h

theorem zvec_total (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) : ∑ k, zvec π M t k = 1 := by
  have hJ : ∀ j ∈ Finset.Ico 1 (r + 1 + 1), 1 ≤ j ∧ j ≤ r + 1 := fun j hj => by
    have := Finset.mem_Ico.mp hj
    obtain ⟨_, _⟩ := this
    exact ⟨by omega, by omega⟩
  have hq := bounds_of_mem_insert hM (lastMarked_mem M)
  have := hq.1
  have := hq.2
  rw [sum_univ_split π, zvec_v π hM, zero_add, zvec_sum_pos π hM t hJ,
    if_pos (Finset.mem_Ico.mpr ⟨hq.1, by omega⟩)]
  rw [Finset.sum_eq_zero, add_zero]
  intro l hl
  have hl' := Finset.mem_Icc.mp hl
  have := hl'.1
  have := hl'.2
  have hp := bounds_of_mem_insert hM (markedParent_mem M l)
  have := hp.1
  have := hp.2
  rw [if_pos (Finset.mem_Ico.mpr ⟨hp.1, by omega⟩), if_pos (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
  ring

theorem zvec_mem_hyperplane (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) : zvec π M t ∈ hyperplane v :=
  ⟨zvec_v π hM t, zvec_total π hM t⟩

theorem zvec_mem (hM : M ⊆ Finset.Icc 2 (r + 1)) (t : ℕ → ℝ) (ht : ∀ i ∈ Finset.Icc 2 (r + 1), 0 ≤ t i ∧ t i ≤ 1) :
    zvec π M t ∈ parallelepiped v π M := by
  refine ⟨zvec_mem_hyperplane π hM t, fun i hi => ?_, fun i hi hiM => ?_⟩
  · rw [prefixSum_zvec π hM t hi]
    exact ht i (hM hi)
  · have hi' : i ∈ Finset.Icc 2 (r + 1) := hi
    rw [zvec_unmarked π hM t hi' hiM]
    have := ht i hi'
    constructor <;> linarith

/-- Two points of `H_{-v}` with the same coordinates `t` coincide (Brunck et al., Claim 21). -/
theorem eq_of_coords {p p' : Fin (r + 1 + 1) → ℝ} (hp : p ∈ hyperplane v)
    (hp' : p' ∈ hyperplane v) (hu : ∀ i ∈ M, prefixSum π p i = prefixSum π p' i)
    (hc : ∀ i ∈ Finset.Icc 2 (r + 1), i ∉ M → p (π.pos i) = p' (π.pos i)) : p = p' := by
  set D : ℕ → ℝ := fun j => p (π.pos j) - p' (π.pos j) with hD
  set U : ℕ → ℝ := fun i => ∑ j in Finset.Ico 1 i, D j with hU
  have hUtop : U (r + 1 + 1) = 0 := by
    have h1 := hp.2
    have h2 := hp'.2
    rw [sum_univ_split π, hp.1, zero_add] at h1
    rw [sum_univ_split π, hp'.1, zero_add] at h2
    simp only [hU, hD, Finset.sum_sub_distrib, h1, h2, sub_self]
  have hstep : ∀ m, m ≤ r → U (r + 1 + 1 - m) = 0 := by
    intro m
    induction m with
    | zero => intro _; simpa using hUtop
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have he : r + 1 + 1 - m = (r + 1 - m) + 1 := by omega
      have he' : r + 1 + 1 - (m + 1) = r + 1 - m := by omega
      rw [he] at hprev
      rw [Nat.succ_eq_add_one, he']
      have hsplit : U (r + 1 - m + 1) = U (r + 1 - m) + D (r + 1 - m) :=
        Finset.sum_Ico_succ_top (by omega) D
      by_cases hiM : r + 1 - m ∈ M
      · simp only [hU, hD, Finset.sum_sub_distrib]
        rw [show ∑ j in Finset.Ico 1 (r + 1 - m), p (π.pos j) = prefixSum π p (r + 1 - m) from rfl,
          show ∑ j in Finset.Ico 1 (r + 1 - m), p' (π.pos j) = prefixSum π p' (r + 1 - m) from rfl,
          hu _ hiM, sub_self]
      · have hD0 : D (r + 1 - m) = 0 := by
          simp only [hD]
          rw [hc _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hiM, sub_self]
        rw [hD0, add_zero] at hsplit
        rw [← hsplit, hprev]
  have hUall : ∀ i, 1 ≤ i → i ≤ r + 1 + 1 → U i = 0 := by
    intro i h1 h2
    by_cases hi : i = 1
    · subst hi
      simp [hU]
    · have := hstep (r + 1 + 1 - i) (by omega)
      rwa [show r + 1 + 1 - (r + 1 + 1 - i) = i by omega] at this
  have hDall : ∀ j, 1 ≤ j → j ≤ r + 1 → D j = 0 := by
    intro j h1 h2
    have hs : U (j + 1) = U j + D j := Finset.sum_Ico_succ_top h1 D
    rw [hUall (j + 1) (by omega) (by omega), hUall j h1 (by omega)] at hs
    linarith
  funext k
  by_cases hk : k = v
  · rw [hk, hp.1, hp'.1]
  · obtain ⟨j, h1, h2, rfl⟩ := pos_surj π hk
    have := hDall j h1 h2
    simp only [hD] at this
    linarith

end Zonotope

/-! ## (a) The parallelepiped is a zonotope -/

/-- **Brunck et al., Claim 21, explicitly.** `B_{v,π,M} = e_{π_q} + ∑_{i=2}^{N-1}
[0, e_{π_{r(i)}} - e_{π_i}]` with `q = max ({1} ∪ M)` and `r(i) = max ({1} ∪ {j ∈ M : j < i})`. -/
theorem parallelepiped_eq_zonotope {M : Finset ℕ} (hM : M ⊆ Finset.Icc 2 (r + 1)) :
    parallelepiped v π M = zonotope (Pi.single (π.pos (lastMarked M)) 1) (Finset.Icc 2 (r + 1))
      (fun i => Pi.single (π.pos (markedParent M i)) 1 - Pi.single (π.pos i) 1) := by
  classical
  ext p
  constructor
  · rintro ⟨hH, hUb, hN⟩
    let t : ℕ → ℝ := fun i => if i ∈ M then prefixSum π p i else - p (π.pos i)
    refine ⟨t, fun i hi => ?_, ?_⟩
    · by_cases hiM : i ∈ M
      · simp only [t, if_pos hiM]
        exact hUb i hiM
      · simp only [t, if_neg hiM]
        have := hN i hi hiM
        constructor <;> linarith
    · show p = zvec π M t
      refine eq_of_coords π (M := M) hH (zvec_mem_hyperplane π hM t) (fun i hi => ?_) (fun i hi hiM => ?_)
      · rw [prefixSum_zvec π hM t hi]
        simp only [t, if_pos hi]
      · rw [zvec_unmarked π hM t hi hiM]
        simp only [t, if_neg hiM, neg_neg]
  · rintro ⟨t, ht, rfl⟩
    exact zvec_mem π hM t ht

end MaxCaterpillar.BHRSY
