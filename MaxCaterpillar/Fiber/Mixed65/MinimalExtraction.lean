import MaxCaterpillar.Fiber.Mixed65.Extraction

/-! # Extracting three unchanged gates from a five-gate signed-carrier lift

The two diagonal tails must each leave at least three zero-slope gates. Under
this explicit hypothesis, an arbitrary exact five-gate lift supplies a residual
representation by three original gates, without dividing or normalizing any
weight. The lower bound giving the zero-slope cardinalities is a separate
obligation. This module does not assert disconnectedness.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

private lemma zero_card_of_nonzero_card (a : Fin 5 → ℝ)
    (h : (Finset.univ.filter fun i => a i ≠ 0).card = 2) :
    (Finset.univ.filter fun i => a i = 0).card = 3 := by
  classical
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin 5))) (fun i => a i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hc

  change (Finset.univ.filter fun i => a i = 0).card +
    (Finset.univ.filter fun i => a i ≠ 0).card = 5 at hc
  rw [h] at hc
  exact Nat.add_right_cancel hc

private lemma singleton_slope (d a : Fin 5 → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hc : (Finset.univ.filter fun i => a i ≠ 0).card = 1)
    (h : (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) = s) :
    ∃ p, 0 < a p ∧ d p * a p = s ∧ ∀ i, i ≠ p → a i = 0 := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have ho : ∀ i, i ≠ p → a i = 0 := by
    intro i hi
    by_contra hn
    have hm : i ∈ Finset.univ.filter (fun i => a i ≠ 0) := by simp [hn]
    rw [hp] at hm
    exact hi (Finset.mem_singleton.mp hm)
  have he : (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) =
      if 0 < a p then d p * a p else 0 := by
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single p]
    · intro i _ hip
      simp [ho i hip]
    · simp
  rw [he] at h
  by_cases hpa : 0 < a p
  · exact ⟨p, hpa, by simpa [hpa] using h, ho⟩
  · simp [hpa] at h
    exact (hs h.symm).elim

private lemma tail_singleton_identity {α : Type*}
    (d a : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (p : Fin 5) (hp : 0 < a p) (ho : ∀ i, i ≠ p → a i = 0)
    (h : ∀ x, H x = (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
      ∑ i in Finset.univ.filter (fun i => a i = 0), d i * relu (C i x)) :
    ∀ x, H x = d p * C p x + (∑ i, d i * relu (C i x)) - d p * relu (C p x) := by
  classical
  have hpos : Finset.univ.filter (fun i => 0 < a i) = {p} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hi : i = p
    · simp [hi, hp]
    · simp [hi, ho i hi]
  have hzero : Finset.univ.filter (fun i => a i = 0) = Finset.univ.erase p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hz
      refine ⟨?_, trivial⟩
      intro hi
      subst i
      exact hp.ne' hz
    · rintro ⟨hi, _⟩
      exact ho i hi
  intro x
  have hh := h x
  rw [hpos, hzero, Finset.sum_singleton] at hh
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun i => d i * relu (C i x)) (Finset.mem_univ p)
  dsimp only at he
  linarith only [hh, he]

/-- The extracted residual gates are original neurons with their original output
and invariant incoming coefficients. Only the feature-linear remainder changes. -/
theorem five_gate_residual_extraction {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) = z + H x)
    (ha : 3 ≤ (Finset.univ.filter fun i => a i = 0).card)
    (hb : 3 ≤ (Finset.univ.filter fun i => b i = 0).card) :
    ∃ S : Finset (Fin 5), S.card = 3 ∧ ∃ l : Fin 5 → ℝ,
      ∀ x, H x = (∑ i, l i * C i x) + ∑ i in S, d i * relu (C i x) := by
  classical
  obtain ⟨hsa, hsb, hrem⟩ := finite_signed_carrier_extraction d a b C H h
  have hca : (Finset.univ.filter fun i => a i ≠ 0).card ≤ 2 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 5))) (fun i => a i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    change (Finset.univ.filter fun i => a i = 0).card +
      (Finset.univ.filter fun i => a i ≠ 0).card = 5 at hc
    have hh : (Finset.univ.filter fun i => a i ≠ 0).card +
        (Finset.univ.filter fun i => a i = 0).card = 5 := by
      exact (Nat.add_comm _ _).trans hc
    exact Nat.le_of_add_le_add_right (show (Finset.univ.filter fun i => a i ≠ 0).card + 3 ≤ 2 + 3 by
      calc
        _ ≤ (Finset.univ.filter fun i => a i ≠ 0).card + (Finset.univ.filter fun i => a i = 0).card := Nat.add_le_add_left ha _
        _ = _ := hh)
  have hcb : (Finset.univ.filter fun i => b i ≠ 0).card ≤ 2 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 5))) (fun i => b i = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    change (Finset.univ.filter fun i => b i = 0).card +
      (Finset.univ.filter fun i => b i ≠ 0).card = 5 at hc
    have hh : (Finset.univ.filter fun i => b i ≠ 0).card +
        (Finset.univ.filter fun i => b i = 0).card = 5 := by
      exact (Nat.add_comm _ _).trans hc
    exact Nat.le_of_add_le_add_right (show (Finset.univ.filter fun i => b i ≠ 0).card + 3 ≤ 2 + 3 by
      calc
        _ ≤ (Finset.univ.filter fun i => b i ≠ 0).card + (Finset.univ.filter fun i => b i = 0).card := Nat.add_le_add_left hb _
        _ = _ := hh)
  have hca0 : 0 < (Finset.univ.filter fun i => a i ≠ 0).card := by
    obtain ⟨i, hi, _⟩ := exists_positive_passing_of_slope d a (by rw [hsa]; norm_num)
    exact Finset.card_pos.mpr ⟨i, by simp [hi.ne']⟩
  have hcb0 : 0 < (Finset.univ.filter fun i => b i ≠ 0).card := by
    obtain ⟨i, hi, _⟩ := exists_negative_passing_of_slope d b (by rw [hsb]; norm_num)
    exact Finset.card_pos.mpr ⟨i, by simp [hi.ne']⟩
  by_cases hca2 : (Finset.univ.filter fun i => a i ≠ 0).card = 2
  · refine ⟨Finset.univ.filter (fun i => a i = 0), zero_card_of_nonzero_card a hca2,
      (fun i => if 0 < a i then d i else 0), ?_⟩
    intro x
    convert (hrem x).1 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hh <;> simp [hh]
  by_cases hcb2 : (Finset.univ.filter fun i => b i ≠ 0).card = 2
  · refine ⟨Finset.univ.filter (fun i => b i = 0), zero_card_of_nonzero_card b hcb2,
      (fun i => if 0 < b i then d i else 0), ?_⟩
    intro x
    convert (hrem x).2 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hh <;> simp [hh]
  have hca1 : (Finset.univ.filter fun i => a i ≠ 0).card = 1 := by omega
  have hcb1 : (Finset.univ.filter fun i => b i ≠ 0).card = 1 := by omega
  obtain ⟨p, hpa, hpd, hpo⟩ := singleton_slope d a 1 (by norm_num) hca1 hsa
  obtain ⟨q, hqb, hqd, hqo⟩ := singleton_slope d b (-1) (by norm_num) hcb1 hsb
  have hdp : 0 < d p := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hpa.le
    linarith only [hh, hpd]
  have hdq : d q < 0 := by
    by_contra hn
    have hh := mul_nonneg (le_of_not_gt hn) hqb.le
    linarith only [hh, hqd]
  have hpq : p ≠ q := by intro he; rw [he] at hdp; linarith
  have hqa := tail_singleton_identity d a C H p hpa hpo (fun x => (hrem x).1)
  have hqb' := tail_singleton_identity d b C H q hqb hqo (fun x => (hrem x).2)
  have hCp : ∀ x, relu (C p x) = C p x := by
    intro x
    have hp := relu_sub_relu_neg (C p x)
    have hq := relu_sub_relu_neg (C q x)
    have hbalance : d p * relu (-C p x) = d q * relu (-C q x) := by
      linear_combination (hqa x) - (hqb' x) - d p * hp + d q * hq
    have hl := mul_nonneg hdp.le (relu_nonneg (-C p x))
    have hr := mul_nonpos_of_nonpos_of_nonneg hdq.le (relu_nonneg (-C q x))
    have hz : d p * relu (-C p x) = 0 := by linarith only [hbalance, hl, hr]
    have hz' := (mul_eq_zero.mp hz).resolve_left hdp.ne'
    linarith only [hp, hz']
  have hCq : ∀ x, relu (C q x) = C q x := by
    intro x
    have hh : d q * (C q x - relu (C q x)) = 0 := by
      have ha' := hqa x
      rw [hCp x] at ha'
      nlinarith only [ha', hqb' x]
    have hh' := (mul_eq_zero.mp hh).resolve_left hdq.ne
    linarith only [hh']
  refine ⟨(Finset.univ.erase p).erase q, ?_,
    (fun i => (if i = p then d p else 0) + (if i = q then d q else 0)), ?_⟩
  · rw [Finset.card_erase_of_mem (by simp [hpq.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  · intro x
    have hpSum := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (fun i => d i * relu (C i x)) (Finset.mem_univ p)
    have hqSum := Finset.sum_erase_add ((Finset.univ : Finset (Fin 5)).erase p)
      (fun i => d i * relu (C i x)) (by simp [hpq.symm] : q ∈ Finset.univ.erase p)
    have hlin : (∑ i : Fin 5,
        ((if i = p then d p else 0) + (if i = q then d q else 0)) * C i x) =
        d p * C p x + d q * C q x := by
      simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      simp
    rw [hlin]
    dsimp only at hpSum hqSum
    rw [hCp x] at hpSum
    rw [hCq x] at hqSum
    have hh := hqa x
    rw [hCp x] at hh
    linarith only [hh, hpSum, hqSum]

/-- A residual lower bound supplies both zero-slope cardinalities needed by the
unchanged-gate extraction. The bound is stated against arbitrary feature-linear
remainders, not merely against a preselected signed pair of second-layer gates. -/
theorem five_gate_residual_extraction_of_floor {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) = z + H x)
    (hfloor : ∀ (S : Finset (Fin 5)) (l : Fin 5 → ℝ),
      (∀ x, H x = (∑ i, l i * C i x) + ∑ i in S, d i * relu (C i x)) →
      3 ≤ S.card) :
    ∃ S : Finset (Fin 5), S.card = 3 ∧ ∃ l : Fin 5 → ℝ,
      ∀ x, H x = (∑ i, l i * C i x) + ∑ i in S, d i * relu (C i x) := by
  classical
  obtain ⟨_, _, hrem⟩ := finite_signed_carrier_extraction d a b C H h
  apply five_gate_residual_extraction d a b C H h
  · apply hfloor (Finset.univ.filter fun i => a i = 0)
      (fun i => if 0 < a i then d i else 0)
    intro x
    convert (hrem x).1 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hh <;> simp [hh]
  · apply hfloor (Finset.univ.filter fun i => b i = 0)
      (fun i => if 0 < b i then d i else 0)
    intro x
    convert (hrem x).2 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hh <;> simp [hh]

end MaxCaterpillar.Fiber.Mixed65
