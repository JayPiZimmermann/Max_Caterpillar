import Mathlib

/-!
# A support-moment restriction lemma

The coordinates are paired. Choose one coordinate of each pair independently.
The number of choices containing a support T is at most 2^(n - |T|), in the
multiplication form used below. Averaging fourth moments loses no logarithms.

This file proves a combinatorial theorem, not a network-width theorem.
-/
set_option autoImplicit false

namespace MaxCaterpillar.WeightedRestriction
open BigOperators

/-- The exact constant is attained at support size six. -/
theorem fourth_moment_decay (s : ℕ) : 4 * s ^ 4 ≤ 81 * 2 ^ s := by
  have step : ∀ s : ℕ, 6 ≤ s → (s + 1) ^ 4 ≤ 2 * s ^ 4 := by
    intro s hs
    have h : 6 * (s + 1) ≤ 7 * s := by linarith
    have hp := Nat.pow_le_pow_left h 4
    norm_num [mul_pow] at hp
    linarith only [hp, Nat.zero_le (s ^ 4)]
  have core : ∀ s : ℕ, 6 ≤ s → 4 * s ^ 4 ≤ 81 * 2 ^ s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => norm_num
    | succ s hs ih =>
      have hstep := step s hs
      rw [Nat.pow_succ 2 s]
      linarith only [ih, hstep]
  by_cases hs : s < 6
  · interval_cases s <;> norm_num
  · exact core s (Nat.le_of_not_gt hs)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinates of a support in one fixed pair. -/
def fiber (T : Finset (ι × Bool)) (i : ι) : Finset Bool :=
  Finset.univ.filter fun b => (i, b) ∈ T

/-- A bit may be selected precisely when it contains this entire fiber. -/
def allowed (t : Finset Bool) : Finset Bool :=
  Finset.univ.filter fun b => t ⊆ {b}

lemma allowed_card_bound : ∀ t : Finset Bool,
    (allowed t).card * 2 ^ t.card ≤ 2 := by decide

/-- The finite set of selectors containing T. -/
def containing (T : Finset (ι × Bool)) : Finset (ι → Bool) :=
  Fintype.piFinset fun i => allowed (fiber T i)

lemma mem_containing (T : Finset (ι × Bool)) (f : ι → Bool) :
    f ∈ containing T ↔ ∀ p ∈ T, f p.1 = p.2 := by
  classical
  simp only [containing, Fintype.mem_piFinset, allowed, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.subset_iff, Finset.mem_singleton]
  constructor
  · intro h p hp
    exact (h p.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)).symm
  · intro h i b hb
    have hb' : (i, b) ∈ T := (Finset.mem_filter.mp hb).2
    exact (h (i,b) hb').symm

lemma sum_fiber_card (T : Finset (ι × Bool)) :
    ∑ i, (fiber T i).card = T.card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := T)
    (t := Finset.univ) (f := Prod.fst) (fun p _ => Finset.mem_univ p.1)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_congr (fun b _ => (i,b))
  · intro b hb
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).2, rfl⟩
  · intro a b _ _ hab
    exact (Prod.mk.inj hab).2
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hi⟩
    refine ⟨p.2, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have he : (i, p.2) = p := Prod.ext hi.symm rfl
        rw [he]
        exact hp⟩
    · exact Prod.ext hi.symm rfl

/-- An exact integer counting bound, including incompatible supports. -/
theorem containing_card_bound (T : Finset (ι × Bool)) :
    (containing T).card * 2 ^ T.card ≤ 2 ^ Fintype.card ι := by
  classical
  rw [containing, Fintype.card_piFinset, ← sum_fiber_card T,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _i : ι, 2 := Finset.prod_le_prod' fun i _ => allowed_card_bound (fiber T i)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- Fourth-moment cost of one non-braid support under a selector. -/
def fourthCost (T : Finset (ι × Bool)) (f : ι → Bool) : ℕ :=
  if 3 ≤ T.card ∧ f ∈ containing T then T.card ^ 4 else 0

lemma sum_fourthCost (T : Finset (ι × Bool)) :
    ∑ f : ι → Bool, fourthCost T f =
      if 3 ≤ T.card then T.card ^ 4 * (containing T).card else 0 := by
  classical
  by_cases h : 3 ≤ T.card
  · simp [fourthCost, h, Finset.sum_ite_mem, mul_comm]
  · simp [fourthCost, h]

lemma sum_fourthCost_bound (T : Finset (ι × Bool)) :
    4 * (∑ f : ι → Bool, fourthCost T f) ≤ 81 * 2 ^ Fintype.card ι := by
  classical
  rw [sum_fourthCost]
  split_ifs with h
  · calc
      4 * (T.card ^ 4 * (containing T).card) =
          (4 * T.card ^ 4) * (containing T).card := by ring
      _ ≤ (81 * 2 ^ T.card) * (containing T).card :=
          Nat.mul_le_mul_right _ (fourth_moment_decay T.card)
      _ = 81 * ((containing T).card * 2 ^ T.card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 81 (containing_card_bound T)
  · simp

variable {κ : Type*} [Fintype κ]

/-- Averaging all selectors: one has small total support moment. -/
theorem exists_selector_fourth_moment (T : κ → Finset (ι × Bool)) :
    ∃ f : ι → Bool, 4 * (∑ j, fourthCost (T j) f) ≤ 81 * Fintype.card κ := by
  classical
  have total : (∑ f : ι → Bool, 4 * (∑ j, fourthCost (T j) f)) ≤
      ∑ _f : ι → Bool, 81 * Fintype.card κ := by
    calc
      _ = ∑ j : κ, 4 * (∑ f : ι → Bool, fourthCost (T j) f) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
      _ ≤ ∑ _j : κ, 81 * 2 ^ Fintype.card ι :=
          Finset.sum_le_sum fun j _ => sum_fourthCost_bound (T j)
      _ = _ := by
          have hc : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by
            simp only [Fintype.card_pi, Fintype.card_bool,
              Finset.prod_const, Finset.card_univ]
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hc, Nat.cast_id]
          ring
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty total
  exact ⟨f, hf⟩

/-- The selected coordinates: precisely one from each pair. -/
def selected (f : ι → Bool) : Finset (ι × Bool) :=
  Finset.univ.image fun i => (i, f i)

lemma selected_card (f : ι → Bool) : (selected f).card = Fintype.card ι := by
  classical
  rw [selected, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro a b hab
    exact congrArg Prod.fst hab

lemma subset_selected (T : Finset (ι × Bool)) (f : ι → Bool) :
    T ⊆ selected f ↔ f ∈ containing T := by
  classical
  rw [mem_containing]
  constructor
  · intro h p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (h hp)
    have he : i = p.1 := congrArg Prod.fst hi
    have hb : f i = p.2 := congrArg Prod.snd hi
    simpa [he] using hb
  · intro h p hp
    apply Finset.mem_image.mpr
    exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl (h p hp)⟩

/-- The concrete restriction theorem. No distributional or network assumptions.
Every family of supports has a half-size restriction of bounded fourth moment. -/
theorem paired_fourth_moment_restriction (T : κ → Finset (ι × Bool)) :
    ∃ U : Finset (ι × Bool), U.card = Fintype.card ι ∧
      4 * (∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then (T j).card ^ 4 else 0) ≤
        81 * Fintype.card κ := by
  classical
  obtain ⟨f, hf⟩ := exists_selector_fourth_moment T
  refine ⟨selected f, selected_card f, ?_⟩
  simpa only [fourthCost, subset_selected] using hf

/-- Total fourth moment of surviving supports of size at least three. -/
def moment (T : κ → Finset (ι × Bool)) (U : Finset (ι × Bool)) : ℕ :=
  ∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then (T j).card ^ 4 else 0

/-- Number of surviving supports of size at least three. -/
noncomputable def nonBraidCount (T : κ → Finset (ι × Bool))
    (U : Finset (ι × Bool)) : ℕ :=
  (Finset.univ.filter fun j => 3 ≤ (T j).card ∧ T j ⊆ U).card

lemma moment_controls_count (T : κ → Finset (ι × Bool)) (U : Finset (ι × Bool)) :
    81 * nonBraidCount T U ≤ moment T U := by
  classical
  have h : (∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then 81 else 0) ≤ moment T U := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hp : 3 ≤ (T j).card ∧ T j ⊆ U
    · simp only [if_pos hp]
      have hpow := Nat.pow_le_pow_left hp.1 4
      norm_num at hpow
      exact hpow
    · simp only [if_neg hp, le_refl]
  simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_id, nonBraidCount, mul_comm] using h

/-- One restriction simultaneously controls interference and the non-braid budget. -/
theorem paired_restriction (T : κ → Finset (ι × Bool)) :
    ∃ U : Finset (ι × Bool), U.card = Fintype.card ι ∧
      4 * moment T U ≤ 81 * Fintype.card κ ∧
      4 * nonBraidCount T U ≤ Fintype.card κ := by
  classical
  obtain ⟨U, hcard, hmoment⟩ := paired_fourth_moment_restriction T
  refine ⟨U, hcard, hmoment, ?_⟩
  have hcount := moment_controls_count T U
  change 4 * moment T U ≤ 81 * Fintype.card κ at hmoment
  linarith only [hmoment, hcount]

/-- All even-sized coordinate sets admit the same restriction, after relabelling. -/
theorem half_fourth_moment_restriction {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (hα : Fintype.card α = 2 * n) (T : κ → Finset α) :
    ∃ U : Finset α, U.card = n ∧
      4 * (∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then (T j).card ^ 4 else 0) ≤
        81 * Fintype.card κ := by
  classical
  let e : (Fin n × Bool) ≃ α := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hα]
    exact Nat.mul_comm n 2)
  let Q : κ → Finset (Fin n × Bool) := fun j => (T j).map e.symm.toEmbedding
  obtain ⟨U, hcard, hmoment⟩ := paired_fourth_moment_restriction Q
  refine ⟨U.map e.toEmbedding, ?_, ?_⟩
  · simpa only [Finset.card_map, Fintype.card_fin] using hcard
  · have hsub : ∀ j, Q j ⊆ U ↔ T j ⊆ U.map e.toEmbedding := by
      intro j
      rw [← Finset.map_subset_map (f := e.toEmbedding)]
      simp [Q, Finset.map_map]
    simpa only [Q, Finset.card_map, hsub] using hmoment

example : 4 * (6 : ℕ) ^ 4 = 81 * 2 ^ 6 := by norm_num

#check @paired_restriction
#check @half_fourth_moment_restriction
#print axioms fourth_moment_decay
#print axioms containing_card_bound
#print axioms paired_fourth_moment_restriction
#print axioms paired_restriction
#print axioms half_fourth_moment_restriction
end MaxCaterpillar.WeightedRestriction
