import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # A covering count for supports (Lemma K)

Let `S j ⊆ {0, …, N-1}`, `j ∈ J`, be sets such that for every 4-set `I` and every `a ∈ I` some
`S j` with `|S j| ≥ 2` satisfies `a ∈ S j ⊆ I`. Then `3N² ≤ 6|J| + 11N`, i.e.
`|J| ≥ C(N,2) - ⌊4N/3⌋` (`cover_count`).

Proof: for a vertex `a` let `D a` be the vertices `b` with `S j = {a, b}` for some `j`, and `U a`
the other vertices `≠ a`. Each 3-set `Y ⊆ U a` needs an index `j` with `|S j| ∈ {3, 4}`,
`a ∈ S j` and `S j \ {a} ⊆ Y`; double counting gives `C(m,3) ≤ (m-2) p + t`, hence
`6|D a| + 4p + 3t ≥ 6N - 22`. Summing over `a` counts each index at most twelve times.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators Finset

lemma six_mul_choose_three (m : ℕ) : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  have e : m.descFactorial 3 = (m - 2) * ((m - 1) * (m * 1)) := by
    simp [Nat.descFactorial]
  rw [e] at h
  have : Nat.factorial 3 = 6 := rfl
  rw [this] at h
  rw [← h]; ring

/-- The arithmetic step: `C(m,3) ≤ (m-2) p + t` implies `6m ≤ 4p + 3t + 16`. -/
lemma cover_arith (m p t : ℕ) (h : m.choose 3 ≤ (m - 2) * p + t) : 6 * m ≤ 4 * p + 3 * t + 16 := by
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m
    · omega
    · omega
    · omega
    · have e : Nat.choose 3 3 = 1 := rfl
      have e' : (3 - 2) * p = p := by norm_num
      rw [e, e'] at h; linarith
    · have e : Nat.choose 4 3 = 4 := rfl
      have e' : (4 - 2) * p = 2 * p := by norm_num
      rw [e, e'] at h; linarith
    · have e : Nat.choose 5 3 = 10 := rfl
      have e' : (5 - 2) * p = 3 * p := by norm_num
      rw [e, e'] at h
      rcases Nat.lt_or_ge p 4 with hp | hp
      · interval_cases p <;> linarith
      · linarith
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 6 := ⟨m - 6, by omega⟩
    have h6 := six_mul_choose_three (n + 6)
    have e1 : n + 6 - 1 = n + 5 := by omega
    have e2 : n + 6 - 2 = n + 4 := by omega
    rw [e1, e2] at h6
    rw [e2] at h
    have key : (n + 6) * (n + 5) * (n + 4) ≤ 6 * ((n + 4) * p + t) := by
      rw [← h6]; exact Nat.mul_le_mul_left 6 h
    have h2 : 12 * t ≤ 9 * (n + 4) * t := Nat.mul_le_mul_right _ (by omega)
    have h3 : (n + 4) * (2 * ((n + 6) * (n + 5))) ≤ (n + 4) * (3 * (4 * p + 3 * t)) := by
      have k2 : 2 * ((n + 6) * (n + 5) * (n + 4)) ≤ 12 * ((n + 4) * p) + 12 * t := by
        have := Nat.mul_le_mul_left 2 key
        calc 2 * ((n + 6) * (n + 5) * (n + 4)) ≤ 2 * (6 * ((n + 4) * p + t)) := this
          _ = 12 * ((n + 4) * p) + 12 * t := by ring
      calc (n + 4) * (2 * ((n + 6) * (n + 5))) = 2 * ((n + 6) * (n + 5) * (n + 4)) := by ring
        _ ≤ 12 * ((n + 4) * p) + 12 * t := k2
        _ ≤ 12 * ((n + 4) * p) + 9 * (n + 4) * t := Nat.add_le_add_left h2 _
        _ = (n + 4) * (3 * (4 * p + 3 * t)) := by ring
    have h4 : 2 * ((n + 6) * (n + 5)) ≤ 3 * (4 * p + 3 * t) :=
      Nat.le_of_mul_le_mul_left h3 (by omega)
    have h5 : 18 * n + 60 ≤ 2 * ((n + 6) * (n + 5)) := by
      have : 2 * ((n + 6) * (n + 5)) = 2 * (n * n) + 22 * n + 60 := by ring
      rw [this]; linarith [Nat.zero_le (n * n)]
    have h6 : 18 * n + 60 ≤ 3 * (4 * p + 3 * t) := h5.trans h4
    linarith

variable {N : ℕ}

lemma card_filter_mem_card {ι : Type*} (J : Finset ι) (S : ι → Finset (Fin N)) (r : ℕ) :
    ∑ a : Fin N, (J.filter fun j => a ∈ S j ∧ (S j).card = r).card =
      r * (J.filter fun j => (S j).card = r).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ j ∈ J, (∑ a : Fin N, if a ∈ S j ∧ (S j).card = r then 1 else 0) =
      if (S j).card = r then r else 0 := by
    intro j _
    by_cases hr : (S j).card = r
    · rw [if_pos hr]
      simp only [hr, and_true]
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, hr]
    · simp [hr]
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm,
    Finset.card_filter]

lemma fiber_two {U T : Finset (Fin N)} (hTU : T ⊆ U) (hT : T.card = 2) :
    ((U.powersetCard 3).filter fun Y => T ⊆ Y).card ≤ U.card - 2 := by
  have hsub : ((U.powersetCard 3).filter fun Y => T ⊆ Y) ⊆
      (U \ T).image fun y => insert y T := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hY
    obtain ⟨⟨hYU, hY3⟩, hTY⟩ := hY
    have hc : (Y \ T).card = 1 := by rw [Finset.card_sdiff hTY, hY3, hT]
    obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hc
    have hyY : y ∈ Y \ T := by rw [hy]; exact Finset.mem_singleton_self y
    rw [Finset.mem_sdiff] at hyY
    refine Finset.mem_image.2 ⟨y, Finset.mem_sdiff.2 ⟨hYU hyY.1, hyY.2⟩, ?_⟩
    rw [← Finset.sdiff_union_of_subset hTY, hy, Finset.insert_eq]
  calc _ ≤ ((U \ T).image fun y => insert y T).card := Finset.card_le_of_subset hsub
    _ ≤ (U \ T).card := Finset.card_image_le
    _ = U.card - 2 := by rw [Finset.card_sdiff hTU, hT]

lemma fiber_three {U T : Finset (Fin N)} (hT : T.card = 3) :
    ((U.powersetCard 3).filter fun Y => T ⊆ Y).card ≤ 1 := by
  have hsub : ((U.powersetCard 3).filter fun Y => T ⊆ Y) ⊆ {T} := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hY
    obtain ⟨⟨_, hY3⟩, hTY⟩ := hY
    rw [Finset.mem_singleton]
    exact (Finset.eq_of_subset_of_card_le hTY (by rw [hY3, hT])).symm
  simpa using Finset.card_le_of_subset hsub

/-- Vertices `b` with `S j = {a, b}` for some `j ∈ J`. -/
def coverD {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N)) (a : Fin N) :
    Finset (Fin N) :=
  Finset.univ.filter fun b => b ≠ a ∧ ∃ j ∈ J, S j = {a, b}

/-- The other vertices `b ≠ a`. -/
def coverU {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N)) (a : Fin N) :
    Finset (Fin N) :=
  Finset.univ.filter fun b => b ≠ a ∧ ∀ j ∈ J, S j ≠ {a, b}

/-- Indices `j` with `a ∈ S j`, `|S j| = r` and `S j \ {a} ⊆ U a`. -/
def coverR {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N)) (r : ℕ)
    (a : Fin N) : Finset ι :=
  J.filter fun j => a ∈ S j ∧ (S j).card = r ∧ (S j).erase a ⊆ coverU J S a

/-- Indices `j` with `a ∈ S j` and `|S j| = r`. -/
def coverP {ι : Type*} (J : Finset ι) (S : ι → Finset (Fin N)) (r : ℕ) (a : Fin N) :
    Finset ι :=
  J.filter fun j => a ∈ S j ∧ (S j).card = r

lemma cover_DU {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N)) (a : Fin N) :
    (coverD J S a).card + (coverU J S a).card + 1 = N := by
  have hunion : coverD J S a ∪ coverU J S a = Finset.univ.erase a := by
    ext b
    simp only [coverD, coverU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hc : ∃ j ∈ J, S j = {a, b}
      · exact Or.inl ⟨h, hc⟩
      · push_neg at hc
        exact Or.inr ⟨h, hc⟩
  have hdisj : Disjoint (coverD J S a) (coverU J S a) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [coverD, coverU, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    obtain ⟨_, j, hj, hS⟩ := hb
    exact hb'.2 j hj hS
  have h := Finset.card_disjoint_union hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin] at h
  rw [← h]; exact Nat.sub_add_cancel a.pos

lemma cover_D_le {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N))
    (a : Fin N) : (coverD J S a).card ≤ (coverP J S 2 a).card := by
  have hsub : (coverD J S a).map ⟨fun b => ({b} : Finset (Fin N)), Finset.singleton_injective⟩ ⊆
      (coverP J S 2 a).image fun j => (S j).erase a := by
    intro T hT
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, coverD, Finset.mem_filter,
      Finset.mem_univ, true_and] at hT
    obtain ⟨b, ⟨hba, j, hj, hSj⟩, rfl⟩ := hT
    refine Finset.mem_image.2 ⟨j, ?_, ?_⟩
    · simp only [coverP, Finset.mem_filter, hSj]
      exact ⟨hj, Finset.mem_insert_self _ _, Finset.card_doubleton (Ne.symm hba)⟩
    · rw [hSj, Finset.erase_insert (by simpa using Ne.symm hba)]
  calc (coverD J S a).card = ((coverD J S a).map _).card := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_of_subset hsub
    _ ≤ _ := Finset.card_image_le

lemma cover_R {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N))
    (hcov : ∀ I : Finset (Fin N), I.card = 4 → ∀ a ∈ I,
      ∃ j ∈ J, a ∈ S j ∧ S j ⊆ I ∧ 2 ≤ (S j).card) (a : Fin N) :
    (coverU J S a).card.choose 3 ≤
      ((coverU J S a).card - 2) * (coverR J S 3 a).card + (coverR J S 4 a).card := by
  have haU : a ∉ coverU J S a := by simp [coverU]
  have hserve : ∀ Y ∈ (coverU J S a).powersetCard 3,
      1 ≤ ((coverR J S 3 a ∪ coverR J S 4 a).filter fun j => (S j).erase a ⊆ Y).card := by
    intro Y hY
    rw [Finset.mem_powersetCard] at hY
    obtain ⟨hYU, hY3⟩ := hY
    have haY : a ∉ Y := fun h => haU (hYU h)
    obtain ⟨j, hjJ, haj, hjI, hj2⟩ := hcov (insert a Y)
      (by rw [Finset.card_insert_of_not_mem haY, hY3]) a (Finset.mem_insert_self _ _)
    have hj4 : (S j).card ≤ 4 := by
      have := Finset.card_le_of_subset hjI
      rwa [Finset.card_insert_of_not_mem haY, hY3] at this
    have hEY : (S j).erase a ⊆ Y := by
      intro z hz
      rw [Finset.mem_erase] at hz
      rcases Finset.mem_insert.1 (hjI hz.2) with h | h
      · exact absurd h hz.1
      · exact h
    have hEU : (S j).erase a ⊆ coverU J S a := hEY.trans hYU
    have hne2 : (S j).card ≠ 2 := by
      intro h2
      have hc : ((S j).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem haj, h2]
      obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc
      have hbS : b ∈ (S j).erase a := by rw [hb]; exact Finset.mem_singleton_self b
      have hSj : S j = {a, b} := by
        rw [← Finset.insert_erase haj, hb]
      have hbU := hEU hbS
      simp only [coverU, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
      exact hbU.2 j hjJ hSj
    refine Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨?_, hEY⟩⟩
    have h34 : (S j).card = 3 ∨ (S j).card = 4 := by
      rcases Nat.lt_or_ge (S j).card 4 with h | h
      · left
        exact le_antisymm (Nat.lt_succ_iff.1 h) (Nat.succ_le_of_lt (lt_of_le_of_ne hj2 (Ne.symm hne2)))
      · right; exact le_antisymm hj4 h
    rcases h34 with h3 | h4
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hjJ, haj, h3, hEU⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjJ, haj, h4, hEU⟩)
  have hdisj : Disjoint (coverR J S 3 a) (coverR J S 4 a) := by
    rw [Finset.disjoint_left]
    intro j h3 h4
    simp only [coverR, Finset.mem_filter] at h3 h4
    rw [h3.2.2.1] at h4
    exact absurd h4.2.2.1 (by norm_num)
  calc (coverU J S a).card.choose 3 = ((coverU J S a).powersetCard 3).card :=
        (Finset.card_powersetCard _ _).symm
    _ = ∑ Y in (coverU J S a).powersetCard 3, 1 := by simp
    _ ≤ ∑ Y in (coverU J S a).powersetCard 3,
          ((coverR J S 3 a ∪ coverR J S 4 a).filter fun j => (S j).erase a ⊆ Y).card :=
        Finset.sum_le_sum hserve
    _ = ∑ j in coverR J S 3 a ∪ coverR J S 4 a,
          ((coverU J S a).powersetCard 3 |>.filter fun Y => (S j).erase a ⊆ Y).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ = ∑ j in coverR J S 3 a,
          ((coverU J S a).powersetCard 3 |>.filter fun Y => (S j).erase a ⊆ Y).card +
        ∑ j in coverR J S 4 a,
          ((coverU J S a).powersetCard 3 |>.filter fun Y => (S j).erase a ⊆ Y).card :=
        Finset.sum_union hdisj
    _ ≤ ∑ j in coverR J S 3 a, ((coverU J S a).card - 2) + ∑ j in coverR J S 4 a, 1 := by
        gcongr with j hj j hj
        · simp only [coverR, Finset.mem_filter] at hj
          exact fiber_two hj.2.2.2 (by rw [Finset.card_erase_of_mem hj.2.1, hj.2.2.1])
        · simp only [coverR, Finset.mem_filter] at hj
          exact fiber_three (by rw [Finset.card_erase_of_mem hj.2.1, hj.2.2.1])
    _ = ((coverU J S a).card - 2) * (coverR J S 3 a).card + (coverR J S 4 a).card := by
        simp [Finset.sum_const, mul_comm]

/-- **Lemma K.** If every pair `(I, a)` with `|I| = 4`, `a ∈ I` is served by some `S j` with
`|S j| ≥ 2` and `a ∈ S j ⊆ I`, then `3N² ≤ 6|J| + 11N`. -/
theorem cover_count {ι : Type*} [DecidableEq ι] (J : Finset ι) (S : ι → Finset (Fin N))
    (hcov : ∀ I : Finset (Fin N), I.card = 4 → ∀ a ∈ I,
      ∃ j ∈ J, a ∈ S j ∧ S j ⊆ I ∧ 2 ≤ (S j).card) :
    3 * N * N ≤ 6 * J.card + 11 * N := by
  have hvert : ∀ a : Fin N, 6 * N ≤ 6 * (coverP J S 2 a).card + 4 * (coverR J S 3 a).card +
      3 * (coverR J S 4 a).card + 22 := by
    intro a
    have h1 := cover_arith _ _ _ (cover_R J S hcov a)
    have h2 := cover_D_le J S a
    have h3 := cover_DU J S a
    linarith
  have hR3 : ∀ a, (coverR J S 3 a).card ≤ (coverP J S 3 a).card := fun a =>
    Finset.card_le_of_subset fun j hj => by
      simp only [coverR, coverP, Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.1, hj.2.2.1⟩
  have hR4 : ∀ a, (coverR J S 4 a).card ≤ (coverP J S 4 a).card := fun a =>
    Finset.card_le_of_subset fun j hj => by
      simp only [coverR, coverP, Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.1, hj.2.2.1⟩
  have s2 : ∑ a : Fin N, (coverP J S 2 a).card = 2 * (J.filter fun j => (S j).card = 2).card :=
    card_filter_mem_card J S 2
  have s3 : ∑ a : Fin N, (coverP J S 3 a).card = 3 * (J.filter fun j => (S j).card = 3).card :=
    card_filter_mem_card J S 3
  have s4 : ∑ a : Fin N, (coverP J S 4 a).card = 4 * (J.filter fun j => (S j).card = 4).card :=
    card_filter_mem_card J S 4
  have hJ : (J.filter fun j => (S j).card = 2).card + (J.filter fun j => (S j).card = 3).card +
      (J.filter fun j => (S j).card = 4).card ≤ J.card := by
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> omega
  have t3 : ∑ a : Fin N, (coverR J S 3 a).card ≤ ∑ a : Fin N, (coverP J S 3 a).card :=
    Finset.sum_le_sum fun a _ => hR3 a
  have t4 : ∑ a : Fin N, (coverR J S 4 a).card ≤ ∑ a : Fin N, (coverP J S 4 a).card :=
    Finset.sum_le_sum fun a _ => hR4 a
  have total : ∑ a : Fin N, 6 * N ≤
      ∑ a : Fin N, (6 * (coverP J S 2 a).card + 4 * (coverR J S 3 a).card +
        3 * (coverR J S 4 a).card + 22) :=
    Finset.sum_le_sum fun a _ => hvert a
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at total
  have hNN : N * (6 * N) = 6 * (N * N) := by ring
  have h3N : 3 * N * N = 3 * (N * N) := by ring
  rw [hNN] at total
  rw [h3N]
  linarith

end Frontier
end MaxCaterpillar
