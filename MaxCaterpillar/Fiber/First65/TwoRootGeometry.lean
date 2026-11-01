import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-! # Complementary coordinate-difference supports

Two nonzero zero-sum rows in four coordinates whose supports are disjoint
are scalar multiples of complementary coordinate differences. This is a
linear-algebra statement; its hypotheses are not a definition of a network
fiber or a substitute for the network classification.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

open BigOperators

/-- The finite support of a real vector. -/
noncomputable def nonzeroCoordinates {ι : Type*} [Fintype ι] (a : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_nonzeroCoordinates {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) :
    i ∈ nonzeroCoordinates a ↔ a i ≠ 0 := by
  classical
  simp [nonzeroCoordinates]

/-- A nonzero zero-sum vector has at least two nonzero coordinates. -/
theorem two_le_card_nonzeroCoordinates {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (hsum : ∑ i, a i = 0) (hne : a ≠ 0) :
    2 ≤ (nonzeroCoordinates a).card := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, a p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨q, hqp, hq⟩ : ∃ q, q ≠ p ∧ a q ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : ∑ i, a i = a p := Finset.sum_eq_single p
      (fun i _ hip => h i hip) (by simp)
    exact hp (hs.symm.trans hsum)
  have hsub : ({p, q} : Finset ι) ⊆ nonzeroCoordinates a := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · subst i; exact (mem_nonzeroCoordinates a p).2 hp
    · subst i; exact (mem_nonzeroCoordinates a q).2 hq
  have hc := Finset.card_le_of_subset hsub
  simpa [Ne.symm hqp] using hc

/-- A zero-sum vector supported on a pair is a coordinate difference. -/
theorem eq_coordinate_difference_of_support_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (hsum : ∑ i, a i = 0) (p q : ι) (hpq : p ≠ q)
    (hsupport : nonzeroCoordinates a = {p, q}) :
    a p ≠ 0 ∧ ∀ i, a i =
      a p * (if i = p then 1 else 0) - a p * (if i = q then 1 else 0) := by
  classical
  have hp : a p ≠ 0 := (mem_nonzeroCoordinates a p).1 (by rw [hsupport]; simp)
  have hout : ∀ i, i ≠ p → i ≠ q → a i = 0 := by
    intro i hip hiq
    by_contra hi
    have hm := (mem_nonzeroCoordinates a i).2 hi
    rw [hsupport] at hm
    simp [hip, hiq] at hm
  have hpair : a p + a q = 0 := by
    calc
      a p + a q = ∑ i in ({p, q} : Finset ι), a i := (Finset.sum_pair hpq).symm
      _ = ∑ i, a i := Finset.sum_subset (Finset.subset_univ _) (by
        intro i _ hi
        apply hout i
        · intro hip; apply hi; simp [hip]
        · intro hiq; apply hi; simp [hiq])
      _ = 0 := hsum
  refine ⟨hp, fun i => ?_⟩
  by_cases hip : i = p
  · subst i
    simp [hpq]
  · by_cases hiq : i = q
    · subst i
      simp only [Ne.symm hpq, if_false, if_true, mul_zero, mul_one, zero_sub]
      linarith
    · simp [hip, hiq, hout i hip hiq]

/-- Disjoint nonzero zero-sum vectors on four coordinates occupy two
complementary pairs, with no other directions possible. -/
theorem complementary_coordinate_differences
    (a b : Fin 4 → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hdisj : ∀ i, a i = 0 ∨ b i = 0) :
    ∃ p q r s : Fin 4,
      p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      a p ≠ 0 ∧ b r ≠ 0 ∧
      (∀ i, a i = a p * (if i = p then 1 else 0) -
        a p * (if i = q then 1 else 0)) ∧
      (∀ i, b i = b r * (if i = r then 1 else 0) -
        b r * (if i = s then 1 else 0)) := by
  classical
  have hda : 2 ≤ (nonzeroCoordinates a).card := two_le_card_nonzeroCoordinates a ha ha0
  have hdb : 2 ≤ (nonzeroCoordinates b).card := two_le_card_nonzeroCoordinates b hb hb0
  have hd : Disjoint (nonzeroCoordinates a) (nonzeroCoordinates b) := by
    apply Finset.disjoint_left.2
    intro i hia hib
    rcases hdisj i with h | h
    · exact ((mem_nonzeroCoordinates a i).1 hia) h
    · exact ((mem_nonzeroCoordinates b i).1 hib) h
  have hc : (nonzeroCoordinates a).card + (nonzeroCoordinates b).card ≤ 4 := by
    rw [← Finset.card_union_eq hd]
    simpa using Finset.card_le_univ (nonzeroCoordinates a ∪ nonzeroCoordinates b)
  have hca : (nonzeroCoordinates a).card = 2 := by omega
  have hcb : (nonzeroCoordinates b).card = 2 := by omega
  obtain ⟨p, q, hpq, hpa⟩ := Finset.card_eq_two.1 hca
  obtain ⟨r, s, hrs, hrb⟩ := Finset.card_eq_two.1 hcb
  have hcross : ∀ i ∈ ({p, q} : Finset (Fin 4)),
      ∀ j ∈ ({r, s} : Finset (Fin 4)), i ≠ j := by
    intro i hi j hj hij
    apply Finset.disjoint_left.1 hd
    · rw [hpa]; exact hi
    · rw [hrb, hij]; exact hj
  obtain ⟨hap, heqa⟩ := eq_coordinate_difference_of_support_pair a ha p q hpq hpa
  obtain ⟨hbr, heqb⟩ := eq_coordinate_difference_of_support_pair b hb r s hrs hrb
  exact ⟨p, q, r, s, hpq, hrs, hcross p (by simp) r (by simp),
    hcross p (by simp) s (by simp), hcross q (by simp) r (by simp),
    hcross q (by simp) s (by simp), hap, hbr, heqa, heqb⟩

/-- Orient a two-coordinate zero-sum row so that its coefficient is positive. -/
theorem positive_coordinate_difference_of_card_two {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℝ) (ha : ∑ i, a i = 0)
    (hc : (nonzeroCoordinates a).card = 2) :
    ∃ p q : ι, ∃ c : ℝ, p ≠ q ∧ 0 < c ∧ nonzeroCoordinates a = {p, q} ∧
      ∀ i, a i = c * (if i = p then 1 else 0) - c * (if i = q then 1 else 0) := by
  classical
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.1 hc
  obtain ⟨hap, heq⟩ := eq_coordinate_difference_of_support_pair a ha p q hpq hs
  rcases lt_or_gt_of_ne hap with hneg | hpos
  · refine ⟨q, p, -a p, Ne.symm hpq, neg_pos.2 hneg, ?_, ?_⟩
    · rw [hs, Finset.pair_comm]
    · intro i
      rw [heq i]
      ring
  · exact ⟨p, q, a p, hpq, hpos, hs, heq⟩

/-- The two disjoint rows can be oriented as complementary coordinate
differences with strictly positive scaling factors. -/
theorem complementary_positive_coordinate_differences
    (a b : Fin 4 → ℝ) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hdisj : ∀ i, a i = 0 ∨ b i = 0) :
    ∃ p q r s : Fin 4, ∃ ca cb : ℝ,
      p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      0 < ca ∧ 0 < cb ∧
      (∀ i, a i = ca * (if i = p then 1 else 0) - ca * (if i = q then 1 else 0)) ∧
      (∀ i, b i = cb * (if i = r then 1 else 0) - cb * (if i = s then 1 else 0)) := by
  classical
  have hda := two_le_card_nonzeroCoordinates a ha ha0
  have hdb := two_le_card_nonzeroCoordinates b hb hb0
  have hd : Disjoint (nonzeroCoordinates a) (nonzeroCoordinates b) := by
    apply Finset.disjoint_left.2
    intro i hia hib
    rcases hdisj i with h | h
    · exact ((mem_nonzeroCoordinates a i).1 hia) h
    · exact ((mem_nonzeroCoordinates b i).1 hib) h
  have hc : (nonzeroCoordinates a).card + (nonzeroCoordinates b).card ≤ 4 := by
    rw [← Finset.card_union_eq hd]
    simpa using Finset.card_le_univ (nonzeroCoordinates a ∪ nonzeroCoordinates b)
  obtain ⟨p, q, ca, hpq, hca, hpa, heqa⟩ :=
    positive_coordinate_difference_of_card_two a ha (by omega)
  obtain ⟨r, s, cb, hrs, hcb, hrb, heqb⟩ :=
    positive_coordinate_difference_of_card_two b hb (by omega)
  have hcross : ∀ i ∈ ({p, q} : Finset (Fin 4)),
      ∀ j ∈ ({r, s} : Finset (Fin 4)), i ≠ j := by
    intro i hi j hj hij
    apply Finset.disjoint_left.1 hd
    · rw [hpa]; exact hi
    · rw [hrb, hij]; exact hj
  exact ⟨p, q, r, s, ca, cb, hpq, hrs, hcross p (by simp) r (by simp),
    hcross p (by simp) s (by simp), hcross q (by simp) r (by simp),
    hcross q (by simp) s (by simp), hca, hcb, heqa, heqb⟩

end Fiber
end MaxCaterpillar
