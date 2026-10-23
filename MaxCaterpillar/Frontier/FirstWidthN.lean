import MaxCaterpillar.Frontier.Claw
import MaxCaterpillar.Frontier.CoverCount
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Set.Intervals.Infinite

/-! # A quadratic lower bound on the first width for every `N`

* `exists_generic_point`: for finitely many rows and a coordinate set `I` there is a point `q`,
  zero on `I` and `≤ -1` off `I`, such that `Aⱼ·q = 0` forces `supp Aⱼ ⊆ I`
  (`q_o = -t^(o+1)` with `t` outside the roots of finitely many polynomials).
* `ZNet.cover4`: for every 4-set `I` and `a ∈ I` some translation-invariant row has
  `a ∈ supp Aⱼ ⊆ I` and `|supp Aⱼ| ≥ 2` (claw lemma at a generic point).
* `ZNet.first_width_quadratic`: `3N² + 12 ≤ 6h₁ + 11N`, i.e. `h₁ ≥ C(N,2) - ⌊4N/3⌋ + 2`
  (covering count `cover_count` plus one row with `s > 0` and one with `s < 0`).
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators Polynomial

variable {N h₁ h₂ : ℕ}

/-- A generic point: zero on `I`, `≤ -1` off `I`, and a row vanishing there has support in `I`. -/
theorem exists_generic_point {ι : Type*} [Fintype ι] (A : ι → Point N) (I : Finset (Fin N)) :
    ∃ q : Point N, (∀ i ∈ I, q i = 0) ∧ (∀ i ∉ I, q i ≤ -1) ∧
      ∀ j, lin (A j) q = 0 → ∀ i ∉ I, A j i = 0 := by
  classical
  let P : ι → ℝ[X] := fun j => ∑ i in Iᶜ, C (A j i) * X ^ (i.val + 1)
  have hcoeff : ∀ j, ∀ i ∉ I, (P j).coeff (i.val + 1) = A j i := by
    intro j i hi
    simp only [P, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      rw [if_neg]
      intro h
      exact hne (Fin.ext (by omega)).symm
    · intro h; exact absurd (Finset.mem_compl.2 hi) h
  let qt : ℝ → Point N := fun t i => if i ∈ I then 0 else -t ^ (i.val + 1)
  have heval : ∀ j t, lin (A j) (qt t) = -(P j).eval t := by
    intro j t
    simp only [lin, qt, P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, mul_ite,
      mul_zero, mul_neg]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr
    · ext i; simp
    · intro i _; rfl
  let B : Finset ℝ := (Finset.univ.filter fun j => P j ≠ 0).biUnion fun j => (P j).roots.toFinset
  obtain ⟨t, ht1, htB⟩ := (Set.Ici_infinite (1 : ℝ)).exists_not_mem_finset B
  refine ⟨qt t, fun i hi => by simp [qt, hi], fun i hi => ?_, fun j hj i hi => ?_⟩
  · simp only [qt, if_neg hi, neg_le_neg_iff]
    exact one_le_pow_of_one_le (Set.mem_Ici.1 ht1) _
  · have hP : P j = 0 := by
      by_contra hne
      apply htB
      rw [Finset.mem_biUnion]
      refine ⟨j, by simp [hne], ?_⟩
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      have := heval j t
      rw [hj] at this
      linarith
    rw [← hcoeff j i hi, hP, coeff_zero]

/-- The support of a first-layer row. -/
noncomputable def ZNet.supp (net : ZNet N h₁ h₂) (j : Fin h₁) : Finset (Fin N) :=
  Finset.univ.filter fun i => net.A j i ≠ 0

/-- **Corollary C4′.** For every 4-set `I` and every `a ∈ I` some translation-invariant row has
`a ∈ supp Aⱼ ⊆ I` and at least two nonzero coordinates. -/
theorem ZNet.cover4 [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (I : Finset (Fin N)) (hI : I.card = 4) (a : Fin N) (haI : a ∈ I) :
    ∃ j ∈ Finset.univ.filter (fun j => net.s j = 0),
      a ∈ net.supp j ∧ net.supp j ⊆ I ∧ 2 ≤ (net.supp j).card := by
  obtain ⟨q, hq0, hq1, hgen⟩ := exists_generic_point net.A I
  obtain ⟨j, hs, hlin, ha⟩ := net.claw h I a haI
    (by rw [Finset.card_erase_of_mem haI, hI]) q hq0 hq1
  refine ⟨j, by simp [hs], by simp [ZNet.supp, ha], fun i hi => ?_, ?_⟩
  · by_contra hiI
    simp only [ZNet.supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi (hgen j hlin i hiI)
  · have hb : ∃ b, b ≠ a ∧ net.A j b ≠ 0 := by
      by_contra hc
      push_neg at hc
      have : ∑ i, net.A j i = net.A j a :=
        Finset.sum_eq_single a (fun b _ hb => hc b hb) (by simp)
      exact ha (by rw [← this]; exact hs)
    obtain ⟨b, hba, hbne⟩ := hb
    exact Finset.one_lt_card.2 ⟨a, by simp [ZNet.supp, ha], b, by simp [ZNet.supp, hbne],
      hba.symm⟩

/-- **Theorem Q (first width, every `N`).** A bias-free network computing `max_N` satisfies
`3N² + 12 ≤ 6h₁ + 11N`. -/
theorem ZNet.first_width_quadratic [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : 3 * N * N + 12 ≤ 6 * h₁ + 11 * N := by
  classical
  set J0 := Finset.univ.filter fun j => net.s j = 0 with hJ0
  have hcov := cover_count J0 net.supp fun I hI a haI => net.cover4 h I hI a haI
  obtain ⟨p, hp⟩ := net.exists_pos h
  obtain ⟨n, hn⟩ := net.exists_neg h
  have hpJ : p ∉ J0 := by simp [hJ0, hp.ne']
  have hnJ : n ∉ J0 := by simp [hJ0, hn.ne]
  have hpn : p ≠ n := fun e => by rw [e] at hp; linarith
  have hcard : J0.card + 2 ≤ h₁ := by
    have h1 : (insert p (insert n J0)).card = J0.card + 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem hnJ]
      rw [Finset.mem_insert]; push_neg; exact ⟨hpn, hpJ⟩
    have h2 := Finset.card_le_univ (insert p (insert n J0))
    rw [Fintype.card_fin] at h2
    linarith
  linarith

end Frontier
end MaxCaterpillar
