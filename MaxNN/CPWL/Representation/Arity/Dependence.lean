import MaxNN.CPWL.Representation.Arity.MaxOn
import Mathlib.LinearAlgebra.FiniteDimensional

/-!
# Affine dependence among `d+2` affine functions on `ℝ^d`

The geometric input of the arity reduction.  Among any `d+2` (or more) affine functions
`g j = ⟨a_j, c_j⟩` on `ℝ^d`, the lifted gradients `(1, a_j) ∈ ℝ^{d+1}` are linearly
dependent: there is `λ` with `∑ λ_j = 0`, `∑ λ_j a_j = 0`, `λ ≠ 0`
(`exists_affine_relation`).  Consequently `∑_j λ_j g_j(x) = ∑_j λ_j c_j =: κ` is constant in
`x` (`sum_mul_eval_eq_const`), and after flipping the sign of `λ` we may assume `κ ≥ 0`.

With `J := {j : λ_j < 0}` (nonempty, with nonempty complement in `S`), the constant identity
forces, at **every** point `x`, some `j ∈ J` with `g_j(x) ≤ max_{S \ J} g(x)`: otherwise
all `g_j(x)`, `j ∈ J`, would exceed that maximum and the weighted sum would be negative
(`exists_dominating_subset`).  This is exactly the hypothesis of the inclusion–exclusion
identity (`Arity/InclusionExclusion.lean`).

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- When the gradients satisfy `∑_{j ∈ S} λ_j a_j = 0`, the weighted sum
`∑_{j ∈ S} λ_j g_j(x)` is the constant `∑_{j ∈ S} λ_j c_j`. -/
theorem sum_mul_eval_eq_const {d m : ℕ} (g : Fin m → AffineFn d) (S : Finset (Fin m))
    (lam : Fin m → ℝ) (hgrad : ∀ i : Fin d, ∑ j in S, lam j * (g j).a i = 0)
    (x : Fin d → ℝ) :
    ∑ j in S, lam j * (g j).eval x = ∑ j in S, lam j * (g j).c := by
  have e : ∀ j ∈ S, lam j * (g j).eval x
      = (∑ i, lam j * (g j).a i * x i) + lam j * (g j).c := by
    intro j _
    show lam j * ((∑ i, (g j).a i * x i) + (g j).c) = _
    rw [mul_add, Finset.mul_sum,
      Finset.sum_congr rfl fun i _ => (mul_assoc (lam j) ((g j).a i) (x i)).symm]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_comm]
  have e2 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ∑ j in S, lam j * (g j).a i * x i = 0 := by
    intro i _
    rw [← Finset.sum_mul, hgrad i, zero_mul]
  rw [Finset.sum_congr rfl e2, Finset.sum_const_zero, zero_add]

/-- **Affine dependence.**  More than `d+1` affine functions on `ℝ^d` admit a nontrivial
relation `∑ λ_j = 0`, `∑ λ_j a_j = 0` among their gradients. -/
theorem exists_affine_relation {d m : ℕ} (g : Fin m → AffineFn d) (S : Finset (Fin m))
    (hcard : d + 2 ≤ S.card) :
    ∃ lam : Fin m → ℝ, (∑ j in S, lam j = 0) ∧ (∀ i : Fin d, ∑ j in S, lam j * (g j).a i = 0)
      ∧ ∃ j ∈ S, lam j ≠ 0 := by
  classical
  have hdep : ¬ LinearIndependent ℝ
      (fun j : S => (Fin.cons (1 : ℝ) (g j).a : Fin (d + 1) → ℝ)) := by
    intro hli
    have h1 := FiniteDimensional.fintype_card_le_finrank_of_linearIndependent hli
    rw [Fintype.card_coe, FiniteDimensional.finrank_fin_fun ℝ] at h1
    linarith
  obtain ⟨c, hc, j₁, hj₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hsumc : ∑ j : S, c j = 0 := by
    have h0 := congrFun hc 0
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Fin.cons_zero, mul_one]
  have hgradc : ∀ i : Fin d, ∑ j : S, c j * (g j).a i = 0 := by
    intro i
    have h0 := congrFun hc i.succ
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
  refine ⟨fun j => if h : j ∈ S then c ⟨j, h⟩ else 0, ?_, ?_, ⟨j₁, j₁.2, ?_⟩⟩
  · rw [← Finset.sum_coe_sort]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hsumc
    exact dif_pos j.2
  · intro i
    rw [← Finset.sum_coe_sort]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hgradc i)
    show (if h : (j : Fin m) ∈ S then c ⟨j, h⟩ else 0) * (g j).a i = c j * (g j).a i
    rw [dif_pos j.2]
  · show (if h : (j₁ : Fin m) ∈ S then c ⟨j₁, h⟩ else 0) ≠ 0
    rw [dif_pos j₁.2]
    exact hj₁

/-- From a relation with nonnegative constant `κ = ∑ λ_j c_j ≥ 0`: the negative-weight
indices `J` are nonempty with nonempty complement, and at every point some `j ∈ J` is
dominated by the maximum over `S \ J`. -/
theorem exists_dominated_of_relation {d m : ℕ} (g : Fin m → AffineFn d) (S : Finset (Fin m))
    (lam : Fin m → ℝ) (hsum : ∑ j in S, lam j = 0)
    (hgrad : ∀ i : Fin d, ∑ j in S, lam j * (g j).a i = 0)
    (hne : ∃ j ∈ S, lam j ≠ 0) (hκ : 0 ≤ ∑ j in S, lam j * (g j).c) :
    ∃ J : Finset (Fin m), J ⊆ S ∧ (S \ J).Nonempty ∧
      ∀ x, ∃ j ∈ J, (g j).eval x ≤ maxOn (S \ J) fun i => (g i).eval x := by
  classical
  have hJS : S.filter (fun j => lam j < 0) ⊆ S := Finset.filter_subset _ S
  have hJne : (S.filter (fun j => lam j < 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hnonneg : ∀ j ∈ S, 0 ≤ lam j := by
      intro j hj
      by_contra hlt
      have hmem : j ∈ S.filter (fun j => lam j < 0) :=
        Finset.mem_filter.mpr ⟨hj, lt_of_not_le hlt⟩
      rw [hcon] at hmem
      exact Finset.not_mem_empty j hmem
    obtain ⟨j, hj, hj0⟩ := hne
    exact hj0 ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j hj)
  have hSJ : (S \ S.filter (fun j => lam j < 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
    have hneg : ∀ j ∈ S, lam j < 0 := fun j hj => (Finset.mem_filter.mp (hcon hj)).2
    have hSne : S.Nonempty := hJne.mono hJS
    have hlt := Finset.sum_neg hneg hSne
    rw [hsum] at hlt
    exact lt_irrefl 0 hlt
  refine ⟨S.filter (fun j => lam j < 0), hJS, hSJ, fun x => ?_⟩
  by_contra hcon
  have hgt : ∀ j ∈ S.filter (fun j => lam j < 0),
      maxOn (S \ S.filter (fun j => lam j < 0)) (fun i => (g i).eval x) < (g j).eval x :=
    fun j hj => lt_of_not_le fun h => hcon ⟨j, hj, h⟩
  have hA : ∑ j in S \ S.filter (fun j => lam j < 0), lam j * (g j).eval x
      ≤ ∑ j in S \ S.filter (fun j => lam j < 0),
          lam j * maxOn (S \ S.filter (fun j => lam j < 0)) (fun i => (g i).eval x) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_sdiff.mp hj
    have hlam : 0 ≤ lam j := by
      by_contra hlt
      exact hj'.2 (Finset.mem_filter.mpr ⟨hj'.1, lt_of_not_le hlt⟩)
    exact mul_le_mul_of_nonneg_left (le_maxOn (fun i => (g i).eval x) hj) hlam
  have hB : ∑ j in S.filter (fun j => lam j < 0), lam j * (g j).eval x
      < ∑ j in S.filter (fun j => lam j < 0),
          lam j * maxOn (S \ S.filter (fun j => lam j < 0)) (fun i => (g i).eval x) := by
    refine Finset.sum_lt_sum (fun j hj => ?_) ?_
    · exact le_of_lt (mul_lt_mul_of_neg_left (hgt j hj) (Finset.mem_filter.mp hj).2)
    · obtain ⟨j, hj⟩ := hJne
      exact ⟨j, hj, mul_lt_mul_of_neg_left (hgt j hj) (Finset.mem_filter.mp hj).2⟩
  have htot : ∑ j in S, lam j * (g j).eval x
      < ∑ j in S, lam j * maxOn (S \ S.filter (fun j => lam j < 0)) (fun i => (g i).eval x) := by
    rw [← Finset.sum_sdiff hJS, ← Finset.sum_sdiff hJS]
    exact add_lt_add_of_le_of_lt hA hB
  have hR : ∑ j in S, lam j * maxOn (S \ S.filter (fun j => lam j < 0)) (fun i => (g i).eval x)
      = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [hR, sum_mul_eval_eq_const g S lam hgrad x] at htot
  exact absurd hκ (not_le.mpr htot)

/-- **Dominating subset.**  For `d+2` or more affine functions on `ℝ^d` indexed by `S`, there
is `J ⊆ S` with `S \ J ≠ ∅` such that at every point some `j ∈ J` is dominated by the
maximum over `S \ J`. -/
theorem exists_dominating_subset {d m : ℕ} (g : Fin m → AffineFn d) (S : Finset (Fin m))
    (hcard : d + 2 ≤ S.card) :
    ∃ J : Finset (Fin m), J ⊆ S ∧ (S \ J).Nonempty ∧
      ∀ x, ∃ j ∈ J, (g j).eval x ≤ maxOn (S \ J) fun i => (g i).eval x := by
  obtain ⟨lam, hsum, hgrad, hne⟩ := exists_affine_relation g S hcard
  rcases le_or_lt 0 (∑ j in S, lam j * (g j).c) with hκ | hκ
  · exact exists_dominated_of_relation g S lam hsum hgrad hne hκ
  · refine exists_dominated_of_relation g S (fun j => -lam j) ?_ ?_ ?_ ?_
    · rw [Finset.sum_neg_distrib, hsum, neg_zero]
    · intro i
      rw [Finset.sum_congr rfl fun j _ => neg_mul (lam j) ((g j).a i), Finset.sum_neg_distrib,
        hgrad i, neg_zero]
    · obtain ⟨j, hj, h⟩ := hne
      exact ⟨j, hj, neg_ne_zero.mpr h⟩
    · rw [Finset.sum_congr rfl fun j _ => neg_mul (lam j) ((g j).c), Finset.sum_neg_distrib]
      exact le_of_lt (neg_pos.mpr hκ)

end MaxNN
