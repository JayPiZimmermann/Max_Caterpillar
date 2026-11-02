import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.Weight
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exact finite Bernoulli moment generating function and exponential Markov bound. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
open BigOperators
variable {n : ℕ}

theorem mean_exp_card (p t : ℝ) :
    mean p (fun S : Finset (Fin n) => Real.exp (t * S.card)) =
      (1 - p + p * Real.exp t) ^ n := by
  classical
  have hterm (S : Finset (Fin n)) :
      weight p S * Real.exp (t * S.card) =
        ∏ i : Fin n, if i ∈ S then p * Real.exp t else 1 - p := by
    have hexp : Real.exp (t * S.card) =
        ∏ i : Fin n, if i ∈ S then Real.exp t else 1 := by
      rw [Finset.prod_ite]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
        Finset.prod_const_one, one_pow, mul_one]
      rw [mul_comm, Real.exp_nat_mul]
    rw [hexp, weight, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  unfold mean
  simp_rw [hterm]
  rw [sum_prod_choice]
  simp [add_comm]

theorem mean_exp_card_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mean p (fun S : Finset (Fin n) => Real.exp (t * S.card)) ≤
      Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := by
  rw [mean_exp_card]
  have hbase : 0 ≤ 1 - p + p * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hp0 (Real.exp_pos t).le)
  have hb : 1 - p + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
    have := Real.add_one_le_exp (p * (Real.exp t - 1))
    linarith
  calc
    (1 - p + p * Real.exp t) ^ n ≤ Real.exp (p * (Real.exp t - 1)) ^ n :=
      pow_le_pow_left hbase hb n
    _ = Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- A finite weighted exponential Markov bound, with the event supplied explicitly. -/
theorem mass_le_exp_markov (p t a : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Finset (Fin n)))
    (hE : ∀ S ∈ E, a ≤ t * (S.card : ℝ)) :
    mass p E ≤ Real.exp ((n : ℝ) * p * (Real.exp t - 1) - a) := by
  classical
  have hweighted : Real.exp a * mass p E ≤
      mean p (fun S : Finset (Fin n) => Real.exp (t * S.card)) := by
    unfold mass mean
    rw [Finset.mul_sum]
    calc
      (∑ S in E, Real.exp a * weight p S) ≤
          ∑ S in E, weight p S * Real.exp (t * S.card) := by
        apply Finset.sum_le_sum
        intro S hS
        simpa [mul_comm] using mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (hE S hS)) (weight_nonneg hp0 hp1 S)
      _ ≤ ∑ S : Finset (Fin n), weight p S * Real.exp (t * S.card) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        intro S _ _
        exact mul_nonneg (weight_nonneg hp0 hp1 S) (Real.exp_pos _).le
  have hm := hweighted.trans (mean_exp_card_le p t hp0 hp1)
  apply (mul_le_mul_left (Real.exp_pos a)).mp
  calc
    Real.exp a * mass p E ≤ Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := hm
    _ = Real.exp a * Real.exp ((n : ℝ) * p * (Real.exp t - 1) - a) := by
      rw [← Real.exp_add]
      congr 1
      ring

end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli
