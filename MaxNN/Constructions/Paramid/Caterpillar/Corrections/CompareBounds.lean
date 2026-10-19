import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic

/-! # Comparison with the former HDR closed second-width bound

This file contains only symbolic natural-number estimates.  It does not import
the HDR construction or enumerate any finite arities.
-/

namespace MaxNN.Caterpillar.Corrections

/-- Removing the harmless factor `1` gives the standard sharper power bound
`n! ≤ n^(n-1)` for positive `n`. -/
theorem factorial_le_pow_pred {n : ℕ} (hn : 1 ≤ n) :
    n.factorial ≤ n ^ (n - 1) := by
  have hdesc := Nat.descFactorial_le_pow n (n - 1)
  have hfac := Nat.factorial_mul_descFactorial (n := n) (k := n - 1)
    (Nat.sub_le n 1)
  have hone : n - (n - 1) = 1 := by omega
  rw [hone, Nat.factorial_one, one_mul] at hfac
  rwa [hfac] at hdesc

/-- The factorial in the caterpillar bound is controlled by the same
`(N-1)^(N-2)` factor occurring in the HDR base. -/
theorem factorial_le_mul_pow_pred (N : ℕ) (hN : 2 ≤ N) :
    N.factorial ≤ N * (N - 1) ^ (N - 2) := by
  have hpred := factorial_le_pow_pred (n := N - 1) (by omega)
  have hNsucc : N = (N - 1) + 1 := by omega
  have hexp : N - 1 - 1 = N - 2 := by omega
  rw [hexp] at hpred
  have hfac : N.factorial = N * (N - 1).factorial := by
    calc
      N.factorial = ((N - 1) + 1).factorial := by rw [← hNsucc]
      _ = ((N - 1) + 1) * (N - 1).factorial := Nat.factorial_succ _
      _ = N * (N - 1).factorial := by rw [← hNsucc]
  rw [hfac]
  exact Nat.mul_le_mul_left N hpred

private theorem self_le_sixtysix_pow_pred (N : ℕ) (hN : 2 ≤ N) :
    N ≤ 66 ^ (N - 1) := by
  have htwo : N ≤ 2 ^ N := (Nat.lt_two_pow N).le
  have hpow : 2 ^ N ≤ 66 ^ (N - 1) := by
    have hNsucc : N = (N - 1) + 1 := by omega
    have h33 : 2 ≤ 33 ^ (N - 1) := by
      exact (by norm_num : 2 ≤ 33).trans
        (le_self_pow (by norm_num : 1 ≤ (33 : ℕ)) (by omega))
    calc
      2 ^ N = 2 ^ ((N - 1) + 1) := by rw [← hNsucc]
      _ = 2 ^ (N - 1) * 2 := by rw [pow_succ, mul_comm]
      2 ^ (N - 1) * 2 ≤ 2 ^ (N - 1) * 33 ^ (N - 1) :=
        Nat.mul_le_mul_left _ h33
      _ = 66 ^ (N - 1) := by rw [← mul_pow]
  exact htwo.trans hpow

/-- Before the final `+2`, the caterpillar closed bound is strictly smaller
than the former HDR closed bound for every common arity `N ≥ 5`. -/
theorem caterpillar_closed_core_lt_HDR_closed_core (N : ℕ) (hN : 5 ≤ N) :
    N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) <
      (9 * (N - 1)) ^ (N - 2) * 66 ^ (N - 1) := by
  have hpow2 : 0 < 2 ^ (N - 2) := pow_pos (by decide) _
  have hsub : 2 ^ (N - 2) - 1 < 2 ^ (N - 2) := by omega
  have hstrict :
      N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) <
        N.factorial * 2 ^ (N - 2) * 3 ^ (N - 2) := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left hsub (Nat.factorial_pos N))
      (pow_pos (by decide) _)
  have hfac := factorial_le_mul_pow_pred N (by omega)
  have hN66 := self_le_sixtysix_pow_pred N (by omega)
  have hbase : 6 * (N - 1) ≤ 9 * (N - 1) := by omega
  calc
    N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) <
        N.factorial * 2 ^ (N - 2) * 3 ^ (N - 2) := hstrict
    _ = N.factorial * 6 ^ (N - 2) := by
      rw [mul_assoc, ← mul_pow]
    _ ≤ (N * (N - 1) ^ (N - 2)) * 6 ^ (N - 2) :=
      Nat.mul_le_mul_right _ hfac
    _ = N * (6 * (N - 1)) ^ (N - 2) := by
      rw [mul_assoc, mul_comm ((N - 1) ^ (N - 2)), ← mul_pow]
    _ ≤ 66 ^ (N - 1) * (9 * (N - 1)) ^ (N - 2) :=
      Nat.mul_le_mul hN66 (Nat.pow_le_pow_left hbase _)
    _ = (9 * (N - 1)) ^ (N - 2) * 66 ^ (N - 1) := by
      rw [mul_comm]

/-- Consequently the full caterpillar second-width bound, including the two
linear-remainder neurons, is strictly smaller than the HDR bound. -/
theorem caterpillar_closed_secondWidth_lt_HDR_closed_secondWidth
    (N : ℕ) (hN : 5 ≤ N) :
    N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) + 2 <
      (9 * (N - 1)) ^ (N - 2) * 66 ^ (N - 1) + 2 :=
  Nat.add_lt_add_right (caterpillar_closed_core_lt_HDR_closed_core N hN) 2

theorem caterpillar_closed_secondWidth_le_HDR_closed_secondWidth
    (N : ℕ) (hN : 5 ≤ N) :
    N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) + 2 ≤
      (9 * (N - 1)) ^ (N - 2) * 66 ^ (N - 1) + 2 :=
  (caterpillar_closed_secondWidth_lt_HDR_closed_secondWidth N hN).le

end MaxNN.Caterpillar.Corrections
