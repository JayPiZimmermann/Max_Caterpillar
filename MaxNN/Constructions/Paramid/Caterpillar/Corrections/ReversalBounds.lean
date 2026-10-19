import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Reversal

/-! # Strict improvement from the path-reversal quotient

The path-reversal quotient removes half of one factorial-sized slice.  This
file records that the resulting closed width bound is strictly smaller than
the unquotiented normalized-cone bound in every relevant arity.
-/

namespace MaxNN.Caterpillar.Corrections

/-- For `N ≥ 3`, the path-reversal width bound is strictly smaller than the
raw normalized-cone width bound. -/
theorem reversal_width_bound_strict {N : ℕ} (hN : 3 ≤ N) :
    (N.factorial * (2 ^ (N - 2) - 2) + N.factorial / 2) * 3 ^ (N - 2) + 2 <
      N.factorial * (2 ^ (N - 2) - 1) * 3 ^ (N - 2) + 2 := by
  have hfac : 0 < N.factorial := Nat.factorial_pos N
  have hpow : 0 < 3 ^ (N - 2) := pow_pos (by decide) _
  have htwo : 2 ≤ 2 ^ (N - 2) := by
    have hexp : 1 ≤ N - 2 := by omega
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)
  have hhalf : N.factorial / 2 < N.factorial := by
    exact Nat.div_lt_self hfac (by decide)
  have hpred : 2 ^ (N - 2) - 1 = (2 ^ (N - 2) - 2) + 1 := by
    omega
  rw [hpred, Nat.mul_add, Nat.mul_one]
  exact Nat.add_lt_add_right
    (Nat.mul_lt_mul_of_pos_right
      (Nat.add_lt_add_left hhalf (N.factorial * (2 ^ (N - 2) - 2))) hpow) 2

end MaxNN.Caterpillar.Corrections
