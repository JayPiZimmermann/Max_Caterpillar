import MaxCaterpillar.Definitions
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Asymptotic bounds for the displayed widths -/

namespace MaxCaterpillar

open Filter Asymptotics
open scoped BigOperators

theorem firstWidth_le_square (N : ℕ) : firstWidth N ≤ (N + 1) ^ 2 := by
  have h : N.choose 2 ≤ N * N := Nat.choose_two_right N ▸
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left N (Nat.sub_le N 1))
  unfold firstWidth; nlinarith

theorem firstWidth_le_four_mul_square (N : ℕ) (hN : 1 ≤ N) :
    firstWidth N ≤ 4 * N ^ 2 :=
  (firstWidth_le_square N).trans (by nlinarith)

/-- The first displayed width is quadratic. -/
theorem firstWidth_isBigO_square :
    (fun N : ℕ => (firstWidth N : ℝ)) =O[atTop] fun N => (N : ℝ) ^ 2 :=
  IsBigO.of_bound 4 <| (eventually_ge_atTop 1).mono fun N hN => by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast firstWidth_le_four_mul_square N hN

/-- Each term of the cone count is at most `N ^ N`: the spines on `m` vertices
are at most `N ^ m` ordered selections, the apex at most `N`, and the leaf
attachments at most `N ^ (N - m - 1)`. -/
private theorem spineConeTerm_le_pow (N m : ℕ) (hm : m ∈ Finset.Icc 2 (N - 1)) :
    N.choose m * (m.factorial / 2) * (N - m) * m ^ (N - m - 1) ≤ N ^ N := by
  obtain ⟨h2, hN⟩ := Finset.mem_Icc.mp hm
  have h : N.choose m * (m.factorial / 2) ≤ N ^ m :=
    (Nat.mul_le_mul_left _ (Nat.div_le_self _ _)).trans
      (by rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          exact Nat.descFactorial_le_pow N _)
  calc N.choose m * (m.factorial / 2) * (N - m) * m ^ (N - m - 1)
      ≤ N ^ m * N ^ 1 * N ^ (N - m - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h (by rw [pow_one]; exact Nat.sub_le N _))
          (Nat.pow_le_pow_left (by omega) _)
    _ = N ^ N := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem coneCount_le_pow (N : ℕ) (hN : 3 ≤ N) : coneCount N ≤ N ^ (4 * N) :=
  calc coneCount N ≤ (Finset.Icc 2 (N - 1)).card • N ^ N :=
        Finset.sum_le_card_nsmul _ _ _ (spineConeTerm_le_pow N)
    _ ≤ N ^ N * N ^ N := by
        rw [Nat.card_Icc, smul_eq_mul]
        exact Nat.mul_le_mul_right _
          ((by omega : N - 1 + 1 - 2 ≤ N).trans (Nat.le_self_pow (by omega) N))
    _ ≤ N ^ (4 * N) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)

/-- A concrete form of the `2^{O(N log N)}` second-width estimate. -/
theorem secondWidth_le_two_mul_pow (N : ℕ) (hN : 3 ≤ N) :
    secondWidth N ≤ 2 * N ^ (5 * N) := by
  have h3 : 3 ^ (N - 2) ≤ N ^ N :=
    (Nat.pow_le_pow_left hN _).trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le N 2))
  have hmain : coneCount N * 3 ^ (N - 2) ≤ N ^ (5 * N) :=
    (Nat.mul_le_mul (coneCount_le_pow N hN) h3).trans
      ((pow_add N (4 * N) N).symm.le.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have htwo : 2 ≤ N ^ (5 * N) := (by omega : 2 ≤ N).trans (Nat.le_self_pow (by omega) N)
  calc secondWidth N ≤ N ^ (5 * N) + N ^ (5 * N) :=
        Nat.add_le_add ((Nat.sub_le _ _).trans hmain) htwo
    _ = 2 * N ^ (5 * N) := (two_mul _).symm

/-- Equivalently, the second displayed width is `O(N^(5N))`. -/
theorem secondWidth_isBigO_pow :
    (fun N : ℕ => (secondWidth N : ℝ)) =O[atTop]
      fun N => ((N ^ (5 * N) : ℕ) : ℝ) :=
  IsBigO.of_bound 2 <| (eventually_ge_atTop 3).mono fun N hN => by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast secondWidth_le_two_mul_pow N hN

theorem log_secondWidth_le (N : ℕ) (hN : 3 ≤ N) :
    Real.log (secondWidth N) ≤
      Real.log 2 + ((5 * N : ℕ) : ℝ) * Real.log N := by
  rw [← Real.log_pow, ← Real.log_mul two_ne_zero (pow_pos (Nat.cast_pos.mpr (by omega)) _).ne']
  exact Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos _))
    (by exact_mod_cast secondWidth_le_two_mul_pow N hN)

theorem log_secondWidth_le_six_mul (N : ℕ) (hN : 3 ≤ N) :
    Real.log (secondWidth N) ≤ 6 * ((N : ℝ) * Real.log N) := by
  have h2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log two_pos (by exact_mod_cast (by omega : 2 ≤ N))
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  refine (log_secondWidth_le N hN).trans ?_
  push_cast
  nlinarith [Real.log_nonneg h1]

/-- The logarithm of the second width is `O(N log N)`, i.e. the width is
`2^{O(N log N)}`. -/
theorem log_secondWidth_isBigO_mul_log :
    (fun N : ℕ => Real.log (secondWidth N)) =O[atTop]
      fun N => (N : ℝ) * Real.log N :=
  IsBigO.of_bound 6 <| (eventually_ge_atTop 3).mono fun N hN => by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact log_secondWidth_le_six_mul N hN

end MaxCaterpillar
