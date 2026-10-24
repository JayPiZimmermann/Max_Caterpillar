import Mathlib.Tactic
theorem kappa_local {n : ℕ} (s : Fin 3) (p c o : Fin n) (hpc : p ≠ c) :
    ((if s = 1 then (if p = o then (1 : ℝ) else 0) - (if c = o then 1 else 0) else 0) +
        (if s = 2 ∧ c < p then (if p = o then (1 : ℝ) else 0) - (if c = o then 1 else 0) else 0) +
        (if s = 2 ∧ (if c < p then c else p) = o then (1 : ℝ) else 0)) =
      (if s ≠ 0 ∧ p = o then (1 : ℝ) else 0) - (if s = 1 ∧ c = o then (1 : ℝ) else 0) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  rcases hs with rfl | rfl | rfl <;> by_cases hcp : c < p <;>
    (try simp only [hcp, if_true, if_false, h01, h02, h12, h01.symm, h02.symm, h12.symm,
      Ne.def, not_false_eq_true, true_and, false_and, and_true, and_false, not_true,
      eq_self_iff_true]) <;>
    by_cases hp : p = o <;> by_cases hc : c = o <;>
    (try simp only [hp, hc, if_true, if_false, eq_self_iff_true]) <;>
    first | (exfalso; exact hpc (hp.trans hc.symm)) | norm_num
