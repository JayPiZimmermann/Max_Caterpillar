import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Singleton
import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.CircuitImage

/-! # A coordinate-covered triple cannot have a quotient kernel

This is a direct information-loss obstruction. It simultaneously handles
the smaller-support circuit branches in the zero-root and one-root cases.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

/-- A zero-sum row with positive coefficient at `j` has a negative
halfspace meeting every strict winner cone other than `j`. -/
theorem negative_halfspace_meets_winner (a : Point 4) (j i : Fin 4)
    (hj : 0 < a j) (hij : i ≠ j) :
    ∃ x, lin a x < 0 ∧ x i = Maximum 4 x := by
  let t : ℝ := max 0 (a i / a j) + 1
  have ht : 0 < t := by dsimp [t]; linarith only [le_max_left (0 : ℝ) (a i / a j)]
  let x : Point 4 := unitVec i - t • unitVec j
  have hxi : x i = 1 := by simp [x, unitVec, hij]
  have hxk : ∀ k, x k ≤ 1 := by
    intro k
    by_cases hki : k = i
    · rw [hki, hxi]
    · by_cases hkj : k = j
      · simp only [x, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply,
          if_neg hki, if_pos hkj, mul_one, zero_sub]
        exact (neg_nonpos.mpr ht.le).trans (by norm_num : (0 : ℝ) ≤ 1)
      · simp [x, unitVec, hki, hkj]
  refine ⟨x, ?_, hxi.trans (Maximum_eq_of x 1 i hxi hxk).symm⟩
  have hb : a i ≤ max 0 (a i / a j) * a j :=
    (div_le_iff hj).mp (le_max_right 0 (a i / a j))
  rw [show lin a x = a i - t * a j by
    simp only [x, lin_sub_right, lin_smul_right, lin_unitVec]]
  dsimp only [t]
  nlinarith only [hb, hj]

/-- If the other three rows collectively use every coordinate, their
common kernel is forced to be precisely diagonal by Max4 factorization. -/
theorem kernel_diagonal_of_covered_triple (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hsum : ∀ k, ∑ i, A k i = 0)
    (v : Fin 4) (hv : A v ≠ 0)
    (hcover : ∀ i, ∃ k, k ≠ v ∧ A k i ≠ 0)
    (w : Point 4) (hw : ∀ k, k ≠ v → lin (A k) w = 0) :
    ∃ t, w = diag t := by
  have hn : ∃ i ∈ (Finset.univ : Finset (Fin 4)), A v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext fun i => hn i (Finset.mem_univ i))
  obtain ⟨j, _, hj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero (A v) (hsum v) hn
  have he : ∀ i, i ≠ j → w i = lin ell w := by
    intro i hij
    obtain ⟨x, hx, hxi⟩ := negative_halfspace_meets_winner (A v) j i hj hij
    apply active_kernel_top_coordinate A ell Phi h x w _ i hxi
    intro k hk
    apply hw k
    intro hkv
    rw [hkv] at hk
    exact not_lt_of_ge hk hx
  obtain ⟨k, hkv, hkj⟩ := hcover j
  have hwrep : w = diag (lin ell w) + (w j - lin ell w) • unitVec j := by
    funext i
    by_cases hij : i = j
    · simp [hij, diag, unitVec]
    · simp [he i hij, diag, unitVec, hij]
  have hlast : w j = lin ell w := by
    have hz := hw k hkv
    rw [hwrep, lin_add_right, lin_diag, hsum k, mul_zero, zero_add,
      lin_smul_right, lin_unitVec] at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hkj)
  refine ⟨lin ell w, funext fun i => ?_⟩
  by_cases hij : i = j
  · simpa only [hij, diag] using hlast
  · exact he i hij

/-- Any circuit relation omitting a row is impossible when the other
three rows cover all coordinates. No assumptions on circuit signs or the
second hidden layer are needed. -/
theorem no_circuit_with_covered_dependent_triple (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hsum : ∀ k, ∑ i, A k i = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (c : Point 4) (hc : c ≠ 0)
    (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (v : Fin 4) (hcv : c v = 0)
    (hcover : ∀ i, ∃ k, k ≠ v ∧ A k i ≠ 0) : False := by
  have hz : ∑ j, c j * unitVec v j = 0 := by
    change lin c (unitVec v) = 0
    rw [lin_unitVec, hcv]
  obtain ⟨w, hw⟩ := row_values_surjective_on_circuit A c hc hrel hkernel (unitVec v) hz
  have hv : A v ≠ 0 := by
    intro he
    have hew := hw v
    rw [he, lin_zero_left] at hew
    norm_num [unitVec] at hew
  obtain ⟨t, hwt⟩ := kernel_diagonal_of_covered_triple A ell Phi h hsum v hv hcover w
    (fun k hk => by rw [hw]; simp [unitVec, hk])
  have hew := hw v
  rw [hwt, lin_diag, hsum v, mul_zero] at hew
  norm_num [unitVec] at hew

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
