import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Singleton
import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.CircuitImage

/-! # Mixed-sign four-row circuits

All-negative and singleton cells are constructed in the actual row-value
image. No sign-cell enumeration or decoder regularity is assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

theorem negative_cell_readout (A : Fin 4 → Point 4) (ell : Point 4)
    (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (y : Point 4) (hy : ∀ j, lin (A j) y < 0) : ∃ m, ell = unitVec m := by
  obtain ⟨m, hm⟩ := exists_eq_Maximum y
  refine ⟨m, funext fun i => ?_⟩
  have he := active_kernel_top_coordinate A ell Phi h y (unitVec i)
    (fun j hj => False.elim (not_lt_of_ge hj (hy j))) m hm.symm
  rw [lin_unitVec] at he
  by_cases him : i = m
  · simpa [unitVec, him] using he.symm
  · simpa [unitVec, him, Ne.symm him] using he.symm

/-- A mixed-sign circuit hyperplane contains an all-negative vector. -/
theorem mixed_circuit_negative_cell (A : Fin 4 → Point 4) (c : Point 4)
    (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (p q : Fin 4) (hp : 0 < c p) (hq : c q < 0) :
    ∃ y, ∀ j, lin (A j) y < 0 := by
  let S : ℝ := ∑ j, c j
  have hex : ∃ j, c j ≠ 0 ∧ S / c j ≤ 0 := by
    rcases le_total S 0 with hs | hs
    · exact ⟨p, hp.ne', div_nonpos_of_nonpos_of_nonneg hs hp.le⟩
    · exact ⟨q, hq.ne, div_nonpos_of_nonneg_of_nonpos hs hq.le⟩
  obtain ⟨j, hj, hdiv⟩ := hex
  let z : Point 4 := -diag (1 : ℝ) + (S / c j) • unitVec j
  have hz : ∑ k, c k * z k = 0 := by
    change lin c z = 0
    simp only [z, lin_add_right, lin_neg_right, lin_diag, lin_smul_right,
      lin_unitVec, one_mul, div_mul_cancel _ hj]
    ring
  have hc : c ≠ 0 := by intro he; have he' := congr_fun he j; exact hj he'
  obtain ⟨y, hy⟩ := row_values_surjective_on_circuit A c hc hrel hkernel z hz
  refine ⟨y, fun k => ?_⟩
  rw [hy]
  by_cases hkj : k = j
  · simp only [z, Pi.add_apply, Pi.neg_apply, diag, Pi.smul_apply, smul_eq_mul,
      unitVec_apply, if_pos hkj, mul_one]
    linarith only [hdiv]
  · simp [z, diag, unitVec, hkj]

/-- A negative cell and a two-feature exchange supply a strict singleton
cell at either end, by moving far enough along the exchange ray. -/
theorem singleton_of_negative_cell_exchange (A : Fin 4 → Point 4)
    (y : Point 4) (hy : ∀ j, lin (A j) y < 0)
    (p : Fin 4) (w : Point 4) (hp : 0 < lin (A p) w)
    (hother : ∀ j, j ≠ p → lin (A j) w ≤ 0) :
    ∃ x, SingletonCell A p x := by
  let t : ℝ := max 0 (-lin (A p) y / lin (A p) w) + 1
  have ht : 0 < t := by
    dsimp only [t]
    linarith only [le_max_left (0 : ℝ) (-lin (A p) y / lin (A p) w)]
  have hb : -lin (A p) y ≤
      max 0 (-lin (A p) y / lin (A p) w) * lin (A p) w :=
    (div_le_iff hp).mp (le_max_right _ _)
  refine ⟨y + t • w, ?_, ?_⟩
  · rw [lin_add_right, lin_smul_right]
    dsimp only [t]
    nlinarith only [hb, hp]
  · intro j hj
    rw [lin_add_right, lin_smul_right]
    have he := mul_nonpos_of_nonneg_of_nonpos ht.le (hother j hj)
    linarith only [hy j, he]

/-- Two nonroot indices whose circuit coefficients have the same sign
cannot occur in a mixed-sign circuit representation of Max4. -/
theorem no_mixed_circuit_with_same_sign_nonroots (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (hsum : ∀ j, ∑ i, A j i = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (c : Point 4) (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (r s : Fin 4) (hr : 0 < c r) (hs : c s < 0)
    (p q : Fin 4) (hpq : p ≠ q) (hp : c p ≠ 0) (hq : c q / c p > 0)
    (hpn : 3 ≤ (nonzeroCoordinates (A p)).card)
    (hqn : 3 ≤ (nonzeroCoordinates (A q)).card) : False := by
  obtain ⟨y, hy⟩ := mixed_circuit_negative_cell A c hrel hkernel r s hr hs
  obtain ⟨m, hm⟩ := negative_cell_readout A ell Phi h y hy
  rw [hm] at h
  let z : Point 4 := (c q / c p) • unitVec p - unitVec q
  have hzp : z p = c q / c p := by simp [z, unitVec, hpq, Ne.symm hpq]
  have hzq : z q = -1 := by simp [z, unitVec, hpq, Ne.symm hpq]
  have hzo : ∀ j, j ≠ p → j ≠ q → z j = 0 := by
    intro j hjp hjq
    simp [z, unitVec, hjp, hjq]
  have hz : ∑ j, c j * z j = 0 := by
    change lin c z = 0
    simp only [z, lin_sub_right, lin_smul_right, lin_unitVec, div_mul_cancel _ hp]
    ring
  have hc : c ≠ 0 := by intro he; exact hp (congr_fun he p)
  obtain ⟨w, hw⟩ := row_values_surjective_on_circuit A c hc hrel hkernel z hz
  have hwp : 0 < lin (A p) w := by rw [hw, hzp]; exact hq
  have hwq : lin (A q) w < 0 := by rw [hw, hzq]; norm_num
  have hwother : ∀ j, j ≠ p → j ≠ q → lin (A j) w = 0 := by
    intro j hjp hjq
    rw [hw, hzo j hjp hjq]
  obtain ⟨xp, hxp⟩ := singleton_of_negative_cell_exchange A y hy p w hwp (fun j hj => by
    by_cases hjq : j = q
    · simpa only [hjq] using hwq.le
    · exact (hwother j hj hjq).le)
  have hwqn : 0 < lin (A q) (-w) := by rw [lin_neg_right]; linarith only [hwq]
  obtain ⟨xq, hxq⟩ := singleton_of_negative_cell_exchange A y hy q (-w) hwqn (fun j hj => by
    rw [lin_neg_right]
    by_cases hjp : j = p
    · rw [hjp]; exact neg_nonpos.mpr hwp.le
    · rw [hwother j hjp hj]; norm_num)
  exact no_nonroot_exchange A m Phi h hph p q xp xq hxp hxq hpn hqn
    (hsum p) w hwp hwq hwother

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
