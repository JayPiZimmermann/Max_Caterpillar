import MaxCaterpillar.Fiber.First65.ActiveSpan
import MaxCaterpillar.Fiber.First65.TwoRootGeometry

/-! # Singleton cells in a first-feature representation of Max4

The decoder is arbitrary. These are information-loss arguments, so they
apply in particular to every finite second hidden width.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A strict singleton cell has exactly one potentially informative row. -/
def SingletonCell (A : ι → Point 4) (p : ι) (x : Point 4) : Prop :=
  0 < lin (A p) x ∧ ∀ j, j ≠ p → lin (A j) x < 0

/-- The factorization itself forces the common linear row kernel to be
diagonal: all four coordinates maximize at the origin. -/
theorem factorization_kernel_diagonal (A : ι → Point 4) (ell : Point 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (w : Point 4) (hw : ∀ j, lin (A j) w = 0) : ∃ t, w = diag t := by
  refine ⟨lin ell w, funext fun i => ?_⟩
  exact active_kernel_top_coordinate A ell Phi h 0 w (fun j _ => hw j) i
    (by simp only [Pi.zero_apply, Maximum_zero])

/-- Translation-invariant rows force the explicit linear readout to have
diagonal slope one, directly from the represented maximum. -/
theorem factorization_readout_normalized (A : ι → Point 4) (ell : Point 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hsum : ∀ j, ∑ i, A j i = 0) : ∑ i, ell i = 1 := by
  have hz : Phi 0 = 0 := by
    have he := h 0
    simpa only [Maximum_zero, lin_zero_right, relu_of_nonpos (le_refl (0 : ℝ)),
      zero_add] using he.symm
  have hs : (fun j => relu (lin (A j) (diag 1))) = 0 := by
    funext j
    rw [lin_diag, hsum j, mul_zero, relu_of_nonpos (le_refl (0 : ℝ))]
    rfl
  have he := h (diag 1)
  rw [Maximum_diag, hs, hz, add_zero, lin_diag, one_mul] at he
  exact he.symm

theorem singleton_kernel_top_coordinate (A : ι → Point 4) (ell : Point 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (p : ι) (x w : Point 4) (hx : SingletonCell A p x)
    (hw : lin (A p) w = 0) (k : Fin 4) (hk : x k = Maximum 4 x) :
    w k = lin ell w := by
  apply active_kernel_top_coordinate A ell Phi h x w _ k hk
  intro j hj
  by_cases hjp : j = p
  · simpa only [hjp] using hw
  · exact False.elim (not_lt_of_ge hj (hx.2 j hjp))

/-- At an omitted coordinate, a singleton cell forces the linear readout
coefficient to be either zero or one. -/
theorem singleton_omission_binary (A : ι → Point 4) (ell : Point 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (p : ι) (x : Point 4) (hx : SingletonCell A p x)
    (i : Fin 4) (hi : A p i = 0) : ell i = 0 ∨ ell i = 1 := by
  obtain ⟨k, hk'⟩ := exists_eq_Maximum x
  have hk := hk'.symm
  have he := singleton_kernel_top_coordinate A ell Phi h p x (unitVec i) hx
    (by simpa only [lin_unitVec] using hi) k hk
  rw [lin_unitVec] at he
  by_cases hki : k = i
  · right
    simpa only [unitVec_apply, if_pos hki] using he.symm
  · left
    simpa only [unitVec_apply, if_neg hki] using he.symm

/-- Binary coordinates and diagonal normalization make the readout a
coordinate projection. -/
theorem readout_eq_unitVec_of_binary (ell : Point 4)
    (hbinary : ∀ i, ell i = 0 ∨ ell i = 1)
    (hsum : ∑ i, ell i = 1) : ∃ m, ell = unitVec m := by
  have hex : ∃ m, ell m = 1 := by
    by_contra hn
    push_neg at hn
    have hz : ∀ i, ell i = 0 := fun i => (hbinary i).resolve_right (hn i)
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, funext fun i => ?_⟩
  by_cases him : i = m
  · simpa only [him, unitVec_apply, if_pos rfl] using hm
  · have hi : ell i = 0 := by
      rcases hbinary i with hi | hi
      · exact hi
      · have hnonneg : ∀ j, 0 ≤ ell j := by
          intro j
          rcases hbinary j with hj | hj <;> rw [hj] <;> norm_num
        have hpair : ∑ j in ({i, m} : Finset (Fin 4)), ell j ≤ ∑ j, ell j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hnonneg j)
        rw [Finset.sum_pair him, hi, hm, hsum] at hpair
        norm_num at hpair
    simpa only [unitVec_apply, if_neg him] using hi

/-- If the explicit readout is a coordinate projection, any singleton
cell with a different winner forces its active row to be a root. -/
theorem singleton_row_support_pair (A : ι → Point 4) (m : Fin 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin (unitVec m) x + Phi (fun j => relu (lin (A j) x)))
    (p : ι) (x : Point 4) (hx : SingletonCell A p x)
    (k : Fin 4) (hk : x k = Maximum 4 x) (hkm : k ≠ m) :
    nonzeroCoordinates (A p) ⊆ {k, m} := by
  intro i hi
  by_contra hin
  have hik : i ≠ k := by intro he; apply hin; simp [he]
  have him : i ≠ m := by intro he; apply hin; simp [he]
  let w : Point 4 := A p i • unitVec k - A p k • unitVec i
  have hw : lin (A p) w = 0 := by
    simp only [w, lin_sub_right, lin_smul_right, lin_unitVec]
    ring
  have he := singleton_kernel_top_coordinate A (unitVec m) Phi h p x w hx hw k hk
  have hlin : lin (unitVec m) w = w m := by
    simp [lin, unitVec, Finset.sum_ite_eq']
  rw [hlin] at he
  have hz : A p i = 0 := by
    simpa [w, unitVec, hkm, Ne.symm hkm, Ne.symm hik, Ne.symm him] using he
  exact (mem_nonzeroCoordinates (A p) i).mp hi hz

/-- A genuine nonroot singleton cell has the readout coordinate as its winner. -/
theorem singleton_nonroot_winner (A : ι → Point 4) (m : Fin 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin (unitVec m) x + Phi (fun j => relu (lin (A j) x)))
    (p : ι) (x : Point 4) (hx : SingletonCell A p x)
    (hnonroot : 3 ≤ (nonzeroCoordinates (A p)).card) :
    x m = Maximum 4 x := by
  obtain ⟨k, hk'⟩ := exists_eq_Maximum x
  have hk := hk'.symm
  by_cases hkm : k = m
  · simpa only [hkm] using hk
  · have hs := singleton_row_support_pair A m Phi h p x hx k hk hkm
    have hc := Finset.card_le_of_subset hs
    have hcard : ({k, m} : Finset (Fin 4)).card = 2 := by simp [hkm]
    rw [hcard] at hc
    omega

/-- The unit state on a specified feature axis. -/
def axis (p : ι) : ι → ℝ := fun j => if j = p then 1 else 0

theorem state_on_axis (A : ι → Point 4) (p : ι) (x : Point 4)
    (hp : 0 < lin (A p) x) (hother : ∀ j, j ≠ p → lin (A j) x ≤ 0) :
    (fun j => relu (lin (A j) x)) = lin (A p) x • axis p := by
  funext j
  by_cases hjp : j = p
  · simp [hjp, axis, relu_of_nonneg hp.le]
  · simp [axis, hjp, relu_of_nonpos (hother j hjp)]

/-- A nonroot singleton cell forces the homogeneous decoder to vanish on
the whole positive axis of that feature. -/
theorem decoder_axis_zero_of_nonroot_singleton (A : ι → Point 4) (m : Fin 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin (unitVec m) x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (p : ι) (x : Point 4) (hx : SingletonCell A p x)
    (hnonroot : 3 ≤ (nonzeroCoordinates (A p)).card) : Phi (axis p) = 0 := by
  have hw := singleton_nonroot_winner A m Phi h p x hx hnonroot
  have he := h x
  rw [state_on_axis A p x hx.1 (fun j hj => (hx.2 j hj).le),
    hph _ _ hx.1] at he
  have hlin : lin (unitVec m) x = x m := by simp [lin, unitVec]
  rw [hlin, ← hw] at he
  exact (mul_eq_zero.mp (show lin (A p) x * Phi (axis p) = 0 by linarith)).resolve_left
    hx.1.ne'

/-- Once two nonroot axes have been forced to zero, an exchange vector
with those two opposite active states is impossible. -/
theorem no_nonroot_exchange (A : ι → Point 4) (m : Fin 4)
    (Phi : (ι → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin (unitVec m) x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (p q : ι)
    (xp xq : Point 4) (hxp : SingletonCell A p xp) (hxq : SingletonCell A q xq)
    (hp : 3 ≤ (nonzeroCoordinates (A p)).card)
    (hq : 3 ≤ (nonzeroCoordinates (A q)).card)
    (hsum : ∑ i, A p i = 0)
    (w : Point 4) (hwp : 0 < lin (A p) w) (hwq : lin (A q) w < 0)
    (hother : ∀ j, j ≠ p → j ≠ q → lin (A j) w = 0) : False := by
  have hP := decoder_axis_zero_of_nonroot_singleton A m Phi h hph p xp hxp hp
  have hQ := decoder_axis_zero_of_nonroot_singleton A m Phi h hph q xq hxq hq
  have hpos : Maximum 4 w = w m := by
    rw [h w, state_on_axis A p w hwp (fun j hj => by
      by_cases hjq : j = q
      · simpa only [hjq] using hwq.le
      · exact (hother j hj hjq).le), hph _ _ hwp, hP, mul_zero, add_zero]
    simp [lin, unitVec]
  have hneg : Maximum 4 (-w) = -w m := by
    have hwq' : 0 < lin (A q) (-w) := by rw [lin_neg_right]; linarith only [hwq]
    rw [h (-w), state_on_axis A q (-w) hwq' (fun j hj => by
      rw [lin_neg_right]
      by_cases hjp : j = p
      · rw [hjp]
        exact neg_nonpos.mpr hwp.le
      · rw [hother j hjp hj]
        norm_num), hph _ _ hwq', hQ, mul_zero, add_zero]
    simp [lin, unitVec]
  have hdiag : w = diag (w m) := by
    funext i
    apply le_antisymm
    · exact (le_Maximum w i).trans_eq hpos
    · have he := (le_Maximum (-w) i).trans_eq hneg
      exact neg_le_neg_iff.mp he
  have hz : lin (A p) w = 0 := by rw [hdiag, lin_diag, hsum, mul_zero]
  exact hwp.ne' hz

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
