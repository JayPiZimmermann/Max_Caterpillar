import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Singleton
import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.CircuitImage

/-! # Excluding full positive circuits with two nonroot rows

These statements concern arbitrary real rows and arbitrary homogeneous
decoders. The relation and diagonal-kernel hypotheses describe an actual
rank-three positive circuit; singleton chambers are constructed, not assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

theorem positive_circuit_singleton (A : Fin 4 → Point 4) (c : Point 4)
    (hc : ∀ j, 0 < c j)
    (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (p : Fin 4) : ∃ x, SingletonCell A p x := by
  let S : ℝ := ∑ j in Finset.univ.erase p, c j
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro j _
      exact hc j
    · have he : (Finset.univ.erase p).card = 3 := by simp
      exact Finset.card_pos.mp (by omega)
  let z : Point 4 := fun j => if j = p then S / c p else -1
  have hzp : z p = S / c p := by simp [z]
  have hzo : ∀ j, j ≠ p → z j = -1 := by intro j hj; simp [z, hj]
  have hz : ∑ j, c j * z j = 0 := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => c j * z j) (Finset.mem_univ p)]
    have he : (∑ j in Finset.univ.erase p, c j * z j) = -S := by
      calc
        (∑ j in Finset.univ.erase p, c j * z j) =
            ∑ j in Finset.univ.erase p, -(c j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hzo j (Finset.ne_of_mem_erase hj), mul_neg_one]
        _ = -S := by rw [Finset.sum_neg_distrib]
    rw [he, hzp, mul_div_cancel' _ (hc p).ne']
    ring
  have hc0 : c ≠ 0 := by intro he; have := hc p; rw [he] at this; exact lt_irrefl 0 this
  obtain ⟨x, hx⟩ := row_values_surjective_on_circuit A c hc0 hrel hkernel z hz
  refine ⟨x, ?_, ?_⟩
  · rw [hx, hzp]
    exact div_pos hS (hc p)
  · intro j hj
    rw [hx, hzo j hj]
    norm_num

/-- Four rank-three invariant rows forming a full positive circuit cannot
represent Max4 when their omitted coordinates cover all inputs and at least
two rows are genuine nonroots. In particular this excludes the positive
full-circuit branches of both zero-root and one-root strata. -/
theorem no_positive_circuit_with_two_nonroots (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (hnorm : ∑ i, ell i = 1)
    (hsum : ∀ j, ∑ i, A j i = 0)
    (hcover : ∀ i, ∃ j, A j i = 0)
    (c : Point 4) (hc : ∀ j, 0 < c j)
    (hrel : ∀ x, ∑ j, c j * lin (A j) x = 0)
    (hkernel : ∀ x, (∀ j, lin (A j) x = 0) → ∃ t, x = diag t)
    (p q : Fin 4) (hpq : p ≠ q)
    (hp : 3 ≤ (nonzeroCoordinates (A p)).card)
    (hq : 3 ≤ (nonzeroCoordinates (A q)).card) : False := by
  have hsingle := positive_circuit_singleton A c hc hrel hkernel
  have hbinary : ∀ i, ell i = 0 ∨ ell i = 1 := by
    intro i
    obtain ⟨j, hj⟩ := hcover i
    obtain ⟨x, hx⟩ := hsingle j
    exact singleton_omission_binary A ell Phi h j x hx i hj
  obtain ⟨m, hm⟩ := readout_eq_unitVec_of_binary ell hbinary hnorm
  rw [hm] at h
  let z : Point 4 := c q • unitVec p - c p • unitVec q
  have hzp : z p = c q := by simp [z, unitVec, hpq, Ne.symm hpq]
  have hzq : z q = -c p := by simp [z, unitVec, hpq, Ne.symm hpq]
  have hzo : ∀ j, j ≠ p → j ≠ q → z j = 0 := by
    intro j hjp hjq
    simp [z, unitVec, hjp, hjq]
  have hz : ∑ j, c j * z j = 0 := by
    change lin c z = 0
    simp only [z, lin_sub_right, lin_smul_right, lin_unitVec]
    ring
  have hc0 : c ≠ 0 := by intro he; have := hc p; rw [he] at this; exact lt_irrefl 0 this
  obtain ⟨w, hw⟩ := row_values_surjective_on_circuit A c hc0 hrel hkernel z hz
  obtain ⟨xp, hxp⟩ := hsingle p
  obtain ⟨xq, hxq⟩ := hsingle q
  exact no_nonroot_exchange A m Phi h hph p q xp xq hxp hxq hp hq (hsum p) w
    (by rw [hw, hzp]; exact hc q)
    (by rw [hw, hzq]; exact neg_neg_of_pos (hc p))
    (fun j hjp hjq => by rw [hw, hzo j hjp hjq])

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
