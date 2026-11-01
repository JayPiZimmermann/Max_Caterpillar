import MaxCaterpillar.Fiber.Separation
import MaxCaterpillar.Fiber.SymmetryHomeomorph

/-! # Transporting local separation proofs through the allowed symmetries

Interior membership is invariant under the genuine network symmetries.
Consequently, local openness at each normalized seed suffices for openness of
its full symmetry saturation. The local openness premise is not asserted here.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber

open Set

variable {N h₁ h₂ : ℕ} [NeZero N]

/-- The interior of an invariant set is invariant, because each allowed
generator acts by a homeomorphism on the full parameter fiber. -/
theorem symmetryInvariant_interior {S : Set (ExactFiber N h₁ h₂)}
    (hinv : SymmetryInvariant S) : SymmetryInvariant (interior S) := by
  apply symmetryInvariant_of_step
  intro x y hxy
  obtain ⟨e, he, hequiv⟩ := symmetryStep_homeomorph hxy
  have hpre : e ⁻¹' S = S := by
    ext z
    exact (hinv z (e z) (hequiv z)).symm
  have hint : e ⁻¹' interior S = interior S := by
    rw [e.preimage_interior, hpre]
  have hm : e x ∈ interior S ↔ x ∈ interior S := by
    change x ∈ e ⁻¹' interior S ↔ x ∈ interior S
    rw [hint]
  simpa only [he] using hm.symm

/-- A neighborhood proof at the normalized seeds extends to every point in
the symmetry-saturated sector. -/
theorem isOpen_symmetrySaturation_of_seed_interior
    (S : Set (ExactFiber N h₁ h₂))
    (hseed : ∀ x ∈ S, x ∈ interior (symmetrySaturation S)) :
    IsOpen (symmetrySaturation S) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := hx
  apply mem_interior_iff_mem_nhds.mp
  exact (symmetryInvariant_interior (symmetrySaturation_invariant S) a x hax).mp
    (hseed a ha)

namespace Mixed65

/-- Labeled mixed first rows with arbitrary positive row scales belong to the
actual sector; inverse rescaling normalizes the entire exact network. -/
theorem mem_sector_of_scaled_firstRows (net : ExactFiber 4 6 5)
    {t : ℝ} (ht : 0 < t) (c : Fin 6 → ℝ) (hc : ∀ j, 0 < c j)
    (hrows : ∀ j, net.val.W₁ j = c j • firstRows t j) : net ∈ sector := by
  let norm : ExactFiber 4 6 5 :=
    scaleFirstFiber (fun j => (c j)⁻¹) (fun j => inv_pos.mpr (hc j)) net
  have hnorm : norm ∈ seed := by
    refine ⟨t, ht, ?_⟩
    funext j i
    change (c j)⁻¹ * net.val.W₁ j i = firstRows t j i
    rw [hrows j]
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel (ne_of_gt (hc j)), one_mul]
  refine ⟨norm, hnorm, ?_⟩
  exact EqvGen.symm _ _ (EqvGen.rel _ _
    (SymmetryStep.first net (fun j => (c j)⁻¹) (fun j => inv_pos.mpr (hc j))))

/-- Pointwise openness at every normalized mixed first layer proves openness
of the full mixed sector, with suffix weights and biases unrestricted. -/
theorem sector_isOpen_of_seed_interior
    (hseed : ∀ net ∈ seed, net ∈ interior sector) : IsOpen sector :=
  isOpen_symmetrySaturation_of_seed_interior seed hseed

end Mixed65

end MaxCaterpillar.Fiber
