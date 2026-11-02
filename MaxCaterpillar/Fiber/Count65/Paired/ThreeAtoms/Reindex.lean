import MaxCaterpillar.Fiber.Count65.Paired.ThreeAtoms.Normalization
import MaxCaterpillar.Fiber.Count65.Paired.SecondReindex.Prefix

/-! Embed the extracted three atoms into the actual five physical slots. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired

/-- Any extracted ordering of three distinct physical slots extends to a
genuine second-hidden-layer permutation, retaining two spectator slots. -/
theorem three_atom_physical_permutation (net : Network 4 6 5)
    (e : Fin 3 ≃ NetworkAtoms net) :
    ∃ q : Equiv.Perm (Fin 5), ∀ i : Fin 3, q (Fin.castAdd 2 i) = (e i).val := by
  exact extend_second_prefix (fun i : Fin 3 => (e i).val)
    (fun _ _ hh => e.injective (Subtype.ext hh))

theorem three_atom_reindexed_outputs (net : Network 4 6 5)
    (e : Fin 3 ≃ NetworkAtoms net)
    (hj : ∀ i, networkAtomJump net (e i) = (![1,1,-1] : Fin 3 → ℝ) i) :
    ∃ q : Equiv.Perm (Fin 5),
      (∀ i : Fin 3, q (Fin.castAdd 2 i) = (e i).val) ∧
      ∀ i : Fin 3,
        (permuteHidden (normalizedAtomNetwork net) (Equiv.refl _) q).w₃ (Fin.castAdd 2 i) =
          (![1,1,-1] : Fin 3 → ℝ) i := by
  obtain ⟨q,hq⟩ := three_atom_physical_permutation net e
  refine ⟨q,hq,?_⟩
  intro i
  change (normalizedAtomNetwork net).w₃ (q (Fin.castAdd 2 i)) = _
  rw [hq,normalizedAtomNetwork_output,hj]

end MaxCaterpillar.Fiber.Count65.Paired
