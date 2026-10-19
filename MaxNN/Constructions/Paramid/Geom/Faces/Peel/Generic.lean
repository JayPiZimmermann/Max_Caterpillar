import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Common non-roots of linear functionals (helper of `Geom/Faces/Peel.lean`)

Two facts about an arbitrary real vector space `V` (no finiteness assumption):

* `exists_forall_apply_ne_zero`: finitely many nonzero linear functionals `V → ℝ` have a common
  non-root.  This is the module version of `ReconstructAux.exists_forall_ne_zero_of_ne_zero`
  (`Geom/Reconstruct/Facets.lean`, stated there for `ℝ^m`), with the same proof: add a multiple of
  a non-root of the next functional, avoiding finitely many bad multiples.
* `exists_forall_not_mem`: `V` is not the union of finitely many proper subspaces (each proper
  subspace lies in the kernel of a nonzero functional, `Submodule.exists_le_ker_of_lt_top`).

The peeling lemma applies the first fact on an annihilator subspace of `ℝ^m`
(`Faces/Peel/Annihilator.lean`).
-/

namespace MaxNN.ParamidGeom.Faces.PeelAux

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Common non-root.**  Finitely many nonzero linear functionals on a real vector space have a
common non-root. -/
theorem exists_forall_apply_ne_zero {κ : Type*} (s : Finset κ) (φ : κ → V →ₗ[ℝ] ℝ)
    (hφ : ∀ k ∈ s, φ k ≠ 0) : ∃ v : V, ∀ k ∈ s, φ k v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k hk => absurd hk (Finset.not_mem_empty k)⟩
  | @insert a s _ ih =>
    obtain ⟨v, hv⟩ := ih fun k hk => hφ k (Finset.mem_insert_of_mem hk)
    obtain ⟨u, hu⟩ : ∃ u, φ a u ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ a (Finset.mem_insert_self a s) (LinearMap.ext h)
    obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset
      ((insert a s).image fun k => -φ k v / φ k u)
    refine ⟨v + t • u, fun k hk => ?_⟩
    rw [map_add, map_smul, smul_eq_mul]
    intro h0
    by_cases hku : φ k u = 0
    · rw [hku, mul_zero, add_zero] at h0
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact hu hku
      · exact hv k hks h0
    · apply ht
      refine Finset.mem_image.mpr ⟨k, hk, ?_⟩
      field_simp
      linarith

/-- **No finite union of proper subspaces.**  A real vector space is not the union of finitely
many proper subspaces. -/
theorem exists_forall_not_mem {κ : Type*} (s : Finset κ) (W : κ → Submodule ℝ V)
    (hW : ∀ k ∈ s, W k ≠ ⊤) : ∃ v : V, ∀ k ∈ s, v ∉ W k := by
  have hf : ∀ k ∈ s, ∃ f : V →ₗ[ℝ] ℝ, f ≠ 0 ∧ W k ≤ LinearMap.ker f := fun k hk =>
    (W k).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr (hW k hk))
  choose! f hf0 hfW using hf
  obtain ⟨v, hv⟩ := exists_forall_apply_ne_zero s f hf0
  exact ⟨v, fun k hk hmem => hv k hk (LinearMap.mem_ker.mp (hfW k hk hmem))⟩

end MaxNN.ParamidGeom.Faces.PeelAux
