import MaxNN.Constructions.Paramid.Caterpillar.Block.Global
import MaxNN.Constructions.Paramid.Caterpillar.Formula.CoordinateDirections
import MaxNN.Constructions.Paramid.Caterpillar.Formula.SimplexGerms
import MaxNN.Constructions.Paramid.Caterpillar.Formula.Lift
import MaxNN.Constructions.Paramid.Caterpillar.Coordinate.Base

/-! # Assembly of the global facet proof

All noncoordinate directions are discharged here. The assembly step takes
the canonical coordinate recurrence for the actual finite formula, proved
in `Coordinate.Recurrence` and supplied in `Formula.Correctness`.
-/

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

theorem coordinateDirection_eq_neg_nu (a : Fin (r + 1 + 1)) :
    coordinateDirection a = -ParamidGeom.nu a := by
  funext i
  have h := SimplexFacetAux.dot_nu_toR_vtx a i.succ
  rw [SimplexFacetAux.dot_toR_vtx_succ] at h
  change (if i.succ = a then (1 : ℝ) else 0) -
    (if (0 : Fin (r + 1 + 1)) = a then 1 else 0) = -(ParamidGeom.nu a i)
  rw [h]
  have hz : (if (0 : Fin (r + 1 + 1)) = a then (1 : ℝ) else 0) =
      (if a = 0 then 1 else 0) := by simp only [eq_comm]
  rw [hz]
  ring

/-- The canonical coordinate direction is the only required facet datum
once block cancellation and vertex-permutation symmetry are used. -/
theorem germDiff_coordinateResidual_mem_LSpan_of_canonical (hr : 2 ≤ r)
    (hcanonical : germDiff (fun _ : Fin (r + 1) => (1 : ℝ))
      (coordinateResidual r) ∈ LSpan (r + 1) (r - 1))
    (u : Fin (r + 1) → ℝ) :
    germDiff u (coordinateResidual r) ∈ LSpan (r + 1) (r - 1) := by
  classical
  by_cases hcoord : ∃ a : Fin (r + 1 + 1), ∃ t : ℝ, u = t • coordinateDirection a
  · obtain ⟨a, t, rfl⟩ := hcoord
    exact germDiff_coordinateResidual_smul_coordinate_mem_LSpan a t hcanonical
  · have hf : germDiff u (formula r) ∈ LSpan (r + 1) (r - 1) := by
      by_cases hb : BlockDirection u
      · rcases repeatedValues_or_smul_coordinateDirection u hb with hrep | hc
        · exact germDiff_formula_mem_LSpan_of_repeatedValues hr u hrep
        · exact False.elim (hcoord hc)
      · exact germDiff_formula_mem_LSpan_of_not_blockDirection hr u hb
    have hs : germDiff u (hS (simplexVerts (r + 1))) ∈ LSpan (r + 1) (r - 1) := by
      apply germDiff_hS_simplexVerts_mem_LSpan_of_forall_ne_smul_nu hr u
      intro a c he
      apply hcoord
      refine ⟨a, -c, ?_⟩
      rw [coordinateDirection_eq_neg_nu, smul_neg, neg_smul, neg_neg]
      exact he
    unfold coordinateResidual
    rw [germDiff_sub (formula_mem_SSpan r)
      (GermAux.hS_mem_SSpan (SimplexFacetAux.simplexVerts_nonempty (r + 1)))]
    exact Submodule.sub_mem _ hf hs

theorem formula_sub_simplex_mem_LSpan_of_canonical (hr : 2 ≤ r)
    (hcanonical : germDiff (fun _ : Fin (r + 1) => (1 : ℝ))
      (formula r - hS (simplexVerts (r + 1))) ∈ LSpan (r + 1) (r - 1)) :
    formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r :=
  formula_sub_simplex_mem_LSpan_of_germDiff (by omega)
    (germDiff_coordinateResidual_mem_LSpan_of_canonical hr hcanonical)

theorem formula_sub_simplex_mem_LSpan_succ_of_recurrence {s : ℕ} (hs : 1 ≤ s)
    (hlower : formula s - hS (simplexVerts (s + 1)) ∈ LSpan (s + 1) s)
    (hrec : germDiff (fun _ : Fin (s + 1 + 1) => (1 : ℝ)) (formula (s + 1)) -
      valueFormula s ∈ LSpan (s + 1 + 1) s) :
    formula (s + 1) - hS (simplexVerts (s + 1 + 1)) ∈ LSpan (s + 1 + 1) (s + 1) := by
  apply formula_sub_simplex_mem_LSpan_of_canonical (by omega)
  rw [germDiff_sub (formula_mem_SSpan (s + 1))
    (GermAux.hS_mem_SSpan (SimplexFacetAux.simplexVerts_nonempty (s + 1 + 1))),
    germDiff_hS_simplexVerts_one]
  have h := Submodule.add_mem _ hrec (valueFormula_sub_MAX_mem_LSpan hlower)
  simpa only [sub_add_sub_cancel, Nat.add_sub_cancel] using h

end MaxNN.Caterpillar
