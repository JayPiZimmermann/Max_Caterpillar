import MaxNN.Constructions.Paramid.Caterpillar.Formula.Simplex
import MaxNN.Constructions.Paramid.Geom.SimplexMod

/-! # Completeness for the actual caterpillar candidate

The candidate is unconditionally a combination of full-dimensional simplex
support functions modulo lower-dimensional functions. Consequently its class
identity follows once all of its facet differences match those of the simplex.
The completeness bridge itself does not use induction on the dimension.
-/

open BigOperators

namespace MaxNN.ParamidGeom.KuhnRhoAux

theorem paramidUnit_mem_simplexMod_of_top_card {m k : ℕ}
    (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) (hm : k + 1 = m) :
    paramidUnit γ v ∈ simplexMod m := by
  classical
  by_cases h : LinearIndependent ℝ (Fin.snoc v γ)
  · exact paramidUnit_mem_simplexMod h hm
  · exact Submodule.mem_sup_right
      (paramidUnit_mem_LSpan_of_not_linearIndependent h hm)

theorem mem_LSpan_of_mem_simplexMod_of_flagFun_eq_zero {m : ℕ}
    (hm : 1 ≤ m) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ simplexMod m)
    (hflags : ∀ us : List (Fin m → ℝ), IsFlag us → flagFun us f = 0) :
    f ∈ LSpan m (m - 1) := by
  obtain ⟨g, hg, l, hl, hgl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨r, a, P, hP, hgP⟩ := exists_sum_of_mem_span_simplexFns hg
  refine mem_LSpan_of_flagFun_eq_zero_of_sub_mem hm
    (simplexMod_le_SSpan m hf) a P hP ?_ hflags
  rw [← hgP, sub_eq_of_eq_add' hgl.symm]
  exact hl

theorem mem_LSpan_of_mem_simplexMod_of_forall_germDiff_mem {m : ℕ}
    (hm : 2 ≤ m) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ simplexMod m)
    (hg : ∀ u, germDiff u f ∈ LSpan m (m - 2)) :
    f ∈ LSpan m (m - 1) := by
  apply mem_LSpan_of_mem_simplexMod_of_flagFun_eq_zero (by omega) hf
  intro us hus
  cases us with
  | nil => have := hus.1; simp only [List.length_nil] at this; omega
  | cons u us =>
    have hlen := hus.1
    simp only [List.length_cons] at hlen
    have hne : us ≠ [] := by
      intro he
      simp only [he, List.length_nil] at hlen
      omega
    rw [flagFun_cons u us hne]
    exact flagFun_eq_zero_of_mem_LSpan (hg u) us (by omega)

end MaxNN.ParamidGeom.KuhnRhoAux

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain ParamidGeom.KuhnRhoAux

theorem caterpillarUnit_mem_simplexMod {r : ℕ} (apex : Fin (r + 1) → ℝ)
    (A : Fin (r + 1) → Fin (r + 1) → ℝ) (S : Finset (Fin (r + 1))) :
    caterpillarUnit apex A S ∈ simplexMod (r + 1) := by
  rw [caterpillarUnit_eq_dot_add_paramidUnit]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right (FlagAux.dot_mem_LSpan apex _))
    (paramidUnit_mem_simplexMod_of_top_card _ _ rfl)

theorem formula_mem_simplexMod (r : ℕ) : formula r ∈ simplexMod (r + 1) := by
  classical
  have he : formula r = ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S • caterpillarUnit (toR (vtx (π 0)))
        (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S := by
    rw [formula_eq_sum]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact Submodule.sum_mem _ fun π _ => Submodule.sum_mem _ fun S _ =>
    Submodule.smul_mem _ _ (caterpillarUnit_mem_simplexMod _ _ S)

theorem formula_sub_simplex_mem_simplexMod (r : ℕ) :
    formula r - hS (simplexVerts (r + 1)) ∈ simplexMod (r + 1) :=
  Submodule.sub_mem _ (formula_mem_simplexMod r) (hS_simplexVerts_mem_simplexMod (r + 1))

/-- All directional facet identities suffice for the class identity of the
complete actual finite sum. No unknown correction function is a premise. -/
theorem formula_sub_simplex_mem_LSpan_of_germDiff {r : ℕ} (hr : 1 ≤ r)
    (hg : ∀ u, germDiff u (formula r - hS (simplexVerts (r + 1))) ∈
      LSpan (r + 1) (r - 1)) :
    formula r - hS (simplexVerts (r + 1)) ∈ LSpan (r + 1) r := by
  have h := mem_LSpan_of_mem_simplexMod_of_forall_germDiff_mem
    (m := r + 1) (by omega) (formula_sub_simplex_mem_simplexMod r)
    (by simpa only [Nat.add_sub_add_right] using hg)
  simpa only [Nat.add_sub_cancel] using h

end MaxNN.Caterpillar
