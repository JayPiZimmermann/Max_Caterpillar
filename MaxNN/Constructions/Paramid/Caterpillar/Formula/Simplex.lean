import MaxNN.Constructions.Paramid.Caterpillar.Formula.Values
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Facets.Simplex

/-! # The candidate in reduced simplex coordinates

The actual finite decorated-word sum belongs to the support-function span.
Permuting the simplex vertices changes the candidate by an explicitly known
linear summand. The top-dimensional identity for every arity is proved in
`Formula.Correctness`; the lower-dimensional corrections are compiled into
the network in `Construction`.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

noncomputable def simplexValues (y : Fin (r + 1) → ℝ) : Fin (r + 1 + 1) → ℝ :=
  fun a => dot (toR (vtx a)) y

theorem simplexValues_zero (y : Fin (r + 1) → ℝ) : simplexValues y 0 = 0 := by
  simp [simplexValues, toR, vtx_zero, dot]

theorem simplexValues_succ (y : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    simplexValues y i.succ = y i := by
  simp [simplexValues, toR, vtx_succ, dot, Pi.single_apply]

/-- The complete explicit candidate, before lower-dimensional corrections. -/
noncomputable def formula (r : ℕ) (y : Fin (r + 1) → ℝ) : ℝ :=
  valueFormula r (simplexValues y)

theorem formula_eq_sum (r : ℕ) : formula r = fun y =>
    ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S * caterpillarUnit (toR (vtx (π 0)))
        (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S y := rfl

theorem permutationUnit_mem_SSpan (π : Equiv.Perm (Fin (r + 1 + 1)))
    (S : Finset (Fin (r + 1))) :
    caterpillarUnit (toR (vtx (π 0)))
      (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S ∈ SSpan (r + 1) := by
  rw [caterpillarUnit_eq_dot_add_paramidOn _ _ S
    (edgeVecs_simplex_injective (fun i => π i.succ)
      (π.injective.comp (Fin.succ_injective (r + 1))) S)]
  exact Submodule.add_mem _ (GermAux.dot_mem_SSpan _) (paramidOn_mem_SSpan _ _)

theorem formula_mem_SSpan (r : ℕ) : formula r ∈ SSpan (r + 1) := by
  have h : (∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S • caterpillarUnit (toR (vtx (π 0)))
        (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S) ∈ SSpan (r + 1) :=
    Submodule.sum_mem _ fun π _ => Submodule.sum_mem _ fun S _ =>
      Submodule.smul_mem _ _ (permutationUnit_mem_SSpan π S)
  have he : formula r = ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
      wordWeight r S • caterpillarUnit (toR (vtx (π 0)))
        (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S := by
    rw [formula_eq_sum]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rwa [he]

theorem germDiff_formula_eq_sum (r : ℕ) (u : Fin (r + 1) → ℝ) :
    germDiff u (formula r) =
      ∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
        wordWeight r S • germDiff u (caterpillarUnit (toR (vtx (π 0)))
          (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S) := by
  let U := fun (π : Equiv.Perm (Fin (r + 1 + 1))) (S : Finset (Fin (r + 1))) =>
    caterpillarUnit (toR (vtx (π 0))) (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S
  have hw : ∀ π S, (fun y => wordWeight r S * U π S y) ∈ SSpan (r + 1) :=
    fun π S => Submodule.smul_mem _ _ (permutationUnit_mem_SSpan π S)
  have hs : ∀ π, (fun y => ∑ S in admissibleCuts r, wordWeight r S * U π S y)
      ∈ SSpan (r + 1) := by
    intro π
    have he : (fun y => ∑ S in admissibleCuts r, wordWeight r S * U π S y) =
        ∑ S in admissibleCuts r, (fun y => wordWeight r S * U π S y) := by
      funext y
      simp only [Finset.sum_apply]
    rw [he]
    exact Submodule.sum_mem (SSpan (r + 1))
      (fun S (_ : S ∈ admissibleCuts r) => hw π S)
  rw [formula_eq_sum, germDiff_sum _ (fun π _ => hs π)]
  funext y
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro π _
  rw [germDiff_sum _ (fun S _ => hw π S)]
  apply Finset.sum_congr rfl
  intro S _
  change germDiff u (wordWeight r S • U π S) y =
    (wordWeight r S • germDiff u (U π S)) y
  rw [germDiff_smul _ (permutationUnit_mem_SSpan π S)]

/-- Relabel the full vertex values and subtract the new value at vertex zero. -/
noncomputable def permutedInput (τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun i => simplexValues y (τ i.succ) - simplexValues y (τ 0)

theorem simplexValues_permutedInput (τ : Equiv.Perm (Fin (r + 1 + 1)))
    (y : Fin (r + 1) → ℝ) (a : Fin (r + 1 + 1)) :
    simplexValues (permutedInput τ y) a = simplexValues y (τ a) - simplexValues y (τ 0) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · rw [simplexValues_zero, sub_self]
  · rw [simplexValues_succ]
    rfl

theorem formula_permutedInput (τ : Equiv.Perm (Fin (r + 1 + 1))) (y : Fin (r + 1) → ℝ) :
    formula r (permutedInput τ y) = formula r y - totalWeight r * simplexValues y (τ 0) := by
  unfold formula
  have he : simplexValues (permutedInput τ y) =
      fun a => simplexValues y (τ a) + (-simplexValues y (τ 0)) := by
    funext a
    rw [simplexValues_permutedInput, sub_eq_add_neg]
  rw [he, valueFormula_add_const, valueFormula_permute]
  ring

end MaxNN.Caterpillar
