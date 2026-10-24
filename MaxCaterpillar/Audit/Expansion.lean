import MaxCaterpillar.Core
import MaxCaterpillar.Frontier.Basic

/-! # Nonvacuity: caterpillar expansions of the maximum exist

The lower bounds `caterpillar_expansion_choose_le`, `caterpillar_expansion_exponential` and
`caterpillar_expansion_quadratic` assume an expansion `IsCaterpillarExpansion r K`. This file
proves that such an expansion exists for every `N = r + 2`:

* `N ≥ 3`: the canonical expansion of `max_N` by the correction units and the auxiliary
  functions (`canonical_expansion`), merged along `normalizedKey`, uses `K = 𝒦₀`, the full
  set of normalized caterpillar face descriptions.
* `N = 2`: `max(x₀, x₁) = σ(x₁) - σ(-x₁) + σ(x₀ - x₁)` needs no caterpillar function.
-/

open BigOperators

namespace MaxCaterpillar
namespace Audit

open MaxNN MaxNN.Caterpillar Corrections MaxNN.Width

/-- `max₂` is a combination of the auxiliary functions. -/
theorem maximum_two_eq_auxiliary :
    ∃ a : Fin (W (0 + 1 + 1)) → ℝ, ∀ x : Point (0 + 1 + 1),
      Maximum (0 + 1 + 1) x = ∑ j, a j * auxiliaryFunction (0 + 1 + 1) j x := by
  classical
  have h01 : (0 : Fin 2) < 1 := by decide
  refine ⟨fun j => ((if j = posIdx (1 : Fin 2) then 1 else 0) -
      (if j = negIdx (1 : Fin 2) then 1 else 0)) +
      (if j = prIdx (prIdxOf (0 : Fin 2) 1 h01) then 1 else 0), fun x => ?_⟩
  have hmax : Maximum 2 x = max (x 0) (x 1) := by
    refine le_antisymm ((Frontier.Maximum_le_iff _ _).2 fun i => ?_)
      (max_le (Frontier.le_Maximum x 0) (Frontier.le_Maximum x 1))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hpair := pairMaxLin_feat x (0 : Fin 2) 1
  unfold pairMaxLin coordLin at hpair
  rw [dif_pos h01] at hpair
  show Maximum 2 x = _
  rw [hmax, ← hpair]
  simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- For `N ≥ 3`, the canonical expansion merged along `normalizedKey` is a caterpillar
expansion by all normalized descriptions. -/
theorem isCaterpillarExpansion_normalizedKeys (r : ℕ) (hr : 1 ≤ r) :
    IsCaterpillarExpansion r (caterpillarDescriptions r) := by
  classical
  refine ⟨Finset.Subset.refl _, ?_⟩
  set c := coefficient r
  let c' : RealKey (r + 1) → ℝ := fun q => if h : q ∈ correctionKeys r then c (Sum.inl ⟨q, h⟩)
    else 0
  let d : RealKey (r + 1) → ℝ := fun k =>
    ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k), c' q
  refine ⟨d, fun j => c (Sum.inr j), fun x => ?_⟩
  have hcan := canonical_expansion r hr x
  rw [Fintype.sum_sum_type] at hcan
  rw [← hcan]
  congr 1
  · -- the correction units, merged along `normalizedKey`
    have h1 : ∑ k : (↑(correctionKeys r) : Type), c (Sum.inl k) * atom r (Sum.inl k) x =
        ∑ q in correctionKeys r, c' q * realUnitY q x := by
      rw [← Finset.sum_coe_sort (correctionKeys r)]
      refine Finset.sum_congr rfl fun q _ => ?_
      show c (Sum.inl q) * realUnitY q.1 x = c' q.1 * realUnitY q.1 x
      simp only [c', dif_pos q.2]
    rw [h1]
    unfold caterpillarDescriptions caterpillarFunction
    simp only [d, Finset.sum_mul]
    symm
    calc ∑ k in normalizedKeys r,
          ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k), c' q * realUnitY k x
        = ∑ k in normalizedKeys r,
          ∑ q in (correctionKeys r).filter (fun q => normalizedKey q = k),
            c' q * realUnitY q x := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
          obtain ⟨hq, hqk⟩ := Finset.mem_filter.mp hq
          rw [← hqk, realUnitY_normalizedKey hq]
      _ = ∑ q in correctionKeys r, c' q * realUnitY q x :=
          Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩) _

/-- **Nonvacuity of the caterpillar lower bounds.** For every `N = r + 2` the maximum has a
caterpillar expansion. -/
theorem exists_isCaterpillarExpansion (r : ℕ) : ∃ K, IsCaterpillarExpansion r K := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨a, ha⟩ := maximum_two_eq_auxiliary
    exact ⟨∅, Finset.empty_subset _, fun _ => 0, a, fun x => by
      simp only [Finset.sum_empty, zero_add]; exact ha x⟩
  · exact ⟨_, isCaterpillarExpansion_normalizedKeys r hr⟩

end Audit
end MaxCaterpillar
