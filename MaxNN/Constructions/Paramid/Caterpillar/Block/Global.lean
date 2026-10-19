import MaxNN.Constructions.Paramid.Caterpillar.Geometry.Toggle
import MaxNN.Constructions.Paramid.Caterpillar.Geometry.BlockRemainder
import MaxNN.Constructions.Paramid.Caterpillar.Block.Levels
import MaxNN.Constructions.Paramid.Caterpillar.Block.Pairing

/-! # Global cancellation when no vertex level is a singleton

The actual factorial-weighted sum is paired directly on its original index
set. The proof includes all terms: the inactive terms belong individually to
the lower-dimensional span, while the active terms cancel in pairs modulo it.
-/

open BigOperators

namespace MaxNN.Caterpillar

open ParamidGeom ParamidChain

variable {r : ℕ}

theorem germDiff_blockUnit_mem_LSpan_of_inactive (hr : 2 ≤ r)
    (u : Fin (r + 1) → ℝ) (hu : u ≠ 0) (hx : RepeatedValues (simplexValues u))
    (q : BlockIndex r) (hp : ¬ ActivePrefix (simplexValues u) q)
    (hs : ¬ ActiveSuffix (simplexValues u) q) :
    germDiff u (blockUnit q) ∈ LSpan (r + 1) (r - 1) := by
  have ha := repeatedValues_base_has_apex (simplexValues u) hx q.1
  have ho := simplex_base_has_other u hu q.1
  have hrep := repeatedValues_base_other_repeated (simplexValues u) hx q.1
  rcases germDiff_mem_LSpan_or_split hr (toR (vtx (q.1 0)))
      (fun i : Fin (r + 1) => toR (vtx (q.1 i.succ))) q.2.1
      (edgeVecs_simplex_injective (fun i => q.1 i.succ)
        (q.1.injective.comp (Fin.succ_injective (r + 1))) q.2.1) u ha ho hrep
    with hsmall | ⟨j, hj, hsplit, hroot | hlast⟩
  · exact hsmall
  · apply False.elim
    apply hs
    have hne : blockWordValues (simplexValues u) q j.succ ≠ blockApexValue (simplexValues u) q :=
      fun he => hsplit.1 (hroot.symm.trans he.symm)
    exact ⟨j, hsplit.suffix_has_two (hrep j.succ hne), hj, hsplit, hroot⟩
  · apply False.elim
    apply hp
    have hne : blockWordValues (simplexValues u) q 0 ≠ blockApexValue (simplexValues u) q :=
      fun he => hsplit.1 (he.trans hlast)
    exact ⟨j, hsplit.prefix_has_two (hrep 0 hne), hj, hsplit, hlast⟩

theorem germDiff_formula_eq_index_sum (u : Fin (r + 1) → ℝ) :
    germDiff u (formula r) =
      ∑ q : BlockIndex r, wordWeight r q.2.1 • germDiff u (blockUnit q) := by
  classical
  rw [germDiff_formula_eq_sum]
  change (∑ π : Equiv.Perm (Fin (r + 1 + 1)), ∑ S in admissibleCuts r,
    wordWeight r S • germDiff u (caterpillarUnit (toR (vtx (π 0)))
      (fun i : Fin (r + 1) => toR (vtx (π i.succ))) S)) = _
  simp only [BlockIndex, Fintype.sum_prod_type, blockUnit]
  apply Finset.sum_congr rfl
  intro π _
  exact Finset.sum_subtype (admissibleCuts r) (fun _ => Iff.rfl) _

/-- For every arity `N=r+2 >= 4`, all full simplex directions in which every
value is repeated have lower-order facet data for the complete candidate.
In particular, this closes every noncoordinate two-level block direction. -/
theorem germDiff_formula_mem_LSpan_of_repeatedValues (hr : 2 ≤ r)
    (u : Fin (r + 1) → ℝ) (hx : RepeatedValues (simplexValues u)) :
    germDiff u (formula r) ∈ LSpan (r + 1) (r - 1) := by
  classical
  by_cases hu : u = 0
  · rw [hu, germDiff_eq_sub, neg_zero, sub_self]
    exact Submodule.zero_mem _
  · rw [germDiff_formula_eq_index_sum]
    apply sum_mem_of_involutive_pair (LSpan (r + 1) (r - 1))
      (fun q : BlockIndex r => wordWeight r q.2.1 • germDiff u (blockUnit q))
      (blockTransform (simplexValues u)) (blockTransform_involutive (simplexValues u))
    intro q
    by_cases hp : ActivePrefix (simplexValues u) q
    · rw [wordWeight_blockTransform_prefix _ _ hp, neg_smul, ← sub_eq_add_neg, ← smul_sub]
      exact Submodule.smul_mem _ _ (DoublingAux.LSpan_mono
        (Nat.le_sub_of_add_le (show 1 + 1 ≤ r from hr))
        (germDiff_blockUnit_sub_transform_mem_LSpan_one_of_prefix u q hp))
    · by_cases hs : ActiveSuffix (simplexValues u) q
      · rw [wordWeight_blockTransform_suffix _ _ hs, neg_smul, ← sub_eq_add_neg, ← smul_sub]
        exact Submodule.smul_mem _ _ (DoublingAux.LSpan_mono
          (Nat.le_sub_of_add_le (show 1 + 1 ≤ r from hr))
          (germDiff_blockUnit_sub_transform_mem_LSpan_one_of_suffix u q hs))
      · rw [blockTransform_eq_self _ _ hp hs]
        have h := Submodule.smul_mem (LSpan (r + 1) (r - 1)) (wordWeight r q.2.1)
          (germDiff_blockUnit_mem_LSpan_of_inactive hr u hu hx q hp hs)
        exact Submodule.add_mem _ h h

end MaxNN.Caterpillar
