import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.WordEncoding
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.Reversal
import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Spine.ClosedCount

/-! # The full leaf-order and spine-reversal bound

Every normalized word key is carried by one of the canonical spine data.
For each spine length, reversal pairs distinct data with identical keys.
Summing these finite image bounds yields a closed count for the existing
normalized cone dictionary, without changing the construction coefficients.
-/

namespace MaxNN.Caterpillar.Corrections

open scoped BigOperators

theorem normalizedWordCones_subset_spineShapes (r : ℕ) :
    normalizedWordCones r ⊆
      (Finset.range r).biUnion (SpineData.shapeKeys (r + 1)) := by
  classical
  intro k hk
  unfold normalizedWordCones wordCones at hk
  rw [Finset.image_image] at hk
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hk
  apply Finset.mem_biUnion.mpr
  refine ⟨wordSpineLength w, Finset.mem_range.mpr (wordSpineLength_lt w), ?_⟩
  exact Finset.mem_image.mpr
    ⟨wordSpineData w, Finset.mem_univ _, (normalizedKey_wordKey_eq_shapeKey w).symm⟩

theorem card_normalizedWordCones_le_spine (r : ℕ) :
    (normalizedWordCones r).card ≤ spineConeBound (r + 1 + 1) := by
  classical
  calc
    _ ≤ ((Finset.range r).biUnion (SpineData.shapeKeys (r + 1))).card :=
      Finset.card_le_of_subset (normalizedWordCones_subset_spineShapes r)
    _ ≤ ∑ s in Finset.range r, (SpineData.shapeKeys (r + 1) s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ s in Finset.range r, spineConeTerm (r + 1 + 1) s := by
      apply Finset.sum_le_sum
      intro s _
      exact (SpineData.card_shapeKeys_le_half (r + 1) s).trans_eq
        (card_spineData_div_two (r + 1 + 1) s)
    _ = _ := by
      rw [spineConeBound, show r + 1 + 1 - 2 = r by omega]

end MaxNN.Caterpillar.Corrections
