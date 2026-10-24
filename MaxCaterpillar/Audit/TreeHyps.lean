import MaxCaterpillar.Simplify.CoverageMain
import MaxCaterpillar.Audit.CaterpillarTree

/-! # Nonvacuity of the degree-type hypotheses of the tree lower bounds

The degree-type hypotheses `∀ u, F.hingeDeg u ≤ Δ` (`tree_bounded_choose_le`,
`tree_bounded_exponential`) and `OutLeafBound F.descr s` (`tree_outLeaf_choose_le`,
`tree_outLeaf_exponential`) hold for every tree face once `Δ = N` resp. `s = N`. Together
with `exists_isTreeExpansion` this makes those theorems nonvacuous for every `N`; the bounds
they give are strong only when an expansion with a bound independent of `N` exists.

For `tree_hub_exponential` and `tree_star_or_bounded_exponential` this trivial choice is not
available (they need `(144(2Δ-1)² + 1)·3 ≤ N`, so `N ≥ 10803` and `Δ` far below `N`); their
nonvacuity needs an expansion of `max_N` by trees satisfying `HubOK` for such `Δ`, which is
not established.
-/

open BigOperators Finset

namespace MaxCaterpillar
namespace Audit

open Trees

/-- Every hinge degree is at most `N`. -/
theorem hingeDeg_le_card {N : ℕ} (F : TreeFace N) (u : Fin N) : F.hingeDeg u ≤ N := by
  classical
  unfold TreeFace.hingeDeg
  exact (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])

/-- Every description satisfies the out-leaf bound with `s = N`. -/
theorem outLeafBound_card {N : ℕ} (D : CountLower.Descr N) : Simplify.OutLeafBound D N :=
  fun _ U _ => (Finset.card_le_univ U).trans (by rw [Fintype.card_fin])

/-- **Nonvacuity of `tree_bounded_*` and `tree_outLeaf_*`.** For every `N = r + 2` there is a
tree expansion of `max_N` (by caterpillar trees) all of whose faces satisfy the degree
hypotheses with `Δ = s = N`. -/
theorem exists_isTreeExpansion_bounded (r : ℕ) :
    ∃ K : Finset (TreeFace (r + 1 + 1)), IsTreeExpansion r K ∧
      (∀ F ∈ K, F.IsCaterpillar) ∧ (∀ F ∈ K, ∀ u, F.hingeDeg u ≤ r + 1 + 1) ∧
      ∀ F ∈ K, Simplify.OutLeafBound F.descr (r + 1 + 1) := by
  obtain ⟨K, hc, hK⟩ := exists_isTreeExpansion r
  exact ⟨K, hK, hc, fun F _ u => hingeDeg_le_card F u, fun F _ => outLeafBound_card _⟩

/-- Transfer a caterpillar expansion to a tree expansion whose faces satisfy any property `P`
that some tree face of each caterpillar function has (e.g. `IsCaterpillar`, or reduced
degree `≤ 2`). -/
theorem isTreeExpansion_of_pred (r : ℕ) (P : TreeFace (r + 1 + 1) → Prop)
    (hP : ∀ k ∈ caterpillarDescriptions r, ∃ F : TreeFace (r + 1 + 1), P F ∧
      caterpillarFunction k = F.unit) {K : Finset (FaceKey r)}
    (hK : IsCaterpillarExpansion r K) :
    ∃ K' : Finset (TreeFace (r + 1 + 1)), (∀ F ∈ K', P F) ∧ K'.card ≤ K.card ∧
      IsTreeExpansion r K' := by
  classical
  obtain ⟨hsub, d, a, h⟩ := hK
  have hT : ∀ k : K, ∃ F : TreeFace (r + 1 + 1), P F ∧
      caterpillarFunction k.1 = F.unit := fun k => hP k.1 (hsub k.2)
  choose T hTc hTu using hT
  refine ⟨K.attach.image T, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hF
    exact hTc k
  · exact Finset.card_image_le.trans (Finset.card_attach).le
  · refine ⟨fun F => ∑ k in K.attach.filter (fun k => T k = F), d k.1, a, fun x => ?_⟩
    rw [h x]
    congr 1
    simp only [Finset.sum_mul]
    rw [show ∑ k in K, d k * caterpillarFunction k x =
        ∑ k in K.attach, d k.1 * caterpillarFunction k.1 x from Finset.sum_attach.symm]
    symm
    calc ∑ F in K.attach.image T, ∑ k in K.attach.filter (fun k => T k = F), d k.1 * F.unit x
        = ∑ F in K.attach.image T, ∑ k in K.attach.filter (fun k => T k = F),
            d k.1 * caterpillarFunction k.1 x := by
          refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun k hk => ?_
          rw [← (Finset.mem_filter.1 hk).2, hTu k]
      _ = ∑ k in K.attach, d k.1 * caterpillarFunction k.1 x :=
          Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem T hk) _

end Audit
end MaxCaterpillar
