import MaxNN.Constructions.Paramid.Geom.Defs
import MaxNN.PolyhedralGeometry.SupportCut

/-!
# Support functions see only the convex hull; one cut modulo lower dimension

Helper for `Geom/Kuhn.lean` (namespace `MaxNN.ParamidGeom.Kuhn`).

* `dot_le_hS_of_mem_convexHull`: a point of `conv T` pairs with `y` to at most `hS T y`.
* `hS_eq_of_convexHull_eq`: `hS S = hS T` whenever `conv S = conv T` (also for empty sets).
* `hS_cut_mem_LSpan`: for a nonzero normal `a`, `hS S − (hS S⁺ + hS S⁻) ∈ LSpan m (m − 1)`, where
  `S^± = upperPoints / lowerPoints S a c` are the generating sets of the two halves of `conv S`
  (`PolyhedralGeometry/SupportCut.lean`).  If the section `S⁰ ∪ M` is nonempty this is the cut
  identity `h_S + h_{S⁰ ∪ M} = h_{S⁺} + h_{S⁻}` with a section of dimension `≤ m − 1`; if it is
  empty, `S` lies strictly on one side and the identity is exact.
* `list_sum_sub_mem_LSpan`: termwise membership of differences passes to list sums.
-/

namespace MaxNN.ParamidGeom.Kuhn

open BigOperators MaxNN.SupportCut

variable {m : ℕ}

theorem hS_empty : hS (∅ : Finset (Fin m → ℝ)) = 0 := by
  funext y
  unfold hS
  rw [dif_neg (Finset.not_nonempty_empty)]
  rfl

/-- A point of the convex hull of `T` pairs with `y` to at most `hS T y`. -/
theorem dot_le_hS_of_mem_convexHull {T : Finset (Fin m → ℝ)} (hT : T.Nonempty)
    {x : Fin m → ℝ} (hx : x ∈ convexHull ℝ (T : Set (Fin m → ℝ))) (y : Fin m → ℝ) :
    dot x y ≤ hS T y := by
  have hsub : (T : Set (Fin m → ℝ)) ⊆ {z | dot y z ≤ hS T y} := by
    intro z hz
    show dot y z ≤ hS T y
    rw [dot_comm, hS_of_nonempty hT]
    exact Finset.le_sup' (fun p => dot p y) (Finset.mem_coe.mp hz)
  have hconv : Convex ℝ {z : Fin m → ℝ | dot y z ≤ hS T y} :=
    convex_halfspace_le (dotL y).isLinear (hS T y)
  have h := convexHull_min hsub hconv hx
  rw [dot_comm]
  exact h

/-- **`hS` depends only on the convex hull.** -/
theorem hS_eq_of_convexHull_eq {S T : Finset (Fin m → ℝ)}
    (h : convexHull ℝ (S : Set (Fin m → ℝ)) = convexHull ℝ (T : Set (Fin m → ℝ))) :
    hS S = hS T := by
  by_cases hS0 : S.Nonempty
  · have hT0 : T.Nonempty := by
      have hne : (convexHull ℝ (T : Set (Fin m → ℝ))).Nonempty := by
        rw [← h]
        exact convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hS0)
      exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne)
    funext y
    apply le_antisymm
    · rw [hS_of_nonempty hS0]
      refine Finset.sup'_le _ _ fun p hp => ?_
      have hp' : p ∈ convexHull ℝ (T : Set (Fin m → ℝ)) := by
        rw [← h]
        exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)
      exact dot_le_hS_of_mem_convexHull hT0 hp' y
    · rw [hS_of_nonempty hT0]
      refine Finset.sup'_le _ _ fun p hp => ?_
      have hp' : p ∈ convexHull ℝ (S : Set (Fin m → ℝ)) := by
        rw [h]
        exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)
      exact dot_le_hS_of_mem_convexHull hS0 hp' y
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS0
    have hT' : T = ∅ := by
      have hc : convexHull ℝ (T : Set (Fin m → ℝ)) = ∅ := by
        rw [← h, hS', Finset.coe_empty, convexHull_empty]
      exact Finset.coe_eq_empty.mp (convexHull_empty_iff.mp hc)
    rw [hS', hT']

/-- A nonempty point set whose affine span has dimension `≤ k` gives an element of `LSpan m k`. -/
theorem hS_mem_LSpan_of_finrank_le {S : Finset (Fin m → ℝ)} (hS0 : S.Nonempty) {k : ℕ}
    (hk : FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k) :
    hS S ∈ LSpan m k :=
  Submodule.subset_span ⟨S, hS0, hk, fun y => hS_of_nonempty hS0 y⟩

/-- **One cut, modulo lower dimension.**  For a nonzero normal `a`,
`hS S − (hS S⁺ + hS S⁻) ∈ LSpan m (m − 1)`. -/
theorem hS_cut_mem_LSpan (S : Finset (Fin m → ℝ)) {a : Fin m → ℝ} (ha : a ≠ 0) (c : ℝ) :
    hS S - (hS (upperPoints S a c) + hS (lowerPoints S a c)) ∈ LSpan m (m - 1) := by
  by_cases h0 : (sectionPoints S a c).Nonempty
  · have hmem : hS (sectionPoints S a c) ∈ LSpan m (m - 1) :=
      hS_mem_LSpan_of_finrank_le h0 (finrank_vectorSpan_sectionPoints_le S ha c)
    have heq : hS S - (hS (upperPoints S a c) + hS (lowerPoints S a c)) =
        -hS (sectionPoints S a c) := by
      funext y
      have hid := support_cut_identity S a c h0 y
      have e1 : hS S y = S.sup' (nonempty_of_nonempty_sectionPoints h0) (fun p => dot p y) :=
        hS_of_nonempty _ y
      have e2 : hS (sectionPoints S a c) y =
          (sectionPoints S a c).sup' h0 (fun p => dot p y) :=
        hS_of_nonempty _ y
      have e3 : hS (upperPoints S a c) y =
          (upperPoints S a c).sup' (nonempty_upperPoints h0) (fun p => dot p y) :=
        hS_of_nonempty _ y
      have e4 : hS (lowerPoints S a c) y =
          (lowerPoints S a c).sup' (nonempty_lowerPoints h0) (fun p => dot p y) :=
        hS_of_nonempty _ y
      show hS S y - (hS (upperPoints S a c) y + hS (lowerPoints S a c) y) =
        -hS (sectionPoints S a c) y
      rw [e1, e2, e3, e4]
      linarith
    rw [heq]
    exact Submodule.neg_mem _ hmem
  · have hzero : ∀ p ∈ S, level a c p ≠ 0 := fun p hp h =>
      h0 ⟨p, mem_sectionPoints_of_mem hp h⟩
    have hcross : ∀ p ∈ S, ∀ q ∈ S, 0 < level a c p → ¬ level a c q < 0 :=
      fun p hp q hq hpos hneg => h0 ⟨_, crossPoint_mem_sectionPoints hp hq hpos hneg⟩
    have hcp : crossPoints S a c = ∅ := by
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro x hx
      exact h0 ⟨x, crossPoints_subset_sectionPoints hx⟩
    have heq : hS S = hS (upperPoints S a c) + hS (lowerPoints S a c) := by
      by_cases hpos : ∃ p ∈ S, 0 < level a c p
      · obtain ⟨p, hp, hp0⟩ := hpos
        have hall : ∀ q ∈ S, 0 < level a c q := fun q hq =>
          lt_of_le_of_ne (not_lt.mp (hcross p hp q hq hp0)) (hzero q hq).symm
        have hU : upperPoints S a c = S := by
          unfold upperPoints upperSide
          rw [hcp, Finset.union_empty]
          exact Finset.filter_true_of_mem fun q hq => (hall q hq).le
        have hL : lowerPoints S a c = ∅ := by
          unfold lowerPoints lowerSide
          rw [hcp, Finset.union_empty]
          exact Finset.filter_false_of_mem fun q hq => not_le.mpr (hall q hq)
        rw [hU, hL, hS_empty, add_zero]
      · push_neg at hpos
        have hall : ∀ q ∈ S, level a c q < 0 := fun q hq =>
          lt_of_le_of_ne (hpos q hq) (hzero q hq)
        have hU : upperPoints S a c = ∅ := by
          unfold upperPoints upperSide
          rw [hcp, Finset.union_empty]
          exact Finset.filter_false_of_mem fun q hq => not_le.mpr (hall q hq)
        have hL : lowerPoints S a c = S := by
          unfold lowerPoints lowerSide
          rw [hcp, Finset.union_empty]
          exact Finset.filter_true_of_mem fun q hq => (hall q hq).le
        rw [hU, hL, hS_empty, zero_add]
    rw [heq, sub_self]
    exact Submodule.zero_mem _

/-- Termwise membership of differences in `LSpan m j` passes to list sums. -/
theorem list_sum_sub_mem_LSpan {β : Type*} {j : ℕ} (L : List β)
    (f g : β → (Fin m → ℝ) → ℝ) (h : ∀ x ∈ L, f x - g x ∈ LSpan m j) :
    (L.map f).sum - (L.map g).sum ∈ LSpan m j := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self x L)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have e : f x + (L.map f).sum - (g x + (L.map g).sum) =
        (f x - g x) + ((L.map f).sum - (L.map g).sum) := by abel
    rw [e]
    exact add_mem h1 h2

end MaxNN.ParamidGeom.Kuhn
