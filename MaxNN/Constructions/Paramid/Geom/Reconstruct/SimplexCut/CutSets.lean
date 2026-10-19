import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut.Bary

/-!
# Cutting an indexed point set through all but two of its points
(helper for `Geom/Reconstruct/SimplexCut.lean`)

Let `p : ι → ℝ^N`, `s` a finite index set, and `H = {⟨a, ·⟩ = c}` a hyperplane containing every
`p i` (`i ∈ s`) except `p j` (strictly above) and `p k` (strictly below).  Then the point sets of
the cut identity (`PolyhedralGeometry/SupportCut.lean`) are explicit (`cutSets_of_two`): with
`q` the crossing point of the segment `[p j, p k]`,

* `sectionPoints (s.image p) a c = insert q (((s.erase j).erase k).image p)`,
* `upperPoints (s.image p) a c = s.image (update p k q)` (the vertex `p k` is replaced by `q`),
* `lowerPoints (s.image p) a c = s.image (update p j q)`.

Also: the cut identity in `hS` form (`hS_add_hS_sectionPoints`), membership of a support function
in `LSpan` from a dimension bound (`hS_mem_LSpan_of_finrank_le`), and the dimension bound for a
point set `insert q ((T.erase k).image p)` (`finrank_vectorSpan_insert_image_le`).

Everything here lives in the sub-namespace `MaxNN.ParamidGeom.SimplexCut`.
-/

namespace MaxNN.ParamidGeom

namespace SimplexCut

open BigOperators MaxNN.SupportCut

noncomputable section

variable {N : ℕ} {ι : Type*} [DecidableEq ι]

/-- The crossing point does not depend on the order of the two points. -/
theorem crossPoint_comm (a : Fin N → ℝ) (c : ℝ) (x y : Fin N → ℝ) :
    crossPoint a c x y = crossPoint a c y x := by
  unfold crossPoint
  rw [show level a c y - level a c x = -(level a c x - level a c y) by ring, inv_neg, neg_smul,
    ← smul_neg, neg_sub]

/-- Replacing the value at an index `k ∈ s` by `q` replaces the point `p k` of `s.image p` by
`q`. -/
theorem image_update_eq_insert {E : Type*} [DecidableEq E] (p : ι → E) {s : Finset ι} {k : ι}
    (hk : k ∈ s) (q : E) :
    s.image (Function.update p k q) = insert q ((s.erase k).image p) := by
  conv_lhs => rw [← Finset.insert_erase hk]
  rw [Finset.image_insert, Function.update_same]
  congr 1
  exact Finset.image_congr fun i hi => Function.update_noteq (Finset.ne_of_mem_erase hi) _ _

/-- **The cut through all but two points.**  If `p i` lies on `H = {⟨a, ·⟩ = c}` for every
`i ∈ s` other than `j` and `k`, with `p j` strictly above and `p k` strictly below `H`, then the
section, the upper half and the lower half of `s.image p` are `insert q` of the points on `H`,
`s.image (update p k q)` and `s.image (update p j q)`, for `q` the crossing point of
`[p j, p k]`. -/
theorem cutSets_of_two (p : ι → Fin N → ℝ) (s : Finset ι) (a : Fin N → ℝ) (c : ℝ) {j k : ι}
    (hj : j ∈ s) (hk : k ∈ s) (hpos : 0 < level a c (p j)) (hneg : level a c (p k) < 0)
    (hzero : ∀ i ∈ s, i ≠ j → i ≠ k → level a c (p i) = 0) :
    sectionPoints (s.image p) a c =
        insert (crossPoint a c (p j) (p k)) (((s.erase j).erase k).image p) ∧
      upperPoints (s.image p) a c = s.image (Function.update p k (crossPoint a c (p j) (p k))) ∧
      lowerPoints (s.image p) a c =
        s.image (Function.update p j (crossPoint a c (p j) (p k))) := by
  have hpos' : ∀ i ∈ s, 0 < level a c (p i) → i = j := by
    intro i hi h
    by_contra hij
    by_cases hik : i = k
    · rw [hik] at h
      linarith
    · rw [hzero i hi hij hik] at h
      exact lt_irrefl 0 h
  have hneg' : ∀ i ∈ s, level a c (p i) < 0 → i = k := by
    intro i hi h
    by_contra hik
    by_cases hij : i = j
    · rw [hij] at h
      linarith
    · rw [hzero i hi hij hik] at h
      exact lt_irrefl 0 h
  have hP : (s.image p).filter (fun x => 0 < level a c x) = {p j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      rw [hpos' i hi h]
    · rintro rfl
      exact ⟨⟨j, hj, rfl⟩, hpos⟩
  have hQ : (s.image p).filter (fun x => level a c x < 0) = {p k} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      rw [hneg' i hi h]
    · rintro rfl
      exact ⟨⟨k, hk, rfl⟩, hneg⟩
  have hM : crossPoints (s.image p) a c = {crossPoint a c (p j) (p k)} := by
    unfold crossPoints
    rw [hP, hQ, Finset.singleton_product_singleton, Finset.image_singleton]
  have hZ : zeroSide (s.image p) a c = ((s.erase j).erase k).image p := by
    ext x
    simp only [zeroSide, Finset.mem_filter, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      refine ⟨i, ⟨?_, ?_, hi⟩, rfl⟩
      · rintro rfl
        rw [h] at hneg
        exact lt_irrefl 0 hneg
      · rintro rfl
        rw [h] at hpos
        exact lt_irrefl 0 hpos
    · rintro ⟨i, ⟨hik, hij, hi⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hzero i hi hij hik⟩
  have hU : upperSide (s.image p) a c = (s.erase k).image p := by
    ext x
    simp only [upperSide, Finset.mem_filter, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      rintro rfl
      linarith
    · rintro ⟨i, ⟨hik, hi⟩, rfl⟩
      refine ⟨⟨i, hi, rfl⟩, ?_⟩
      by_cases hij : i = j
      · rw [hij]
        exact hpos.le
      · rw [hzero i hi hij hik]
  have hL : lowerSide (s.image p) a c = (s.erase j).image p := by
    ext x
    simp only [lowerSide, Finset.mem_filter, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, h⟩
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      rintro rfl
      linarith
    · rintro ⟨i, ⟨hij, hi⟩, rfl⟩
      refine ⟨⟨i, hi, rfl⟩, ?_⟩
      by_cases hik : i = k
      · rw [hik]
        exact hneg.le
      · rw [hzero i hi hij hik]
  refine ⟨?_, ?_, ?_⟩
  · rw [sectionPoints, hZ, hM, Finset.union_comm, ← Finset.insert_eq]
  · rw [upperPoints, hU, hM, Finset.union_comm, ← Finset.insert_eq, image_update_eq_insert p hk]
  · rw [lowerPoints, hL, hM, Finset.union_comm, ← Finset.insert_eq, image_update_eq_insert p hj]

/-- The cut identity (`SupportCut.support_cut_identity`) written with `hS`. -/
theorem hS_add_hS_sectionPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    (h0 : (sectionPoints S a c).Nonempty) (y : Fin N → ℝ) :
    hS S y + hS (sectionPoints S a c) y =
      hS (upperPoints S a c) y + hS (lowerPoints S a c) y := by
  rw [hS_of_nonempty (nonempty_of_nonempty_sectionPoints h0), hS_of_nonempty h0,
    hS_of_nonempty (nonempty_upperPoints h0), hS_of_nonempty (nonempty_lowerPoints h0)]
  exact support_cut_identity S a c h0 y

theorem hS_empty : hS (∅ : Finset (Fin N → ℝ)) = 0 := by
  funext y
  simp [hS]

/-- A support function of a point set of affine dimension `≤ k` lies in `LSpan N k`. -/
theorem hS_mem_LSpan_of_finrank_le {S : Finset (Fin N → ℝ)} {k : ℕ}
    (hdim : FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin N → ℝ))) ≤ k) :
    hS S ∈ LSpan N k := by
  by_cases hne : S.Nonempty
  · exact Submodule.subset_span ⟨S, hne, hdim, fun y => hS_of_nonempty hne y⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [hS_empty]
    exact Submodule.zero_mem _

/-- `insert q ((T.erase k).image p)` (`k ∈ T`, `|T| = n + 1`) has affine dimension `≤ n`. -/
theorem finrank_vectorSpan_insert_image_le (p : ι → Fin N → ℝ) {T : Finset ι} {k : ι}
    (hk : k ∈ T) (q : Fin N → ℝ) {n : ℕ} (hT : T.card = n + 1) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(insert q ((T.erase k).image p)) : Set (Fin N → ℝ))) ≤ n := by
  rw [← image_update_eq_insert p hk q]
  exact finrank_vectorSpan_image_finset_le ℝ (Function.update p k q) T hT

end

end SimplexCut

end MaxNN.ParamidGeom
