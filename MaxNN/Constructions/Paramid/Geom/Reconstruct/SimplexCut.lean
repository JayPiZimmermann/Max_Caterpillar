import MaxNN.Constructions.Paramid.Geom.Reconstruct.SimplexCut.SweepFacts

/-!
# The geometric core of the simplex sweep reconstruction

Helper of `Geom/Reconstruct.lean` (blueprint `work/depth2_simplex/lean_core/BLUEPRINT.md`,
section M-Reconstruct; paper level: `CONSTRUCTIVE_SWEEP_RECONSTRUCTION_2026-10-13.md`, Section 3,
algorithm VCR specialised to simplices).

Throughout, `p : Fin (m + 1) → ℝ^m` is affinely independent (an `m`-simplex), `β_j` are its
barycentric coordinates, `λ_j = (β_j)'(v) = baryLin p hp v j` their rates along a direction `v`,
`F_j = (univ.erase j).image p` the facet opposite `p_j`, and
`facetSign p hp v j = − sign λ_j` (`+1` upper, `−1` lower, `0` vertical;
`SimplexCut/Bary.lean`).

## 1. Facet signs (`SimplexCut/Bary.lean`)

`sum_baryLin` (`∑_j λ_j = 0`), `sum_baryLin_smul` (`∑_j λ_j • p_j = v`),
`exists_facetSign_eq_one`, `exists_facetSign_eq_neg_one` (for `v ≠ 0` there is an upper and a
lower facet).

## 2. The ridge cut

For `j ≠ k` with `λ_j λ_k > 0` (two upper or two lower facets), the affine function
`ℓ = λ_j β_k − λ_k β_j = ⟨a, ·⟩ − c` (`a = ridgeNormal`, `c = ridgeLevel`,
`dot_ridgeNormal_sub_ridgeLevel`) is vertical (`dot_ridgeNormal_self`), nonconstant
(`ridgeNormal_ne_zero`), vanishes at every vertex except `p_j` (`ℓ = −λ_k`) and `p_k` (`ℓ = λ_j`),
and cuts the edge `[p_j, p_k]` at `q = ridgePoint = (λ_j p_j + λ_k p_k) / (λ_j + λ_k)`
(`ridgePoint_eq`).

* `ridgeCut_upper`, `ridgeCut_lower`: the `SupportCut` point sets of the simplex, as `Finset`s;
  `ridgeCut_points_of_neg`, `ridgeCut_points_of_pos`: the same for `s.image p`, any index set
  `s ∋ j, k`; `ridgeCut_facet_of_neg`, `ridgeCut_facet_of_pos`: the facets
  `F_i = (univ.erase i).image p`, `i ≠ j, k`, are cut into the facets opposite `i` of the two
  pieces, with a section of affine dimension `≤ m − 2`.
* `hS_ridgeCut`: `h_{s.image p} + h_{section} = h_{left piece} + h_{right piece}`.
* `affineIndependent_ridgeLeft/Right`: the pieces `update p k q` and `update p j q` are simplices;
  `facetSign_ridgeLeft/Right`: their facet signs (the facet opposite `q` keeps the sign of `F_k`
  resp. `F_j`, the facet in the cut hyperplane is vertical, all others keep their signs);
  `ridgeLeft_facet_self`, `ridgeLeft_facet_cut`, `ridgeRight_facet_self`, `ridgeRight_facet_cut`:
  which point sets these facets are.
* `finrank_ridgeSection_le` (`≤ m − 1`), `finrank_ridgeSection_facet_le` (`≤ m − 2`).
* `residual_ridgeCut`: the node identity (V_node) of VCR for simplices.

## 3. The column (leaf)

`column_sweep`: for exactly one upper facet `F⁺ = F_a`, one lower facet `F⁻ = F_b`, all others
vertical, `h_P + 𝒯 h_{F⁻} = 𝒯 h_{F⁺} + h_{F⁻}` (no height hypothesis); `column_hS`: with all
vertices high, the prism form `h_P + h_{T F⁻} = h_{T F⁺} + h_{F⁻}`, `T G = G ∪ π G`.
The proof does not need the cut of the prism: in a column, `v ∥ p_b − p_a`, so
`π p_a = π p_b`, and both sides are compared through `max`.

## 4. The simplex reconstruction

`simplex_reconstruct` (blueprint statement): for high vertices,
`h_P − ∑_j facetSign_j · 𝒯 h_{F_j} ∈ LSpan m (m − 1)`, by induction on the number of
non-vertical facets (ridge cuts, then a column at every leaf).

Generic helpers live in the sub-namespace `MaxNN.ParamidGeom.SimplexCut` (among them
`SimplexCut.hS_eq_of_convexHull_eq`: `hS` depends only on the convex hull); the sweep facts needed
here (`SimplexCut/SweepFacts.lean`) are proved locally because `Geom/Sweep.lean` did not exist
when this module was written.  Do not `open` both `SimplexCut` and `Sweep`: the helper names
`hS_empty`, `hS_eq_of_convexHull_eq`, `hS_le_of_subset_convexHull` exist in both
sub-namespaces; and with `SimplexCut` open inside `MaxNN.ParamidGeom`, the name
`sweep_hS_of_high` also refers to the (different) declaration of `Geom/Sweep.lean`, so qualify it.
-/

namespace MaxNN.ParamidGeom

open BigOperators MaxNN.SupportCut SimplexCut

noncomputable section

variable {m : ℕ}

/-! ## Generic helpers -/

namespace SimplexCut

theorem image_erase_update_self {ι E : Type*} [DecidableEq ι] [DecidableEq E] [Fintype ι]
    (p : ι → E) (k : ι) (q : E) :
    (Finset.univ.erase k).image (Function.update p k q) = (Finset.univ.erase k).image p :=
  Finset.image_congr fun _ hi => Function.update_noteq (Finset.ne_of_mem_erase hi) _ _

theorem one_le_of_ne {j k : Fin (m + 1)} (hjk : j ≠ k) : 1 ≤ m := by
  have hkT : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
  have hc : (Finset.univ.erase j).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin, Nat.add_sub_cancel]
  have hpos : 0 < (Finset.univ.erase j).card := Finset.card_pos.mpr ⟨k, hkT⟩
  exact Nat.succ_le_of_lt (lt_of_lt_of_eq hpos hc)

theorem two_le_of_three_ne {i j k : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 ≤ m := by
  have hkT : k ∈ (Finset.univ.erase i).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩⟩
  have hc : ((Finset.univ.erase i).erase j).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    omega
  have hpos : 0 < ((Finset.univ.erase i).erase j).card := Finset.card_pos.mpr ⟨k, hkT⟩
  exact Nat.succ_le_of_lt (Nat.sub_pos_iff_lt.mp (lt_of_lt_of_eq hpos hc))

theorem sign_add_of_mul_pos {a b : ℝ} (h : 0 < a * b) :
    SignType.sign (a + b) = SignType.sign b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [sign_pos (add_pos ha hb), sign_pos hb]
  · rw [sign_neg (add_neg ha hb), sign_neg hb]

/-- If `⟨p_a, y⟩ ≤ ⟨p_b, y⟩` (`a ≠ b`), dropping `p_a` does not change the support function. -/
theorem hS_image_univ_eq_erase {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Fin N → ℝ) {a b : ι} (hab : a ≠ b) (y : Fin N → ℝ)
    (h : dot (p a) y ≤ dot (p b) y) :
    hS (Finset.univ.image p) y = hS ((Finset.univ.erase a).image p) y := by
  have hb : p b ∈ (Finset.univ.erase a).image p :=
    Finset.mem_image_of_mem p (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)
  have hne : ((Finset.univ.erase a).image p).Nonempty := ⟨p b, hb⟩
  have hne' : (Finset.univ.image p).Nonempty := ⟨p b, Finset.mem_image_of_mem p (Finset.mem_univ b)⟩
  rw [hS_of_nonempty hne', hS_of_nonempty hne]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    by_cases hia : i = a
    · rw [hia]
      exact le_trans h (Finset.le_sup' (fun x => dot x y) hb)
    · exact Finset.le_sup' (fun x => dot x y)
        (Finset.mem_image_of_mem p (Finset.mem_erase.mpr ⟨hia, Finset.mem_univ i⟩))
  · exact Finset.sup'_le _ _ fun x hx => Finset.le_sup' (fun x => dot x y)
      (Finset.image_subset_image (Finset.erase_subset a Finset.univ) hx)

/-- A point set inside the convex hull of a nonempty `S` has support function `≤ h_S`. -/
theorem hS_le_of_subset_convexHull {N : ℕ} {S T : Finset (Fin N → ℝ)} (hSne : S.Nonempty)
    (hTne : T.Nonempty) (hT : (T : Set (Fin N → ℝ)) ⊆ convexHull ℝ (S : Set (Fin N → ℝ)))
    (y : Fin N → ℝ) : hS T y ≤ hS S y := by
  rw [hS_of_nonempty hTne, hS_of_nonempty hSne]
  refine Finset.sup'_le _ _ fun t ht => ?_
  have hconv : Convex ℝ {x : Fin N → ℝ | dot y x ≤ S.sup' hSne (fun p => dot p y)} :=
    convex_halfspace_le (dotL y).isLinear _
  have hsub : (S : Set (Fin N → ℝ)) ⊆ {x : Fin N → ℝ | dot y x ≤ S.sup' hSne (fun p => dot p y)} :=
    fun p hp => by
      show dot y p ≤ _
      rw [dot_comm]
      exact Finset.le_sup' (fun p => dot p y) hp
  have hmem := convexHull_min hsub hconv (hT (Finset.mem_coe.mpr ht))
  have hmem' : dot y t ≤ S.sup' hSne (fun p => dot p y) := hmem
  rw [dot_comm] at hmem'
  exact hmem'

/-- **`hS` depends only on the convex hull.** -/
theorem hS_eq_of_convexHull_eq {N : ℕ} {S T : Finset (Fin N → ℝ)}
    (h : convexHull ℝ (S : Set (Fin N → ℝ)) = convexHull ℝ (T : Set (Fin N → ℝ))) :
    hS S = hS T := by
  funext y
  by_cases hSne : S.Nonempty
  · have hTne : T.Nonempty := by
      rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ), ← h,
        convexHull_nonempty_iff, Finset.coe_nonempty]
      exact hSne
    apply le_antisymm
    · exact hS_le_of_subset_convexHull hTne hSne
        ((subset_convexHull ℝ (S : Set (Fin N → ℝ))).trans h.le) y
    · exact hS_le_of_subset_convexHull hSne hTne
        ((subset_convexHull ℝ (T : Set (Fin N → ℝ))).trans h.ge) y
  · have hTne : ¬T.Nonempty := by
      rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ), ← h,
        convexHull_nonempty_iff, Finset.coe_nonempty]
      exact hSne
    rw [Finset.not_nonempty_iff_eq_empty] at hSne hTne
    rw [hSne, hTne]

/-- If `⟨p_a, y⟩ = ⟨p_b, y⟩` (`a ≠ b`), the facets opposite `p_a` and `p_b` have the same support
function at `y`. -/
theorem hS_image_erase_eq_of_dot_eq {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Fin N → ℝ) {a b : ι} (hab : a ≠ b) (y : Fin N → ℝ)
    (h : dot (p a) y = dot (p b) y) :
    hS ((Finset.univ.erase a).image p) y = hS ((Finset.univ.erase b).image p) y := by
  rw [← hS_image_univ_eq_erase p hab y h.le, ← hS_image_univ_eq_erase p hab.symm y h.ge]

end SimplexCut

/-! ## 2. The ridge cut -/

section Ridge

variable (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) (v : Fin m → ℝ)
  (j k : Fin (m + 1))

/-- Normal vector `a` of the ridge hyperplane `{ℓ = 0}`, `ℓ = λ_j β_k − λ_k β_j`
(`ℓ x = ⟨a, x⟩ − c`, `dot_ridgeNormal_sub_ridgeLevel`). -/
def ridgeNormal : Fin m → ℝ :=
  dualVec (baryLin p hp v j • ((simplexBasis p hp).coord k).linear -
    baryLin p hp v k • ((simplexBasis p hp).coord j).linear)

/-- Level `c` of the ridge hyperplane `{⟨a, ·⟩ = c}`. -/
def ridgeLevel : ℝ :=
  baryLin p hp v k * (simplexBasis p hp).coord j 0 -
    baryLin p hp v j * (simplexBasis p hp).coord k 0

/-- The crossing point `q` of the edge `[p_j, p_k]` with the ridge hyperplane (the `SupportCut`
crossing point; closed form `ridgePoint_eq`). -/
def ridgePoint : Fin m → ℝ :=
  crossPoint (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) (p j) (p k)

/-- The edge parameter `t = λ_k / (λ_j + λ_k)`: `q = (1 − t) p_j + t p_k`. -/
def ridgeParam : ℝ :=
  baryLin p hp v k / (baryLin p hp v j + baryLin p hp v k)

/-- **`ℓ = λ_j β_k − λ_k β_j` written as `⟨a, x⟩ − c`.** -/
theorem dot_ridgeNormal_sub_ridgeLevel (x : Fin m → ℝ) :
    dot (ridgeNormal p hp v j k) x - ridgeLevel p hp v j k =
      baryLin p hp v j * (simplexBasis p hp).coord k x -
        baryLin p hp v k * (simplexBasis p hp).coord j x := by
  rw [ridgeNormal, dot_dualVec, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, affine_linear_eq_sub, affine_linear_eq_sub, ridgeLevel]
  ring

theorem level_ridge (x : Fin m → ℝ) :
    level (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) x =
      baryLin p hp v j * (simplexBasis p hp).coord k x -
        baryLin p hp v k * (simplexBasis p hp).coord j x :=
  dot_ridgeNormal_sub_ridgeLevel p hp v j k x

/-- **The ridge hyperplane is vertical:** `⟨a, v⟩ = 0`. -/
theorem dot_ridgeNormal_self : dot (ridgeNormal p hp v j k) v = 0 := by
  rw [ridgeNormal, dot_dualVec, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul]
  show baryLin p hp v j * baryLin p hp v k - baryLin p hp v k * baryLin p hp v j = 0
  ring

theorem level_ridge_left (hjk : j ≠ k) :
    level (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) (p j) = -baryLin p hp v k := by
  rw [level_ridge, coord_simplexBasis_vertex, coord_simplexBasis_vertex, if_neg hjk.symm,
    if_pos rfl]
  ring

theorem level_ridge_right (hjk : j ≠ k) :
    level (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) (p k) = baryLin p hp v j := by
  rw [level_ridge, coord_simplexBasis_vertex, coord_simplexBasis_vertex, if_pos rfl, if_neg hjk]
  ring

theorem level_ridge_other {i : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k) :
    level (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) (p i) = 0 := by
  rw [level_ridge, coord_simplexBasis_vertex, coord_simplexBasis_vertex, if_neg (Ne.symm hik),
    if_neg (Ne.symm hij)]
  ring

/-- **The ridge normal is nonzero** (`ℓ` takes the values `−λ_k ≠ λ_j` at `p_j`, `p_k`). -/
theorem ridgeNormal_ne_zero (hjk : j ≠ k) (hsum : baryLin p hp v j + baryLin p hp v k ≠ 0) :
    ridgeNormal p hp v j k ≠ 0 := by
  intro h0
  have hconst : ∀ x, level (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) x =
      -ridgeLevel p hp v j k := by
    intro x
    show dot (ridgeNormal p hp v j k) x - ridgeLevel p hp v j k = _
    rw [h0]
    simp [dot]
  have e1 := level_ridge_left p hp v j k hjk
  have e2 := level_ridge_right p hp v j k hjk
  rw [hconst] at e1 e2
  exact hsum (by linarith)

theorem ridge_sum_ne_zero (hsame : 0 < baryLin p hp v j * baryLin p hp v k) :
    baryLin p hp v j + baryLin p hp v k ≠ 0 := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨hj, hk⟩ | ⟨hj, hk⟩
  · exact (add_pos hj hk).ne'
  · exact (add_neg hj hk).ne

/-- **Closed form of the crossing point:** `q = (1 − t) p_j + t p_k`, `t = λ_k / (λ_j + λ_k)`. -/
theorem ridgePoint_eq (hjk : j ≠ k) (hsum : baryLin p hp v j + baryLin p hp v k ≠ 0) :
    ridgePoint p hp v j k =
      (1 - ridgeParam p hp v j k) • p j + ridgeParam p hp v j k • p k := by
  have hsum' : -baryLin p hp v k - baryLin p hp v j ≠ 0 := by
    intro h
    apply hsum
    linarith
  rw [ridgePoint, crossPoint_eq_segCross]
  funext l
  rw [segCross_apply, level_ridge_left p hp v j k hjk, level_ridge_right p hp v j k hjk,
    ridgeParam]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem ridgeParam_pos (hsame : 0 < baryLin p hp v j * baryLin p hp v k) :
    0 < ridgeParam p hp v j k := by
  rw [ridgeParam]
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨hj, hk⟩ | ⟨hj, hk⟩
  · exact div_pos hk (add_pos hj hk)
  · exact div_pos_iff.mpr (Or.inr ⟨hk, add_neg hj hk⟩)

theorem one_sub_ridgeParam (hsum : baryLin p hp v j + baryLin p hp v k ≠ 0) :
    1 - ridgeParam p hp v j k = baryLin p hp v j / (baryLin p hp v j + baryLin p hp v k) := by
  rw [ridgeParam, eq_div_iff hsum, sub_mul, div_mul_cancel _ hsum]
  ring

theorem one_sub_ridgeParam_pos (hsame : 0 < baryLin p hp v j * baryLin p hp v k) :
    0 < 1 - ridgeParam p hp v j k := by
  rw [one_sub_ridgeParam p hp v j k (ridge_sum_ne_zero p hp v j k hsame)]
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨hj, hk⟩ | ⟨hj, hk⟩
  · exact div_pos hj (add_pos hj hk)
  · exact div_pos_iff.mpr (Or.inr ⟨hj, add_neg hj hk⟩)

/-- The crossing point seen from `p_k`: `q = (1 − s) p_k + s p_j`, `s = 1 − t`. -/
theorem ridgePoint_eq_right (hjk : j ≠ k) (hsum : baryLin p hp v j + baryLin p hp v k ≠ 0) :
    ridgePoint p hp v j k =
      (1 - (1 - ridgeParam p hp v j k)) • p k + (1 - ridgeParam p hp v j k) • p j := by
  rw [ridgePoint_eq p hp v j k hjk hsum, sub_sub_cancel, add_comm]

/-- **The cut point sets, two upper facets** (`λ_j, λ_k < 0`), for any index set `s ∋ j, k`:
for `s = univ` the simplex, for `s = univ.erase i` (`i ≠ j, k`) its facet `F_i`. -/
theorem ridgeCut_points_of_neg (hjk : j ≠ k) (hj : baryLin p hp v j < 0)
    (hk : baryLin p hp v k < 0) (s : Finset (Fin (m + 1))) (hjs : j ∈ s) (hks : k ∈ s) :
    sectionPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) (((s.erase j).erase k).image p) ∧
      upperPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        s.image (Function.update p k (ridgePoint p hp v j k)) ∧
      lowerPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        s.image (Function.update p j (ridgePoint p hp v j k)) :=
  cutSets_of_two p s _ _ hjs hks
    (by
      rw [level_ridge_left p hp v j k hjk]
      linarith)
    (by
      rw [level_ridge_right p hp v j k hjk]
      exact hj)
    (fun _ _ hij hik => level_ridge_other p hp v j k hij hik)

/-- **The cut point sets, two lower facets** (`λ_j, λ_k > 0`): the halves are exchanged. -/
theorem ridgeCut_points_of_pos (hjk : j ≠ k) (hj : 0 < baryLin p hp v j)
    (hk : 0 < baryLin p hp v k) (s : Finset (Fin (m + 1))) (hjs : j ∈ s) (hks : k ∈ s) :
    sectionPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) (((s.erase j).erase k).image p) ∧
      upperPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        s.image (Function.update p j (ridgePoint p hp v j k)) ∧
      lowerPoints (s.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        s.image (Function.update p k (ridgePoint p hp v j k)) := by
  obtain ⟨h1, h2, h3⟩ := cutSets_of_two p s (ridgeNormal p hp v j k) (ridgeLevel p hp v j k)
    hks hjs
    (by
      rw [level_ridge_right p hp v j k hjk]
      exact hj)
    (by
      rw [level_ridge_left p hp v j k hjk]
      linarith)
    (fun _ _ hik hij => level_ridge_other p hp v j k hij hik)
  rw [crossPoint_comm (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) (p k) (p j)] at h1 h2 h3
  have e : (s.erase k).erase j = (s.erase j).erase k := Finset.erase_right_comm
  rw [e] at h1
  exact ⟨h1, h2, h3⟩

/-- **Ridge cut through two upper facets** `F_j`, `F_k` (`λ_j, λ_k < 0`): the hyperplane
`{⟨a, ·⟩ = c}` is vertical with `a ≠ 0`; the section of the simplex is `q` together with the
vertices other than `p_j, p_k`; the upper half is the simplex with `p_k` replaced by `q`, the lower
half the simplex with `p_j` replaced by `q`. -/
theorem ridgeCut_upper (hjk : j ≠ k) (hj : baryLin p hp v j < 0) (hk : baryLin p hp v k < 0) :
    ridgeNormal p hp v j k ≠ 0 ∧ dot (ridgeNormal p hp v j k) v = 0 ∧
      sectionPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p) ∧
      upperPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        Finset.univ.image (Function.update p k (ridgePoint p hp v j k)) ∧
      lowerPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        Finset.univ.image (Function.update p j (ridgePoint p hp v j k)) :=
  ⟨ridgeNormal_ne_zero p hp v j k hjk (add_neg hj hk).ne, dot_ridgeNormal_self p hp v j k,
    ridgeCut_points_of_neg p hp v j k hjk hj hk Finset.univ (Finset.mem_univ j)
      (Finset.mem_univ k)⟩

/-- **Ridge cut through two lower facets** `F_j`, `F_k` (`λ_j, λ_k > 0`). -/
theorem ridgeCut_lower (hjk : j ≠ k) (hj : 0 < baryLin p hp v j) (hk : 0 < baryLin p hp v k) :
    ridgeNormal p hp v j k ≠ 0 ∧ dot (ridgeNormal p hp v j k) v = 0 ∧
      sectionPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p) ∧
      upperPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        Finset.univ.image (Function.update p j (ridgePoint p hp v j k)) ∧
      lowerPoints (Finset.univ.image p) (ridgeNormal p hp v j k) (ridgeLevel p hp v j k) =
        Finset.univ.image (Function.update p k (ridgePoint p hp v j k)) :=
  ⟨ridgeNormal_ne_zero p hp v j k hjk (add_pos hj hk).ne', dot_ridgeNormal_self p hp v j k,
    ridgeCut_points_of_pos p hp v j k hjk hj hk Finset.univ (Finset.mem_univ j)
      (Finset.mem_univ k)⟩

/-- **The cut identity of a ridge cut** (`λ_j λ_k > 0`), for the simplex (`s = univ`) or any face
`s.image p` with `j, k ∈ s`:
`h_{s.image p} + h_{section} = h_{s.image (update p k q)} + h_{s.image (update p j q)}`. -/
theorem hS_ridgeCut (hjk : j ≠ k) (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (s : Finset (Fin (m + 1))) (hjs : j ∈ s) (hks : k ∈ s) (y : Fin m → ℝ) :
    hS (s.image p) y + hS (insert (ridgePoint p hp v j k) (((s.erase j).erase k).image p)) y =
      hS (s.image (Function.update p k (ridgePoint p hp v j k))) y +
        hS (s.image (Function.update p j (ridgePoint p hp v j k))) y := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨hj, hk⟩ | ⟨hj, hk⟩
  · obtain ⟨h1, h2, h3⟩ := ridgeCut_points_of_pos p hp v j k hjk hj hk s hjs hks
    have h0 : (sectionPoints (s.image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k)).Nonempty := by
      rw [h1]
      exact Finset.insert_nonempty _ _
    have key := hS_add_hS_sectionPoints h0 y
    rw [h1, h2, h3] at key
    linarith
  · obtain ⟨h1, h2, h3⟩ := ridgeCut_points_of_neg p hp v j k hjk hj hk s hjs hks
    have h0 : (sectionPoints (s.image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k)).Nonempty := by
      rw [h1]
      exact Finset.insert_nonempty _ _
    have key := hS_add_hS_sectionPoints h0 y
    rw [h1, h2, h3] at key
    exact key

/-- The left piece `update p k q` is a simplex. -/
theorem affineIndependent_ridgeLeft (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k) :
    AffineIndependent ℝ (Function.update p k (ridgePoint p hp v j k)) :=
  affineIndependent_update_of_eq hp hjk (ridgeParam_pos p hp v j k hsame).ne'
    (ridgePoint_eq p hp v j k hjk (ridge_sum_ne_zero p hp v j k hsame))

/-- The right piece `update p j q` is a simplex. -/
theorem affineIndependent_ridgeRight (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k) :
    AffineIndependent ℝ (Function.update p j (ridgePoint p hp v j k)) :=
  affineIndependent_update_of_eq hp hjk.symm (one_sub_ridgeParam_pos p hp v j k hsame).ne'
    (ridgePoint_eq_right p hp v j k hjk (ridge_sum_ne_zero p hp v j k hsame))

/-- Rates of the left piece: `λ_j + λ_k` at the new vertex `q` (index `k`), `0` at index `j`
(its facet opposite `p_j` lies in the vertical cut hyperplane), unchanged elsewhere. -/
theorem baryLin_ridgeLeft (hjk : j ≠ k) (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h1 : AffineIndependent ℝ (Function.update p k (ridgePoint p hp v j k))) (i : Fin (m + 1)) :
    baryLin (Function.update p k (ridgePoint p hp v j k)) h1 v i =
      if i = k then baryLin p hp v j + baryLin p hp v k
      else if i = j then 0 else baryLin p hp v i := by
  have hsum := ridge_sum_ne_zero p hp v j k hsame
  have hk0 : baryLin p hp v k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsame
    exact lt_irrefl 0 hsame
  rw [baryLin_update_of_eq hp hjk (ridgeParam_pos p hp v j k hsame).ne'
    (ridgePoint_eq p hp v j k hjk hsum) h1 v i]
  have e1 : baryLin p hp v k / ridgeParam p hp v j k = baryLin p hp v j + baryLin p hp v k := by
    rw [ridgeParam]
    field_simp
    ring
  have e2 : baryLin p hp v j -
      baryLin p hp v k * (1 - ridgeParam p hp v j k) / ridgeParam p hp v j k = 0 := by
    rw [one_sub_ridgeParam p hp v j k hsum, ridgeParam]
    field_simp
    ring
  rw [e1, e2]

/-- Rates of the right piece: `λ_j + λ_k` at the new vertex `q` (index `j`), `0` at index `k`,
unchanged elsewhere. -/
theorem baryLin_ridgeRight (hjk : j ≠ k) (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h2 : AffineIndependent ℝ (Function.update p j (ridgePoint p hp v j k))) (i : Fin (m + 1)) :
    baryLin (Function.update p j (ridgePoint p hp v j k)) h2 v i =
      if i = j then baryLin p hp v j + baryLin p hp v k
      else if i = k then 0 else baryLin p hp v i := by
  have hsum := ridge_sum_ne_zero p hp v j k hsame
  have hj0 : baryLin p hp v j ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsame
    exact lt_irrefl 0 hsame
  rw [baryLin_update_of_eq hp hjk.symm (one_sub_ridgeParam_pos p hp v j k hsame).ne'
    (ridgePoint_eq_right p hp v j k hjk hsum) h2 v i]
  have e1 : baryLin p hp v j / (1 - ridgeParam p hp v j k) =
      baryLin p hp v j + baryLin p hp v k := by
    rw [one_sub_ridgeParam p hp v j k hsum]
    field_simp
    ring
  have e2 : baryLin p hp v k - baryLin p hp v j * (1 - (1 - ridgeParam p hp v j k)) /
      (1 - ridgeParam p hp v j k) = 0 := by
    rw [sub_sub_cancel, one_sub_ridgeParam p hp v j k hsum, ridgeParam]
    field_simp
    ring
  rw [e1, e2]

/-- **Facet signs of the left piece** `update p k q`: the facet opposite `q` (index `k`) has the
sign of `F_k`, the facet opposite `p_j` (in the cut hyperplane) is vertical, all others keep the
signs of the corresponding facets of `p`. -/
theorem facetSign_ridgeLeft (hjk : j ≠ k) (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h1 : AffineIndependent ℝ (Function.update p k (ridgePoint p hp v j k))) (i : Fin (m + 1)) :
    facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v i =
      if i = j then 0 else facetSign p hp v i := by
  rw [facetSign_eq, baryLin_ridgeLeft p hp v j k hjk hsame h1 i]
  by_cases hik : i = k
  · have hij : i ≠ j := by
      rw [hik]
      exact hjk.symm
    rw [if_pos hik, if_neg hij, hik, facetSign_eq, sign_add_of_mul_pos hsame]
  · by_cases hij : i = j
    · rw [if_neg hik, if_pos hij, if_pos hij, sign_zero, SignType.coe_zero, neg_zero]
    · rw [if_neg hik, if_neg hij, if_neg hij, facetSign_eq]

/-- **Facet signs of the right piece** `update p j q`: the facet opposite `q` (index `j`) has the
sign of `F_j`, the facet opposite `p_k` (in the cut hyperplane) is vertical, all others keep the
signs of the corresponding facets of `p`. -/
theorem facetSign_ridgeRight (hjk : j ≠ k) (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h2 : AffineIndependent ℝ (Function.update p j (ridgePoint p hp v j k))) (i : Fin (m + 1)) :
    facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v i =
      if i = k then 0 else facetSign p hp v i := by
  rw [facetSign_eq, baryLin_ridgeRight p hp v j k hjk hsame h2 i]
  by_cases hij : i = j
  · have hik : i ≠ k := by
      rw [hij]
      exact hjk
    have hsame' : 0 < baryLin p hp v k * baryLin p hp v j := by
      rw [mul_comm]
      exact hsame
    rw [if_pos hij, if_neg hik, hij, facetSign_eq, add_comm, sign_add_of_mul_pos hsame']
  · by_cases hik : i = k
    · rw [if_neg hij, if_pos hik, if_pos hik, sign_zero, SignType.coe_zero, neg_zero]
    · rw [if_neg hij, if_neg hik, if_neg hik, facetSign_eq]

/-- The facet of the left piece opposite `q` is the old facet `F_k`. -/
theorem ridgeLeft_facet_self :
    (Finset.univ.erase k).image (Function.update p k (ridgePoint p hp v j k)) =
      (Finset.univ.erase k).image p :=
  image_erase_update_self p k _

/-- The facet of the left piece opposite `p_j` is the section (in the cut hyperplane). -/
theorem ridgeLeft_facet_cut (hjk : j ≠ k) :
    (Finset.univ.erase j).image (Function.update p k (ridgePoint p hp v j k)) =
      insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p) :=
  image_update_eq_insert p (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩) _

/-- The facet of the right piece opposite `q` is the old facet `F_j`. -/
theorem ridgeRight_facet_self :
    (Finset.univ.erase j).image (Function.update p j (ridgePoint p hp v j k)) =
      (Finset.univ.erase j).image p :=
  image_erase_update_self p j _

/-- The facet of the right piece opposite `p_k` is the section (in the cut hyperplane). -/
theorem ridgeRight_facet_cut (hjk : j ≠ k) :
    (Finset.univ.erase k).image (Function.update p j (ridgePoint p hp v j k)) =
      insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p) := by
  rw [image_update_eq_insert p (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩),
    Finset.erase_right_comm]

/-- The section of the simplex has affine dimension `≤ m − 1`. -/
theorem finrank_ridgeSection_le (hjk : j ≠ k) :
    FiniteDimensional.finrank ℝ (vectorSpan ℝ
      (↑(insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p)) :
        Set (Fin m → ℝ))) ≤ m - 1 := by
  have hkT : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
  have hc : (Finset.univ.erase j).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin, Nat.add_sub_cancel]
  have hm := one_le_of_ne hjk
  exact finrank_vectorSpan_insert_image_le p hkT _ (by omega)

/-- The section of a cut facet `F_i` (`i ≠ j, k`) has affine dimension `≤ m − 2`. -/
theorem finrank_ridgeSection_facet_le {i : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    FiniteDimensional.finrank ℝ (vectorSpan ℝ
      (↑(insert (ridgePoint p hp v j k) ((((Finset.univ.erase i).erase j).erase k).image p)) :
        Set (Fin m → ℝ))) ≤ m - 2 := by
  have hkT : k ∈ (Finset.univ.erase i).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩⟩
  have hc : ((Finset.univ.erase i).erase j).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    omega
  have hm := two_le_of_three_ne hij hik hjk
  exact finrank_vectorSpan_insert_image_le p hkT _ (by omega)

/-- **The cut of a facet `F_i` (`i ≠ j, k`), two upper facets `F_j`, `F_k`:** the same
hyperplane cuts `F_i` into the facets opposite `i` of the two pieces, with a section of affine
dimension `≤ m − 2`. -/
theorem ridgeCut_facet_of_neg (hjk : j ≠ k) (hj : baryLin p hp v j < 0)
    (hk : baryLin p hp v k < 0) {i : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k) :
    sectionPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) ((((Finset.univ.erase i).erase j).erase k).image p) ∧
      upperPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        (Finset.univ.erase i).image (Function.update p k (ridgePoint p hp v j k)) ∧
      lowerPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        (Finset.univ.erase i).image (Function.update p j (ridgePoint p hp v j k)) ∧
      FiniteDimensional.finrank ℝ (vectorSpan ℝ
        (↑(insert (ridgePoint p hp v j k) ((((Finset.univ.erase i).erase j).erase k).image p)) :
          Set (Fin m → ℝ))) ≤ m - 2 :=
  let h := ridgeCut_points_of_neg p hp v j k hjk hj hk (Finset.univ.erase i)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩)
  ⟨h.1, h.2.1, h.2.2, finrank_ridgeSection_facet_le p hp v j k hij hik hjk⟩

/-- **The cut of a facet `F_i` (`i ≠ j, k`), two lower facets `F_j`, `F_k`.** -/
theorem ridgeCut_facet_of_pos (hjk : j ≠ k) (hj : 0 < baryLin p hp v j)
    (hk : 0 < baryLin p hp v k) {i : Fin (m + 1)} (hij : i ≠ j) (hik : i ≠ k) :
    sectionPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        insert (ridgePoint p hp v j k) ((((Finset.univ.erase i).erase j).erase k).image p) ∧
      upperPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        (Finset.univ.erase i).image (Function.update p j (ridgePoint p hp v j k)) ∧
      lowerPoints ((Finset.univ.erase i).image p) (ridgeNormal p hp v j k)
        (ridgeLevel p hp v j k) =
        (Finset.univ.erase i).image (Function.update p k (ridgePoint p hp v j k)) ∧
      FiniteDimensional.finrank ℝ (vectorSpan ℝ
        (↑(insert (ridgePoint p hp v j k) ((((Finset.univ.erase i).erase j).erase k).image p)) :
          Set (Fin m → ℝ))) ≤ m - 2 :=
  let h := ridgeCut_points_of_pos p hp v j k hjk hj hk (Finset.univ.erase i)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩)
  ⟨h.1, h.2.1, h.2.2, finrank_ridgeSection_facet_le p hp v j k hij hik hjk⟩

/-- The crossing point of two high vertices is high. -/
theorem dot_ridgePoint_nonneg (w : Fin m → ℝ) (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k) (hj : 0 ≤ dot w (p j))
    (hk : 0 ≤ dot w (p k)) : 0 ≤ dot w (ridgePoint p hp v j k) := by
  rw [ridgePoint_eq p hp v j k hjk (ridge_sum_ne_zero p hp v j k hsame), dot_add_right,
    dot_smul_right, dot_smul_right]
  exact add_nonneg (mul_nonneg (one_sub_ridgeParam_pos p hp v j k hsame).le hj)
    (mul_nonneg (ridgeParam_pos p hp v j k hsame).le hk)

/-- **The node identity (V_node) of the reconstruction, for a ridge cut of a simplex.**  The
reconstruction residual `R(P) = h_P − ∑_l facetSign_l · 𝒯 h_{F_l}` of the simplex is the sum of
the residuals of the two pieces, minus the support function of the section, plus the swept
sections of the cut facets `F_i` (`i ≠ j, k`). -/
theorem residual_ridgeCut (w : Fin m → ℝ) (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h1 : AffineIndependent ℝ (Function.update p k (ridgePoint p hp v j k)))
    (h2 : AffineIndependent ℝ (Function.update p j (ridgePoint p hp v j k))) (y : Fin m → ℝ) :
    hS (Finset.univ.image p) y -
        ∑ l, facetSign p hp v l * sweep v w (hS ((Finset.univ.erase l).image p)) y =
      (hS (Finset.univ.image (Function.update p k (ridgePoint p hp v j k))) y -
          ∑ l, facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p k (ridgePoint p hp v j k)))) y) +
        (hS (Finset.univ.image (Function.update p j (ridgePoint p hp v j k))) y -
          ∑ l, facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p j (ridgePoint p hp v j k)))) y) -
        hS (insert (ridgePoint p hp v j k) (((Finset.univ.erase j).erase k).image p)) y +
        ∑ i in (Finset.univ.erase j).erase k, facetSign p hp v i *
          sweep v w (hS (insert (ridgePoint p hp v j k)
            ((((Finset.univ.erase i).erase j).erase k).image p))) y := by
  have hkj : k ≠ j := hjk.symm
  have hcut := hS_ridgeCut p hp v j k hjk hsame Finset.univ (Finset.mem_univ j)
    (Finset.mem_univ k) y
  have e0 : ∑ l, facetSign p hp v l * sweep v w (hS ((Finset.univ.erase l).image p)) y =
      facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y +
        facetSign p hp v k * sweep v w (hS ((Finset.univ.erase k).image p)) y +
        ∑ l in (Finset.univ.erase j).erase k,
          facetSign p hp v l * sweep v w (hS ((Finset.univ.erase l).image p)) y :=
    sum_split_pair hjk _
  have e1 : ∑ l, facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v l *
        sweep v w (hS ((Finset.univ.erase l).image
          (Function.update p k (ridgePoint p hp v j k)))) y =
      facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v j *
          sweep v w (hS ((Finset.univ.erase j).image
            (Function.update p k (ridgePoint p hp v j k)))) y +
        facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v k *
          sweep v w (hS ((Finset.univ.erase k).image
            (Function.update p k (ridgePoint p hp v j k)))) y +
        ∑ l in (Finset.univ.erase j).erase k,
          facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p k (ridgePoint p hp v j k)))) y :=
    sum_split_pair hjk _
  have e2 : ∑ l, facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v l *
        sweep v w (hS ((Finset.univ.erase l).image
          (Function.update p j (ridgePoint p hp v j k)))) y =
      facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v j *
          sweep v w (hS ((Finset.univ.erase j).image
            (Function.update p j (ridgePoint p hp v j k)))) y +
        facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v k *
          sweep v w (hS ((Finset.univ.erase k).image
            (Function.update p j (ridgePoint p hp v j k)))) y +
        ∑ l in (Finset.univ.erase j).erase k,
          facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p j (ridgePoint p hp v j k)))) y :=
    sum_split_pair hjk _
  have s1j : facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v j = 0 := by
    rw [facetSign_ridgeLeft p hp v j k hjk hsame h1 j, if_pos rfl]
  have s1k : facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v k =
      facetSign p hp v k := by
    rw [facetSign_ridgeLeft p hp v j k hjk hsame h1 k, if_neg hkj]
  have s2k : facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v k = 0 := by
    rw [facetSign_ridgeRight p hp v j k hjk hsame h2 k, if_pos rfl]
  have s2j : facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v j =
      facetSign p hp v j := by
    rw [facetSign_ridgeRight p hp v j k hjk hsame h2 j, if_neg hjk]
  have erest : ∑ l in (Finset.univ.erase j).erase k,
        facetSign p hp v l * sweep v w (hS ((Finset.univ.erase l).image p)) y =
      ∑ l in (Finset.univ.erase j).erase k,
          facetSign (Function.update p k (ridgePoint p hp v j k)) h1 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p k (ridgePoint p hp v j k)))) y +
        ∑ l in (Finset.univ.erase j).erase k,
          facetSign (Function.update p j (ridgePoint p hp v j k)) h2 v l *
            sweep v w (hS ((Finset.univ.erase l).image
              (Function.update p j (ridgePoint p hp v j k)))) y -
        ∑ i in (Finset.univ.erase j).erase k, facetSign p hp v i *
          sweep v w (hS (insert (ridgePoint p hp v j k)
            ((((Finset.univ.erase i).erase j).erase k).image p))) y := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hij, hik⟩ := ne_ne_of_mem_erase_erase hi
    have hcut_i := sweep_add_eq_of_add_eq (fun z => hS_ridgeCut p hp v j k hjk hsame
      (Finset.univ.erase i) (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
      (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩) z) v w y
    rw [facetSign_ridgeLeft p hp v j k hjk hsame h1 i, if_neg hij,
      facetSign_ridgeRight p hp v j k hjk hsame h2 i, if_neg hik]
    linear_combination (facetSign p hp v i) * hcut_i
  rw [e0, e1, e2, s1j, s1k, s2k, s2j, ridgeLeft_facet_self p hp v j k,
    ridgeRight_facet_self p hp v j k, erest]
  linarith [hcut]

end Ridge

/-! ## 3. The column (leaf of the reconstruction) -/

section Column

variable {p : Fin (m + 1) → Fin m → ℝ} {hp : AffineIndependent ℝ p} {v w : Fin m → ℝ}

/-- **The column identity, sweep form.**  If `F_a` is the only upper facet, `F_b` the only lower
facet and all other facets are vertical, then
`h_P + 𝒯 h_{F_b} = 𝒯 h_{F_a} + h_{F_b}` for the sweep `𝒯 = sweep v w`, `⟨w, v⟩ = 1`.  (No
height hypothesis is needed in this form.) -/
theorem column_sweep (hvw : dot w v = 1) {a b : Fin (m + 1)} (ha : facetSign p hp v a = 1)
    (hb : facetSign p hp v b = -1) (h0 : ∀ i, i ≠ a → i ≠ b → facetSign p hp v i = 0)
    (y : Fin m → ℝ) :
    hS (Finset.univ.image p) y + sweep v w (hS ((Finset.univ.erase b).image p)) y =
      sweep v w (hS ((Finset.univ.erase a).image p)) y + hS ((Finset.univ.erase b).image p) y := by
  have ha' : baryLin p hp v a < 0 := facetSign_eq_one_iff.mp ha
  have hb' : 0 < baryLin p hp v b := facetSign_eq_neg_one_iff.mp hb
  have h0' : ∀ i, i ≠ a → i ≠ b → baryLin p hp v i = 0 := fun i hia hib =>
    facetSign_eq_zero_iff.mp (h0 i hia hib)
  have hab : a ≠ b := by
    rintro rfl
    linarith
  have hla : baryLin p hp v a = -baryLin p hp v b := by
    have hl : ∑ i, baryLin p hp v i = baryLin p hp v a + baryLin p hp v b :=
      Fintype.sum_eq_add a b hab fun x hx => h0' x hx.1 hx.2
    rw [sum_baryLin] at hl
    linarith
  have hv : v = baryLin p hp v b • (p b - p a) := by
    have hs : ∑ i, baryLin p hp v i • p i = baryLin p hp v a • p a + baryLin p hp v b • p b :=
      Fintype.sum_eq_add a b hab fun x hx => by simp only [h0' x hx.1 hx.2, zero_smul]
    rw [sum_baryLin_smul, hla, neg_smul] at hs
    exact hs.trans (by rw [smul_sub]; abel)
  have hedge : ∀ z, dot v z = baryLin p hp v b * (dot (p b) z - dot (p a) z) := by
    intro z
    conv_lhs => rw [hv]
    rw [dot_smul_left, dot_sub_left]
  unfold sweep
  split_ifs with hvy
  · rw [hS_image_univ_eq_erase p hab y (by nlinarith [hedge y])]
  · push_neg at hvy
    have hvy' : dot v (y - dot v y • w) = 0 := by
      rw [dot_sub_right, dot_smul_right, dot_comm v w, hvw, mul_one, sub_self]
    have heq : dot (p a) (y - dot v y • w) = dot (p b) (y - dot v y • w) := by
      have h := hedge (y - dot v y • w)
      rw [hvy'] at h
      have hz : dot (p b) (y - dot v y • w) - dot (p a) (y - dot v y • w) = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hb'.ne'
        · exact h'
      linarith
    rw [hS_image_univ_eq_erase p hab.symm y (by nlinarith [hedge y]),
      hS_image_erase_eq_of_dot_eq p hab _ heq]
    ring

/-- **The column identity, prism form** (vertices of nonnegative height):
`h_P + h_{T F⁻} = h_{T F⁺} + h_{F⁻}` with `T G = G ∪ G.image (sweepProj v w)`. -/
theorem column_hS_of_nonneg (hvw : dot w v = 1) {a b : Fin (m + 1)}
    (ha : facetSign p hp v a = 1) (hb : facetSign p hp v b = -1)
    (h0 : ∀ i, i ≠ a → i ≠ b → facetSign p hp v i = 0) (hhigh : ∀ i, 0 ≤ dot w (p i)) :
    hS (Finset.univ.image p) + hS ((Finset.univ.erase b).image p ∪
        ((Finset.univ.erase b).image p).image (sweepProj v w)) =
      hS ((Finset.univ.erase a).image p ∪
          ((Finset.univ.erase a).image p).image (sweepProj v w)) +
        hS ((Finset.univ.erase b).image p) := by
  have hF : ∀ c : Fin (m + 1), ∀ g ∈ (Finset.univ.erase c).image p, 0 ≤ dot w g := by
    intro c g hg
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
    exact hhigh i
  rw [← sweep_hS_of_high v w _ (hF b), ← sweep_hS_of_high v w _ (hF a)]
  funext y
  exact column_sweep hvw ha hb h0 y

/-- **The column identity** (the leaf of the reconstruction, blueprint form with
`0 < ⟨w, p_i⟩`): `h_P + h_{T F⁻} = h_{T F⁺} + h_{F⁻}` for `F⁺ = F_a`, `F⁻ = F_b`. -/
theorem column_hS (hvw : dot w v = 1) {a b : Fin (m + 1)} (ha : facetSign p hp v a = 1)
    (hb : facetSign p hp v b = -1) (h0 : ∀ i, i ≠ a → i ≠ b → facetSign p hp v i = 0)
    (hhigh : ∀ i, 0 < dot w (p i)) :
    hS (Finset.univ.image p) + hS ((Finset.univ.erase b).image p ∪
        ((Finset.univ.erase b).image p).image (sweepProj v w)) =
      hS ((Finset.univ.erase a).image p ∪
          ((Finset.univ.erase a).image p).image (sweepProj v w)) +
        hS ((Finset.univ.erase b).image p) :=
  column_hS_of_nonneg hvw ha hb h0 fun i => (hhigh i).le

end Column

/-! ## 4. The simplex reconstruction -/

/-- The residual of a column is the support function of its lower facet. -/
theorem residual_mem_LSpan_of_column (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v w : Fin m → ℝ} (hvw : dot w v = 1) {a b : Fin (m + 1)} (ha : baryLin p hp v a < 0)
    (hb : 0 < baryLin p hp v b) (h0 : ∀ i, i ≠ a → i ≠ b → baryLin p hp v i = 0) :
    (fun y => hS (Finset.univ.image p) y -
      ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y) ∈
        LSpan m (m - 1) := by
  have hab : a ≠ b := by
    rintro rfl
    linarith
  have hres : (fun y => hS (Finset.univ.image p) y -
      ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y) =
        hS ((Finset.univ.erase b).image p) := by
    funext y
    have hsplit : ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y =
        facetSign p hp v a * sweep v w (hS ((Finset.univ.erase a).image p)) y +
          facetSign p hp v b * sweep v w (hS ((Finset.univ.erase b).image p)) y :=
      Fintype.sum_eq_add a b hab fun x hx => by
        simp only [facetSign_of_eq_zero (h0 x hx.1 hx.2), zero_mul]
    have hcol := column_sweep hvw (facetSign_of_neg ha) (facetSign_of_pos hb)
      (fun i hia hib => facetSign_of_eq_zero (h0 i hia hib)) y
    rw [hsplit, facetSign_of_neg ha, facetSign_of_pos hb]
    linarith
  rw [hres]
  apply hS_mem_LSpan_of_finrank_le
  have hc : (Finset.univ.erase b).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_fin, Nat.add_sub_cancel]
  have hm := one_le_of_ne hab
  exact finrank_vectorSpan_image_finset_le ℝ p (Finset.univ.erase b) (by omega)

/-- The facets with nonzero rate of the left piece: those of `p` except `F_j`. -/
theorem filter_ridgeLeft (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) {j k : Fin (m + 1)} (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h1 : AffineIndependent ℝ (Function.update p k (ridgePoint p hp v j k))) :
    (Finset.univ.filter fun i =>
        baryLin (Function.update p k (ridgePoint p hp v j k)) h1 v i ≠ 0) =
      (Finset.univ.filter fun i => baryLin p hp v i ≠ 0).erase j := by
  have hsum := ridge_sum_ne_zero p hp v j k hsame
  have hk0 : baryLin p hp v k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsame
    exact lt_irrefl 0 hsame
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    baryLin_ridgeLeft p hp v j k hjk hsame h1 i]
  by_cases hik : i = k
  · rw [if_pos hik, hik]
    exact ⟨fun _ => ⟨hjk.symm, hk0⟩, fun _ => hsum⟩
  · rw [if_neg hik]
    by_cases hij : i = j
    · rw [if_pos hij, hij]
      simp
    · rw [if_neg hij]
      exact ⟨fun h => ⟨hij, h⟩, fun h => h.2⟩

/-- The facets with nonzero rate of the right piece: those of `p` except `F_k`. -/
theorem filter_ridgeRight (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) {j k : Fin (m + 1)} (hjk : j ≠ k)
    (hsame : 0 < baryLin p hp v j * baryLin p hp v k)
    (h2 : AffineIndependent ℝ (Function.update p j (ridgePoint p hp v j k))) :
    (Finset.univ.filter fun i =>
        baryLin (Function.update p j (ridgePoint p hp v j k)) h2 v i ≠ 0) =
      (Finset.univ.filter fun i => baryLin p hp v i ≠ 0).erase k := by
  have hsum := ridge_sum_ne_zero p hp v j k hsame
  have hj0 : baryLin p hp v j ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsame
    exact lt_irrefl 0 hsame
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
    baryLin_ridgeRight p hp v j k hjk hsame h2 i]
  by_cases hij : i = j
  · rw [if_pos hij, hij]
    exact ⟨fun _ => ⟨hjk, hj0⟩, fun _ => hsum⟩
  · rw [if_neg hij]
    by_cases hik : i = k
    · rw [if_pos hik, hik]
      simp
    · rw [if_neg hik]
      exact ⟨fun h => ⟨hik, h⟩, fun h => h.2⟩

/-- **The simplex reconstruction** (vertices of nonnegative height): the reconstruction residual
`h_P − ∑_j facetSign_j · 𝒯 h_{F_j}` of an `m`-simplex lies in `LSpan m (m − 1)`. -/
theorem simplex_reconstruct_of_nonneg (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v w : Fin m → ℝ) (hvw : dot w v = 1) (hhigh : ∀ i, 0 ≤ dot w (p i)) :
    (fun y => hS (Finset.univ.image p) y -
      ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y) ∈
        LSpan m (m - 1) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [dot] at hvw
  suffices H : ∀ n : ℕ, ∀ (P : Fin (m + 1) → Fin m → ℝ) (hP : AffineIndependent ℝ P),
      (Finset.univ.filter fun i => baryLin P hP v i ≠ 0).card ≤ n →
      (∀ i, 0 ≤ dot w (P i)) →
      (fun y => hS (Finset.univ.image P) y -
        ∑ j, facetSign P hP v j * sweep v w (hS ((Finset.univ.erase j).image P)) y) ∈
          LSpan m (m - 1) by
    exact H _ p hp le_rfl hhigh
  intro n
  induction n with
  | zero =>
    intro P hP hcard _
    exfalso
    obtain ⟨j, hj⟩ := exists_baryLin_ne_zero P hP hv0
    have hpos : 0 < (Finset.univ.filter fun i => baryLin P hP v i ≠ 0).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    have h0 := Nat.le_zero.mp hcard
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  | succ n ih =>
    intro P hP hcard hhighP
    by_cases hpair : ∃ j k, j ≠ k ∧ 0 < baryLin P hP v j * baryLin P hP v k
    · obtain ⟨j, k, hjk, hsame⟩ := hpair
      have hj0 : baryLin P hP v j ≠ 0 := by
        intro h
        rw [h, zero_mul] at hsame
        exact lt_irrefl 0 hsame
      have hk0 : baryLin P hP v k ≠ 0 := by
        intro h
        rw [h, mul_zero] at hsame
        exact lt_irrefl 0 hsame
      have h1 := affineIndependent_ridgeLeft P hP v j k hjk hsame
      have h2 := affineIndependent_ridgeRight P hP v j k hjk hsame
      have hjmem : j ∈ Finset.univ.filter fun i => baryLin P hP v i ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj0⟩
      have hkmem : k ∈ Finset.univ.filter fun i => baryLin P hP v i ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk0⟩
      have hc1 : (Finset.univ.filter fun i =>
          baryLin (Function.update P k (ridgePoint P hP v j k)) h1 v i ≠ 0).card ≤ n := by
        rw [filter_ridgeLeft P hP v hjk hsame h1, Finset.card_erase_of_mem hjmem]
        omega
      have hc2 : (Finset.univ.filter fun i =>
          baryLin (Function.update P j (ridgePoint P hP v j k)) h2 v i ≠ 0).card ≤ n := by
        rw [filter_ridgeRight P hP v hjk hsame h2, Finset.card_erase_of_mem hkmem]
        omega
      have hq := dot_ridgePoint_nonneg P hP v j k w hjk hsame (hhighP j) (hhighP k)
      have hh1 : ∀ i, 0 ≤ dot w (Function.update P k (ridgePoint P hP v j k) i) := by
        intro i
        by_cases hik : i = k
        · rw [hik, Function.update_same]
          exact hq
        · rw [Function.update_noteq hik]
          exact hhighP i
      have hh2 : ∀ i, 0 ≤ dot w (Function.update P j (ridgePoint P hP v j k) i) := by
        intro i
        by_cases hij : i = j
        · rw [hij, Function.update_same]
          exact hq
        · rw [Function.update_noteq hij]
          exact hhighP i
      have hR1 := ih _ h1 hc1 hh1
      have hR2 := ih _ h2 hc2 hh2
      have hsec : hS (insert (ridgePoint P hP v j k) (((Finset.univ.erase j).erase k).image P)) ∈
          LSpan m (m - 1) :=
        hS_mem_LSpan_of_finrank_le (finrank_ridgeSection_le P hP v j k hjk)
      have hsecs : (∑ i in (Finset.univ.erase j).erase k, facetSign P hP v i •
          sweep v w (hS (insert (ridgePoint P hP v j k)
            ((((Finset.univ.erase i).erase j).erase k).image P)))) ∈ LSpan m (m - 1) := by
        refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
        obtain ⟨hij, hik⟩ := ne_ne_of_mem_erase_erase hi
        have hm2 := two_le_of_three_ne hij hik hjk
        have e : m - 1 = m - 2 + 1 := by omega
        rw [e]
        refine sweep_hS_mem_LSpan_of_high v w ?_
          (finrank_ridgeSection_facet_le P hP v j k hij hik hjk)
        intro g hg
        rcases Finset.mem_insert.mp hg with hg | hg
        · rw [hg]
          exact hq
        · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hg
          exact hhighP l
      have hdec : (fun y => hS (Finset.univ.image P) y -
          ∑ l, facetSign P hP v l * sweep v w (hS ((Finset.univ.erase l).image P)) y) =
          (fun y => hS (Finset.univ.image (Function.update P k (ridgePoint P hP v j k))) y -
            ∑ l, facetSign (Function.update P k (ridgePoint P hP v j k)) h1 v l *
              sweep v w (hS ((Finset.univ.erase l).image
                (Function.update P k (ridgePoint P hP v j k)))) y) +
          (fun y => hS (Finset.univ.image (Function.update P j (ridgePoint P hP v j k))) y -
            ∑ l, facetSign (Function.update P j (ridgePoint P hP v j k)) h2 v l *
              sweep v w (hS ((Finset.univ.erase l).image
                (Function.update P j (ridgePoint P hP v j k)))) y) -
          hS (insert (ridgePoint P hP v j k) (((Finset.univ.erase j).erase k).image P)) +
          ∑ i in (Finset.univ.erase j).erase k, facetSign P hP v i •
            sweep v w (hS (insert (ridgePoint P hP v j k)
              ((((Finset.univ.erase i).erase j).erase k).image P))) := by
        funext y
        rw [residual_ridgeCut P hP v j k w hjk hsame h1 h2 y]
        simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hdec]
      exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ hR1 hR2) hsec) hsecs
    · push_neg at hpair
      obtain ⟨a, ha⟩ := exists_baryLin_neg P hP hv0
      obtain ⟨b, hb⟩ := exists_baryLin_pos P hP hv0
      have h0 : ∀ i, i ≠ a → i ≠ b → baryLin P hP v i = 0 := by
        intro i hia hib
        rcases lt_trichotomy (baryLin P hP v i) 0 with h | h | h
        · have := hpair i a hia
          nlinarith
        · exact h
        · have := hpair i b hib
          nlinarith
      exact residual_mem_LSpan_of_column P hP hvw ha hb h0

/-- **The simplex reconstruction** (blueprint statement, M-Reconstruct): for an affinely
independent `p : Fin (m + 1) → ℝ^m`, a direction `v` and a height functional `w` with
`⟨w, v⟩ = 1` and all vertices strictly high,
`h_P − ∑_j facetSign p hp v j · sweep v w (h_{F_j}) ∈ LSpan m (m − 1)`.  (The hypothesis
`1 ≤ m` is implied by `⟨w, v⟩ = 1` and kept only for the blueprint signature.) -/
theorem simplex_reconstruct (_hm : 1 ≤ m) (p : Fin (m + 1) → Fin m → ℝ)
    (hp : AffineIndependent ℝ p) (v w : Fin m → ℝ) (hvw : dot w v = 1)
    (hhigh : ∀ i, 0 < dot w (p i)) :
    (fun y => hS (Finset.univ.image p) y -
      ∑ j, facetSign p hp v j * sweep v w (hS ((Finset.univ.erase j).image p)) y)
      ∈ LSpan m (m - 1) :=
  simplex_reconstruct_of_nonneg p hp v w hvw fun i => (hhigh i).le

end

end MaxNN.ParamidGeom
