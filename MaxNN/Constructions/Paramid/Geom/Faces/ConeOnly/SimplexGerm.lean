import MaxNN.Constructions.Paramid.Geom.Faces
import MaxNN.Constructions.Paramid.Geom.SimplexMod

/-!
# Germ differences of the faces of the standard simplex

Helper of `Geom/Faces/ConeOnly.lean` (module L8 of
`work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md`, Section 4.3, local
identity).  Reduced chart: the vertices of `Δ^n = simplexVerts n` are the origin and the unit
vectors `e_i`; a face of `Δ^n` is a set `T ⊆ simplexVerts n` of vertices, with support function
`hS T`.

* `simplexVertDir p`: for a vertex `p`, a direction whose functional is maximal on the vertices
  exactly at `p` and constant on the other vertices.  It is `e_i` for `p = e_i` (value `1` at
  `e_i`, `0` at the other vertices) and `−(1, …, 1)` for `p = 0` (value `0` at `0`, `−1` at the
  other vertices): `dot_simplexVertDir_self`, `dot_simplexVertDir_of_ne`.
* For a set `T` of vertices containing `k`: `face (simplexVertDir k) T = {k}` and, if `T` has a
  second vertex, `face (−simplexVertDir k) T = T.erase k` (`face_simplexVertDir`,
  `face_neg_simplexVertDir`).  Hence
  `germDiff (simplexVertDir k) (hS T) = ⟨k, ·⟩ − hS (T.erase k)` (`germDiff_simplexVertDir_hS`).
* Iterating along a list `ks` of distinct vertices of `T` that leaves at least one vertex of `T`:
  `iterGermDiff (ks.map simplexVertDir) (hS T) − (−1)^|ks| hS (T ∖ ks)` is a linear form
  (`iterGermDiff_simplexVertDir_hS_sub_mem`).
* `card_simplexVerts`: `Δ^n` has `n + 1` vertices; a set of `k + 1` vertices has affine dimension
  `k` (`finrank_vectorSpan_of_subset_simplexVerts`), by the affine independence of the vertices
  (`KuhnRhoAux.stdVerts_affineIndependent`).

Small generic helpers live in the sub-namespace `ConeOnlyAux`.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional

noncomputable section

variable {n : ℕ}

/-! ## Elementary helpers -/

namespace ConeOnlyAux

/-- The vertices of `Δ^n` are `0` and the unit vectors. -/
theorem mem_simplexVerts_iff {p : Fin n → ℝ} :
    p ∈ simplexVerts n ↔ p = 0 ∨ ∃ i : Fin n, (Pi.single i 1 : Fin n → ℝ) = p := by
  unfold simplexVerts
  rw [Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]

theorem dot_piSingle_one (w : Fin n → ℝ) (i : Fin n) : dot w (Pi.single i 1) = w i := by
  show Matrix.dotProduct w (Pi.single i 1) = w i
  rw [Matrix.dotProduct_single, mul_one]

theorem dot_zero_right (w : Fin n → ℝ) : dot w 0 = 0 := by
  show Matrix.dotProduct w 0 = 0
  exact Matrix.dotProduct_zero w

theorem piSingle_one_ne_zero (i : Fin n) : (Pi.single i 1 : Fin n → ℝ) ≠ 0 := by
  intro h
  have h1 := congr_fun h i
  rw [Pi.single_eq_same, Pi.zero_apply] at h1
  exact one_ne_zero h1

/-- A linear form stays a linear form under iterated germ differences. -/
theorem iterGermDiff_mem_LSpan_zero {m : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : f ∈ LSpan m 0)
    (us : List (Fin m → ℝ)) : iterGermDiff us f ∈ LSpan m 0 := by
  cases us with
  | nil => exact hf
  | cons u us =>
    rw [iterGermDiff_eq_zero_of_mem_LSpan hf (u :: us)
      (by simp only [List.length_cons]; omega)]
    exact Submodule.zero_mem _

end ConeOnlyAux

open ConeOnlyAux

/-! ## The vertex directions -/

/-- For a vertex `p` of `Δ^n`: a direction maximal exactly at `p` among the vertices and
constant on the other vertices, namely `p` itself if `p ≠ 0`, and `−(1, …, 1)` if `p = 0`. -/
def simplexVertDir (p : Fin n → ℝ) : Fin n → ℝ := if p = 0 then fun _ => -1 else p

/-- The common value of `⟨simplexVertDir p, ·⟩` at the vertices other than `p`. -/
def simplexVertLevel (p : Fin n → ℝ) : ℝ := if p = 0 then -1 else 0

theorem simplexVertDir_zero : simplexVertDir (0 : Fin n → ℝ) = fun _ => -1 :=
  if_pos rfl

theorem simplexVertDir_single (i : Fin n) :
    simplexVertDir (Pi.single i 1 : Fin n → ℝ) = Pi.single i 1 :=
  if_neg (piSingle_one_ne_zero i)

theorem simplexVertLevel_zero : simplexVertLevel (0 : Fin n → ℝ) = -1 :=
  if_pos rfl

theorem simplexVertLevel_single (i : Fin n) :
    simplexVertLevel (Pi.single i 1 : Fin n → ℝ) = 0 :=
  if_neg (piSingle_one_ne_zero i)

/-- At its own vertex the functional is one above its level. -/
theorem dot_simplexVertDir_self {p : Fin n → ℝ} (hp : p ∈ simplexVerts n) :
    dot (simplexVertDir p) p = simplexVertLevel p + 1 := by
  rcases mem_simplexVerts_iff.mp hp with rfl | ⟨i, rfl⟩
  · rw [simplexVertDir_zero, simplexVertLevel_zero, dot_zero_right]
    norm_num
  · rw [simplexVertDir_single, simplexVertLevel_single, dot_piSingle_one, Pi.single_eq_same]
    norm_num

/-- At the other vertices the functional takes its level. -/
theorem dot_simplexVertDir_of_ne {p q : Fin n → ℝ} (hp : p ∈ simplexVerts n)
    (hq : q ∈ simplexVerts n) (hqp : q ≠ p) : dot (simplexVertDir p) q = simplexVertLevel p := by
  rcases mem_simplexVerts_iff.mp hp with rfl | ⟨i, rfl⟩
  · rcases mem_simplexVerts_iff.mp hq with rfl | ⟨j, rfl⟩
    · exact absurd rfl hqp
    · rw [simplexVertDir_zero, simplexVertLevel_zero, dot_piSingle_one]
  · rw [simplexVertDir_single, simplexVertLevel_single]
    rcases mem_simplexVerts_iff.mp hq with rfl | ⟨j, rfl⟩
    · exact dot_zero_right _
    · rw [dot_piSingle_one]
      have hji : j ≠ i := fun h => hqp (by rw [h])
      exact Pi.single_eq_of_ne hji 1

theorem simplexVertDir_ne_zero (hn : 1 ≤ n) {p : Fin n → ℝ} (hp : p ∈ simplexVerts n) :
    simplexVertDir p ≠ 0 := by
  rcases mem_simplexVerts_iff.mp hp with rfl | ⟨i, rfl⟩
  · rw [simplexVertDir_zero]
    intro h
    have h1 := congr_fun h ⟨0, hn⟩
    rw [Pi.zero_apply] at h1
    norm_num at h1
  · rw [simplexVertDir_single]
    exact piSingle_one_ne_zero i

/-! ## The two faces in the directions `± simplexVertDir k` -/

/-- The face of a set of vertices containing `k` in direction `simplexVertDir k` is `{k}`. -/
theorem face_simplexVertDir {T : Finset (Fin n → ℝ)} (hT : T ⊆ simplexVerts n)
    {k : Fin n → ℝ} (hk : k ∈ T) : face (simplexVertDir k) T = {k} := by
  have hkΔ := hT hk
  ext p
  rw [mem_face, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hmax⟩
    by_contra hpk
    have h1 := hmax k hk
    rw [dot_simplexVertDir_self hkΔ, dot_simplexVertDir_of_ne hkΔ (hT hp) hpk] at h1
    linarith
  · intro hpk
    rw [hpk]
    refine ⟨hk, fun q hq => ?_⟩
    by_cases hqk : q = k
    · rw [hqk]
    · rw [dot_simplexVertDir_of_ne hkΔ (hT hq) hqk, dot_simplexVertDir_self hkΔ]
      linarith

/-- The face of a set of vertices containing `k` and another vertex in direction
`−simplexVertDir k` is the opposite face `T.erase k`. -/
theorem face_neg_simplexVertDir {T : Finset (Fin n → ℝ)} (hT : T ⊆ simplexVerts n)
    {k : Fin n → ℝ} (hk : k ∈ T) (hne : (T.erase k).Nonempty) :
    face (-simplexVertDir k) T = T.erase k := by
  have hkΔ := hT hk
  ext p
  rw [mem_face, Finset.mem_erase]
  constructor
  · rintro ⟨hp, hmax⟩
    refine ⟨fun hpk => ?_, hp⟩
    obtain ⟨q, hq⟩ := hne
    rw [Finset.mem_erase] at hq
    have h1 := hmax q hq.2
    rw [FlagAux.dot_neg_left, FlagAux.dot_neg_left, hpk, dot_simplexVertDir_self hkΔ,
      dot_simplexVertDir_of_ne hkΔ (hT hq.2) hq.1] at h1
    linarith
  · rintro ⟨hpk, hp⟩
    refine ⟨hp, fun q hq => ?_⟩
    rw [FlagAux.dot_neg_left, FlagAux.dot_neg_left, dot_simplexVertDir_of_ne hkΔ (hT hp) hpk]
    by_cases hqk : q = k
    · rw [hqk, dot_simplexVertDir_self hkΔ]
      linarith
    · rw [dot_simplexVertDir_of_ne hkΔ (hT hq) hqk]

/-- **Facet datum of a face of `Δ^n` at one of its vertices**: the vertex minus the opposite
face. -/
theorem germDiff_simplexVertDir_hS {T : Finset (Fin n → ℝ)} (hT : T ⊆ simplexVerts n)
    {k : Fin n → ℝ} (hk : k ∈ T) (hne : (T.erase k).Nonempty) :
    germDiff (simplexVertDir k) (hS T) = dot k - hS (T.erase k) := by
  rw [germDiff_hS ⟨k, hk⟩, face_simplexVertDir hT hk, face_neg_simplexVertDir hT hk hne,
    GermAux.hS_singleton]

/-! ## Iterated facet data of the faces of `Δ^n` -/

/-- **Iterated facet data of a face of `Δ^n`.**  Along a list `ks` of distinct vertices of `T`
that leaves at least one vertex of `T`, the iterated germ difference of `hS T` is
`(−1)^|ks| hS (T ∖ ks)` up to a linear form. -/
theorem iterGermDiff_simplexVertDir_hS_sub_mem (ks : List (Fin n → ℝ)) :
    ∀ T : Finset (Fin n → ℝ), ks.Nodup → T ⊆ simplexVerts n → (∀ k ∈ ks, k ∈ T) →
      (T \ ks.toFinset).Nonempty →
      iterGermDiff (ks.map simplexVertDir) (hS T) -
          (-1 : ℝ) ^ ks.length • hS (T \ ks.toFinset) ∈ LSpan n 0 := by
  induction ks with
  | nil =>
    intro T _ _ _ _
    rw [List.map_nil, iterGermDiff_nil, List.length_nil, pow_zero, one_smul,
      List.toFinset_nil, Finset.sdiff_empty, sub_self]
    exact Submodule.zero_mem _
  | cons k ks ih =>
    intro T hnd hT hks hne
    rw [List.nodup_cons] at hnd
    have hkT : k ∈ T := hks k (List.mem_cons_self k ks)
    have hset : T \ (k :: ks).toFinset = T.erase k \ ks.toFinset := by
      rw [List.toFinset_cons, Finset.sdiff_insert, Finset.erase_sdiff_comm]
    rw [hset] at hne ⊢
    have hne' : (T.erase k).Nonempty := hne.mono (Finset.sdiff_subset _ _)
    have hIH := ih (T.erase k) hnd.2 ((Finset.erase_subset k T).trans hT)
      (fun k' hk' => Finset.mem_erase.mpr ⟨fun h => hnd.1 (by rw [← h]; exact hk'),
        hks k' (List.mem_cons_of_mem k hk')⟩) hne
    rw [List.map_cons, iterGermDiff_cons, germDiff_simplexVertDir_hS hT hkT hne',
      iterGermDiff_sub (GermAux.dot_mem_SSpan k) (GermAux.hS_mem_SSpan hne'), List.length_cons]
    have h0 := iterGermDiff_mem_LSpan_zero (FlagAux.dot_mem_LSpan k 0) (ks.map simplexVertDir)
    have e : iterGermDiff (ks.map simplexVertDir) (dot k) -
          iterGermDiff (ks.map simplexVertDir) (hS (T.erase k)) -
          (-1 : ℝ) ^ (ks.length + 1) • hS (T.erase k \ ks.toFinset) =
        iterGermDiff (ks.map simplexVertDir) (dot k) -
          (iterGermDiff (ks.map simplexVertDir) (hS (T.erase k)) -
            (-1 : ℝ) ^ ks.length • hS (T.erase k \ ks.toFinset)) := by
      funext y
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.sub_mem _ h0 hIH

/-! ## Counting vertices and dimensions -/

/-- `Δ^n` has `n + 1` vertices. -/
theorem card_simplexVerts (n : ℕ) : (simplexVerts n).card = n + 1 := by
  rw [← KuhnRhoAux.univ_image_stdVerts,
    Finset.card_image_of_injective _ (KuhnRhoAux.stdVerts_affineIndependent n).injective,
    Finset.card_univ, Fintype.card_fin]

/-- A set of `k + 1` vertices of `Δ^n` has affine dimension `k`. -/
theorem finrank_vectorSpan_of_subset_simplexVerts {S : Finset (Fin n → ℝ)}
    (hS : S ⊆ simplexVerts n) {k : ℕ} (hk : S.card = k + 1) :
    finrank ℝ (vectorSpan ℝ (S : Set (Fin n → ℝ))) = k := by
  have hai : AffineIndependent ℝ (fun x => x : ↥(S : Set (Fin n → ℝ)) → (Fin n → ℝ)) := by
    refine (KuhnRhoAux.stdVerts_affineIndependent n).range.mono ?_
    intro p hp
    have hp' : p ∈ Finset.univ.image (KuhnRhoAux.stdVerts n) := by
      rw [KuhnRhoAux.univ_image_stdVerts]
      exact hS hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp'
    exact Set.mem_range_self i
  have h := hai.finrank_vectorSpan (n := k) (by simp [hk])
  rwa [Subtype.range_coe] at h

end

end MaxNN.ParamidGeom.Faces
