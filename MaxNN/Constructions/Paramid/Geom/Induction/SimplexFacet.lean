import MaxNN.Constructions.Paramid.Geom.Flag
import MaxNN.Constructions.Paramid.Geom.Induction.FaceMat

/-!
# Facet data of the standard simplex

Helper `H3b` of `Geom/Induction.lean` (`work/depth2_simplex/lean_core/BLUEPRINT.md`,
section "M-Induction, M-Main").

The vertices of `Δ^{n+1} = simplexVerts (n + 1)` are the real vectors `toR (vtx a)`,
`a : Fin (n + 2)` (`simplexVerts_eq_image`).  Against the outer normal `nu j` of the facet
opposite `vtx j` they take the values `⟨nu j, vtx a⟩ = [j = 0] − [a = j]`
(`dot_nu_toR_vtx`).  Hence

* the face of `Δ^{n+1}` in direction `nu j` is the facet `{vtx a : a ≠ j}` (`face_nu`), the image
  of `Δ^n` under the affine map `p ↦ (faceMat j) p + vtx (j.succAbove 0)`
  (`image_succAbove_eq`, via `latticeMap_vtx` and `toR_latticeMap`), whose support function is
  `y ↦ hS Δ^n ((faceMat j)ᵀ y) + ⟨vtx (j.succAbove 0), y⟩` (`hS_image_affine`);
* the face in direction `−nu j` is the vertex `{vtx j}` (`face_neg_nu`).

A flag functional of length `n ≥ 1` kills the linear term and the vertex, which gives
`flagFun_germDiff_hS_simplexVerts_smul_nu`.  If `u` is not a multiple of any `nu j`, then
`⟨u, ·⟩` is constant on at most `n` of the `n + 2` vertices (`card_face_le`), so both faces in
directions `± u` have affine dimension `≤ n − 1` and are killed:
`flagFun_germDiff_hS_simplexVerts_of_forall_ne`.

Generic helpers live in the sub-namespace `SimplexFacetAux`.
-/

namespace MaxNN.ParamidGeom

open BigOperators Matrix MaxNN.ParamidChain FiniteDimensional

noncomputable section

namespace SimplexFacetAux

/-! ## Real vertices of the standard simplex -/

theorem toR_sub {n : ℕ} (a b : Γ n) : toR (a - b) = toR a - toR b := by
  funext i
  simp [toR]

theorem toR_vtx_zero {n : ℕ} : toR (vtx (0 : Fin (n + 1))) = 0 := by
  funext i
  simp [toR]

theorem toR_vtx_succ {n : ℕ} (i : Fin n) : toR (vtx i.succ) = Pi.single i 1 := by
  funext k
  simp only [toR, vtx_succ]
  by_cases h : k = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem dot_single_one {m : ℕ} (w : Fin m → ℝ) (i : Fin m) : dot w (Pi.single i 1) = w i := by
  show Matrix.dotProduct w (Pi.single i 1) = w i
  rw [Matrix.dotProduct_single, mul_one]

theorem dot_zero_right {m : ℕ} (w : Fin m → ℝ) : dot w 0 = 0 := by
  show Matrix.dotProduct w 0 = 0
  exact Matrix.dotProduct_zero w

theorem dot_toR_vtx_zero {n : ℕ} (w : Fin n → ℝ) : dot w (toR (vtx (0 : Fin (n + 1)))) = 0 := by
  rw [toR_vtx_zero, dot_zero_right]

theorem dot_toR_vtx_succ {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    dot w (toR (vtx i.succ)) = w i := by
  rw [toR_vtx_succ, dot_single_one]

/-- The vertex set of `Δ^n` is the set of real vectors `toR (vtx a)`, `a : Fin (n + 1)`. -/
theorem simplexVerts_eq_image (n : ℕ) :
    simplexVerts n = Finset.univ.image (fun a : Fin (n + 1) => toR (vtx a)) := by
  ext p
  simp only [simplexVerts, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, toR_vtx_zero⟩
    · exact ⟨i.succ, toR_vtx_succ i⟩
  · rintro ⟨a, rfl⟩
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · exact Or.inl toR_vtx_zero
    · exact Or.inr ⟨i, (toR_vtx_succ i).symm⟩

theorem simplexVerts_nonempty (n : ℕ) : (simplexVerts n).Nonempty :=
  Finset.insert_nonempty _ _

/-- Values of the outer facet normals on the vertices: `⟨nu j, vtx a⟩ = [j = 0] − [a = j]`. -/
theorem dot_nu_toR_vtx {n : ℕ} (j a : Fin (n + 2)) :
    dot (nu j) (toR (vtx a)) = (if j = 0 then 1 else 0) - (if a = j then 1 else 0) := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨k, rfl⟩
  · rw [dot_toR_vtx_zero]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · simp
    · simp [Fin.succ_ne_zero i, (Fin.succ_ne_zero i).symm]
  · rw [dot_toR_vtx_succ]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · simp [nu_zero, Fin.succ_ne_zero k]
    · rw [nu_succ, Pi.neg_apply]
      by_cases h : k = i
      · subst h
        simp [Fin.succ_ne_zero k]
      · simp [h, Pi.single_eq_of_ne h, Fin.succ_ne_zero i, Fin.succ_inj]

/-- Membership in a face of `Δ^{n+1}`, in terms of vertex indices. -/
theorem mem_face_simplexVerts {n : ℕ} (w p : Fin (n + 1) → ℝ) :
    p ∈ face w (simplexVerts (n + 1)) ↔
      ∃ a : Fin (n + 2), toR (vtx a) = p ∧
        ∀ b : Fin (n + 2), dot w (toR (vtx b)) ≤ dot w (toR (vtx a)) := by
  rw [mem_face, simplexVerts_eq_image]
  constructor
  · rintro ⟨hp, hmax⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨a, rfl, fun b => hmax _ (Finset.mem_image_of_mem _ (Finset.mem_univ b))⟩
  · rintro ⟨a, rfl, hmax⟩
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ a), fun q hq => ?_⟩
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hq
    exact hmax b

/-! ## The two faces in direction `± nu j` -/

/-- The face of `Δ^{n+1}` in direction `nu j` is the facet opposite `vtx j`. -/
theorem face_nu {n : ℕ} (j : Fin (n + 2)) :
    face (nu j) (simplexVerts (n + 1)) =
      Finset.univ.image (fun b : Fin (n + 1) => toR (vtx (j.succAbove b))) := by
  ext p
  rw [mem_face_simplexVerts, Finset.mem_image]
  constructor
  · rintro ⟨a, rfl, hmax⟩
    have haj : a ≠ j := by
      intro haj
      have h := hmax (j.succAbove 0)
      rw [dot_nu_toR_vtx, dot_nu_toR_vtx, if_neg (Fin.succAbove_ne j 0), if_pos haj] at h
      linarith
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq haj
    exact ⟨b, Finset.mem_univ b, by rw [hb]⟩
  · rintro ⟨b, -, rfl⟩
    refine ⟨j.succAbove b, rfl, fun a => ?_⟩
    rw [dot_nu_toR_vtx, dot_nu_toR_vtx, if_neg (Fin.succAbove_ne j b)]
    split_ifs <;> linarith

/-- The face of `Δ^{n+1}` in direction `−nu j` is the vertex `vtx j`. -/
theorem face_neg_nu {n : ℕ} (j : Fin (n + 2)) :
    face (-(nu j)) (simplexVerts (n + 1)) = {toR (vtx j)} := by
  ext p
  rw [mem_face_simplexVerts, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl, hmax⟩
    have haj : a = j := by
      by_contra haj
      have h := hmax j
      rw [FlagAux.dot_neg_left, FlagAux.dot_neg_left, dot_nu_toR_vtx, dot_nu_toR_vtx, if_pos rfl,
        if_neg haj] at h
      linarith
    rw [haj]
  · rintro rfl
    refine ⟨j, rfl, fun a => ?_⟩
    rw [FlagAux.dot_neg_left, FlagAux.dot_neg_left, dot_nu_toR_vtx, dot_nu_toR_vtx, if_pos rfl]
    split_ifs <;> linarith

/-- The facet opposite `vtx j` is the image of `Δ^n` under
`p ↦ (faceMat j) p + vtx (j.succAbove 0)`. -/
theorem image_succAbove_eq {n : ℕ} (j : Fin (n + 2)) :
    Finset.univ.image (fun b : Fin (n + 1) => toR (vtx (j.succAbove b))) =
      (simplexVerts n).image (fun p => (faceMat j).mulVec p + toR (vtx (j.succAbove 0))) := by
  rw [simplexVerts_eq_image n, Finset.image_image]
  congr 1
  funext b
  show toR (vtx (j.succAbove b)) = (faceMat j).mulVec (toR (vtx b)) + toR (vtx (j.succAbove 0))
  rw [← toR_latticeMap, latticeMap_vtx, toR_sub, sub_add_cancel]

/-- Support function of an affine image: `hS (A S + t) y = hS S (Aᵀ y) + ⟨t, y⟩`. -/
theorem hS_image_affine {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (t : Fin m → ℝ)
    {S : Finset (Fin k → ℝ)} (hne : S.Nonempty) (y : Fin m → ℝ) :
    hS (S.image (fun p => A.mulVec p + t)) y = hS S (Aᵀ.mulVec y) + dot t y := by
  rw [hS_of_nonempty (hne.image _), hS_of_nonempty hne, Finset.sup'_image]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    show dot (A.mulVec p + t) y ≤ _
    rw [SupportCut.dot_add_left, GermAux.dot_mulVec]
    exact add_le_add_right (Finset.le_sup' (fun p => dot p (Aᵀ.mulVec y)) hp) _
  · obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup' hne (fun p => dot p (Aᵀ.mulVec y))
    rw [he]
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup' ((fun p => dot p y) ∘ fun p => A.mulVec p + t) hp)
    show _ = dot (A.mulVec p + t) y
    rw [SupportCut.dot_add_left, GermAux.dot_mulVec]

/-! ## Faces in a direction that is not a facet normal -/

/-- A point set with at most `k + 1` points has affine dimension at most `k`. -/
theorem finrank_vectorSpan_le_of_card_le {m k : ℕ} {F : Finset (Fin m → ℝ)} (hne : F.Nonempty)
    (hk : F.card ≤ k + 1) : finrank ℝ (vectorSpan ℝ (F : Set (Fin m → ℝ))) ≤ k := by
  classical
  have hl : F.card = F.card.pred + 1 := (Nat.succ_pred_eq_of_pos hne.card_pos).symm
  have h := finrank_vectorSpan_image_finset_le ℝ (id : (Fin m → ℝ) → (Fin m → ℝ)) F hl
  rw [Finset.image_id] at h
  exact le_trans h (Nat.pred_le_iff.mpr hk)

/-- If `w` is not a multiple of a facet normal, then `⟨w, ·⟩` attains its maximum on at most `n`
of the `n + 2` vertices of `Δ^{n+1}`. -/
theorem card_face_le {n : ℕ} (w : Fin (n + 1) → ℝ)
    (hw : ∀ (j : Fin (n + 2)) (c : ℝ), w ≠ c • nu j) :
    (face w (simplexVerts (n + 1))).card ≤ n := by
  classical
  -- `T`: the indices of the vertices on which `⟨w, ·⟩` is maximal
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin (n + 2)),
      ∀ a, a ∈ T ↔ ∀ b, dot w (toR (vtx b)) ≤ dot w (toR (vtx a)) :=
    ⟨Finset.univ.filter (fun a => ∀ b, dot w (toR (vtx b)) ≤ dot w (toR (vtx a))),
      fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hsub : face w (simplexVerts (n + 1)) ⊆ T.image (fun a => toR (vtx a)) := by
    intro p hp
    obtain ⟨a, rfl, hmax⟩ := (mem_face_simplexVerts w p).mp hp
    exact Finset.mem_image_of_mem _ ((hT a).mpr hmax)
  refine le_trans (Finset.card_le_of_subset hsub) (le_trans Finset.card_image_le ?_)
  by_contra hcard
  push_neg at hcard
  -- at most one index is missing from `T`
  have key : ∀ a b, a ∉ T → b ∉ T → a = b := by
    intro a b ha hb
    by_contra hab
    have hb' : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
    have hsub2 : T ⊆ (Finset.univ.erase a).erase b := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hb (h ▸ hx),
        Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hx), Finset.mem_univ x⟩⟩
    have h1 := Finset.card_le_of_subset hsub2
    have h2 := Finset.card_erase_add_one hb'
    have h3 := Finset.card_erase_add_one (Finset.mem_univ a)
    rw [Finset.card_univ, Fintype.card_fin] at h3
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 2), ∀ a, a ≠ j → a ∈ T := by
    by_cases h : ∃ j, j ∉ T
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, fun a ha => by_contra fun haT => ha (key a j haT hj)⟩
    · push_neg at h
      exact ⟨0, fun a _ => h a⟩
  have heq : ∀ a b, a ≠ j → b ≠ j → dot w (toR (vtx a)) = dot w (toR (vtx b)) :=
    fun a b ha hb => le_antisymm ((hT b).mp (hj b hb) a) ((hT a).mp (hj a ha) b)
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · apply hw 0 (w 0)
    funext k
    have h := heq k.succ (0 : Fin (n + 1)).succ (Fin.succ_ne_zero k) (Fin.succ_ne_zero 0)
    rw [dot_toR_vtx_succ, dot_toR_vtx_succ] at h
    rw [nu_zero, Pi.smul_apply, smul_eq_mul, mul_one]
    exact h
  · apply hw i.succ (-(w i))
    funext k
    rw [nu_succ, smul_neg, neg_smul, neg_neg, Pi.smul_apply, smul_eq_mul]
    by_cases hki : k = i
    · subst hki
      rw [Pi.single_eq_same, mul_one]
    · have h := heq k.succ 0 (fun h => hki (Fin.succ_injective _ h)) (Fin.succ_ne_zero i).symm
      rw [dot_toR_vtx_succ, dot_toR_vtx_zero] at h
      rw [Pi.single_eq_of_ne hki, mul_zero]
      exact h

end SimplexFacetAux

open SimplexFacetAux

/-! ## The facet data of `hS Δ^{n+1}` under flag functionals -/

/-- **The facet datum of the simplex in a facet-normal direction.**  For `u = c • nu j`
(`c ≠ 0`) and a flag `u :: us` of `ℝ^{n+1}` (`n ≥ 1`), the flag functional `Λ_us` of the facet
datum of `h_{Δ^{n+1}}` in direction `u` is `sign c` times `Λ_us` of the facet opposite `vtx j`,
written as `h_{Δ^n} ∘ (faceMat j)ᵀ`. -/
theorem flagFun_germDiff_hS_simplexVerts_smul_nu {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 2)) (c : ℝ)
    (hc : c ≠ 0) (us : List (Fin (n + 1) → ℝ)) (hflag : IsFlag (c • nu j :: us)) :
    flagFun us (germDiff (c • nu j) (hS (simplexVerts (n + 1)))) =
      ((SignType.sign c : ℤ) : ℝ) *
        flagFun us (fun y => hS (simplexVerts n) ((faceMat j)ᵀ.mulVec y)) := by
  have hlen : us.length = n := Nat.succ.inj hflag.1
  have hus : 1 ≤ us.length := by omega
  have hne := simplexVerts_nonempty (n + 1)
  have hG : (fun y => hS (simplexVerts n) ((faceMat j)ᵀ.mulVec y)) ∈ SSpan (n + 1) :=
    comp_mulVec_mem_SSpan (faceMat j) (GermAux.hS_mem_SSpan (simplexVerts_nonempty n))
  have hfacet : flagFun us (hS (face (nu j) (simplexVerts (n + 1)))) =
      flagFun us (fun y => hS (simplexVerts n) ((faceMat j)ᵀ.mulVec y)) := by
    have e : hS (face (nu j) (simplexVerts (n + 1))) =
        (fun y => hS (simplexVerts n) ((faceMat j)ᵀ.mulVec y)) +
          dot (toR (vtx (j.succAbove 0))) := by
      funext y
      rw [Pi.add_apply, face_nu, image_succAbove_eq,
        hS_image_affine _ _ (simplexVerts_nonempty n)]
    rw [e, flagFun_add_dot hG _ us hus]
  have hvert : flagFun us (hS (face (-(nu j)) (simplexVerts (n + 1)))) = 0 := by
    rw [face_neg_nu, GermAux.hS_singleton]
    exact flagFun_eq_zero_of_mem_LSpan (FlagAux.dot_mem_LSpan _ 0) us hus
  have hSF : ∀ w, hS (face w (simplexVerts (n + 1))) ∈ SSpan (n + 1) :=
    fun w => GermAux.hS_mem_SSpan (face_nonempty hne w)
  rw [germDiff_hS hne, flagFun_sub (hSF _) (hSF _)]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have e1 : face (c • nu j) (simplexVerts (n + 1)) = face (-(nu j)) (simplexVerts (n + 1)) := by
      rw [show c • nu j = (-c) • (-(nu j)) by rw [smul_neg, neg_smul, neg_neg]]
      exact face_smul_of_pos (neg_pos.mpr hneg) _ _
    have e2 : face (-(c • nu j)) (simplexVerts (n + 1)) = face (nu j) (simplexVerts (n + 1)) := by
      rw [← neg_smul]
      exact face_smul_of_pos (neg_pos.mpr hneg) _ _
    rw [e1, e2, hvert, hfacet, sign_neg hneg]
    simp
  · have e1 : face (c • nu j) (simplexVerts (n + 1)) = face (nu j) (simplexVerts (n + 1)) :=
      face_smul_of_pos hpos _ _
    have e2 : face (-(c • nu j)) (simplexVerts (n + 1)) =
        face (-(nu j)) (simplexVerts (n + 1)) := by
      rw [← smul_neg]
      exact face_smul_of_pos hpos _ _
    rw [e1, e2, hvert, hfacet, sign_pos hpos]
    simp

/-- **The facet datum of the simplex in a generic direction.**  If `u` is not a multiple of any
facet normal `nu j`, every flag functional `Λ_us` with `u :: us` a flag of `ℝ^{n+1}` (`n ≥ 1`)
kills the facet datum of `h_{Δ^{n+1}}` in direction `u`: both faces have at most `n` vertices,
hence affine dimension `≤ n − 1`. -/
theorem flagFun_germDiff_hS_simplexVerts_of_forall_ne {n : ℕ} (hn : 1 ≤ n) (u : Fin (n + 1) → ℝ)
    (hu : ∀ (j : Fin (n + 2)) (c : ℝ), u ≠ c • nu j) (us : List (Fin (n + 1) → ℝ))
    (hflag : IsFlag (u :: us)) :
    flagFun us (germDiff u (hS (simplexVerts (n + 1)))) = 0 := by
  have hlen : us.length = n := Nat.succ.inj hflag.1
  have hneg : ∀ (j : Fin (n + 2)) (c : ℝ), -u ≠ c • nu j := by
    intro j c h
    apply hu j (-c)
    rw [neg_smul, ← h, neg_neg]
  have hne := simplexVerts_nonempty (n + 1)
  have hmem : ∀ w : Fin (n + 1) → ℝ, (∀ (j : Fin (n + 2)) (c : ℝ), w ≠ c • nu j) →
      hS (face w (simplexVerts (n + 1))) ∈ LSpan (n + 1) (n - 1) := by
    intro w hw
    refine FlagAux.hS_mem_LSpan (face_nonempty hne w) ?_
    exact finrank_vectorSpan_le_of_card_le (face_nonempty hne w)
      (le_trans (card_face_le w hw) (Nat.sub_add_cancel hn).ge)
  rw [germDiff_hS hne u]
  exact flagFun_eq_zero_of_mem_LSpan (Submodule.sub_mem _ (hmem u hu) (hmem (-u) hneg)) us
    (by omega)

end

end MaxNN.ParamidGeom
