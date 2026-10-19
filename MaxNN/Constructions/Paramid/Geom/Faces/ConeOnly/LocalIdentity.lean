import MaxNN.Constructions.Paramid.Geom.Faces.ConeOnly.SimplexGerm
import MaxNN.Constructions.Paramid.Geom.Faces.Cone

/-!
# The local identity at a face of the simplex

Helper of `Geom/Faces/ConeOnly.lean` (module L8 of
`work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md`, Section 4.3, "Local
identity"; S4 Proposition 2.3).

Data: a finite family of paramid cones `Q_j = coneVertsOn (γ j) (V j)`, `j ∈ s`, each of full
dimension `n` (`hfull`), with weights `a j`; `Φ = coneSum s a γ V = ∑_j a_j paramidOn (γ j) (V j)`;
and hypothesis (H): `Φ − h_{Δ^n} ∈ LSpan n (n − 1)`.

Families:

* `coneFamilyUnion s γ V`: all members of the cone families `coneFamily (γ j) (V j)`, `j ∈ s`
  (face-closed, `faceClosed_coneFamilyUnion`);
* `properConeFamily s γ V`: those members other than the cone `Q_j` itself (face-closed,
  `faceClosed_properConeFamily`): the proper cone faces, base faces and apices;
* `properSubsetSpan S`: the span of `hS T` over the nonempty proper subsets `T ⊂ S`.

Main results:

* `germDiff_mem_FSpan_properConeFamily`: a germ difference in a nonzero direction maps
  `FSpan (coneFamilyUnion s γ V)` into `FSpan (properConeFamily s γ V)` (the faces of a
  full-dimensional cone in nonzero directions are proper);
* `iterGermDiff_coneSum_sub_mem` (**local identity**): for a set `S` of `|S| ≥ 2` vertices of
  `Δ^n` and a list `ks` of the other vertices (without repetition),
  `iterGermDiff (ks.map simplexVertDir) Φ − (−1)^|ks| hS S` lies in
  `FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S ⊔ LSpan n 0`;
* `hS_mem_of_ne_simplexVerts`: for `S ≠ Δ^n` (so `ks ≠ []`) this gives
  `hS S ∈ FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S ⊔ LSpan n 0`.

*Proof of the local identity.*  `r = |ks| = n + 1 − |S|` germ differences take (H) into
`LSpan n (|S| − 2)` (`iterGermDiff_mem_LSpan`).  On the simplex they give `(−1)^r hS S` up to a
linear form (`iterGermDiff_simplexVertDir_hS_sub_mem`).  So
`Y = iterGermDiff (ks.map simplexVertDir) Φ − (−1)^r hS S ∈ LSpan n (|S| − 2)`, and `Y` is a
combination of support functions of the face-closed family `coneFamilyUnion s γ V ∪ 𝒫(S)`.
The set `S` is affinely independent, so `U = vectorSpan S` has dimension `|S| − 1`, and the
Face Lemma relative to `U` (`face_lemma_rel`) writes `Y` with faces `face u F`, `⟨u, ·⟩` not
constant on `U`, plus a linear form.  Such a face of a cone-family member is not a cone `Q_j`
(`Q_j` is full-dimensional and `u ≠ 0`); such a face of a subset of `S` is a proper subset of `S`
(its direction space does not contain `U`) (`GSpanRel_union_subsets_le`).
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators FiniteDimensional

noncomputable section

variable {n : ℕ} {ι : Type*}

/-! ## The families -/

/-- All members of the cone families of the cones `j ∈ s`. -/
def coneFamilyUnion (s : Finset ι) (γ : ι → Fin n → ℝ) (V : ι → Finset (Fin n → ℝ)) :
    Set (Finset (Fin n → ℝ)) :=
  {F | ∃ j ∈ s, F ∈ coneFamily (γ j) (V j)}

/-- The members of the cone families of the cones `j ∈ s` other than the cones themselves. -/
def properConeFamily (s : Finset ι) (γ : ι → Fin n → ℝ) (V : ι → Finset (Fin n → ℝ)) :
    Set (Finset (Fin n → ℝ)) :=
  {F | ∃ j ∈ s, F ∈ coneFamily (γ j) (V j) ∧ F ≠ coneVertsOn (γ j) (V j)}

/-- The weighted sum `∑_{j ∈ s} a_j · paramidOn (γ j) (V j)` of the cone units. -/
def coneSum (s : Finset ι) (a : ι → ℝ) (γ : ι → Fin n → ℝ) (V : ι → Finset (Fin n → ℝ)) :
    (Fin n → ℝ) → ℝ :=
  fun y => ∑ j in s, a j * paramidOn (γ j) (V j) y

/-- The span of the support functions of the nonempty proper subsets of `S`. -/
def properSubsetSpan (S : Finset (Fin n → ℝ)) : Submodule ℝ ((Fin n → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ T : Finset (Fin n → ℝ), T ⊂ S ∧ T.Nonempty ∧ f = hS T}

/-! ## Face closure and germs -/

/-- A germ difference keeps a face-closed family's span. -/
theorem germDiff_mem_FSpan {m : ℕ} {𝔉 : Set (Finset (Fin m → ℝ))} (h𝔉 : FaceClosed 𝔉)
    {f : (Fin m → ℝ) → ℝ} (hf : f ∈ FSpan 𝔉) (u : Fin m → ℝ) : germDiff u f ∈ FSpan 𝔉 := by
  rw [germDiff_eq_sub]
  exact Submodule.sub_mem _ (germ_mem_FSpan h𝔉 hf u) (germ_mem_FSpan h𝔉 hf (-u))

/-- Iterated germ differences keep a face-closed family's span. -/
theorem iterGermDiff_mem_FSpan {m : ℕ} {𝔉 : Set (Finset (Fin m → ℝ))} (h𝔉 : FaceClosed 𝔉)
    (us : List (Fin m → ℝ)) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ FSpan 𝔉) :
    iterGermDiff us f ∈ FSpan 𝔉 := by
  induction us generalizing f with
  | nil => exact hf
  | cons u _ ih => exact ih (germDiff_mem_FSpan h𝔉 hf u)

/-- The subsets of `S` form a face-closed family. -/
theorem faceClosed_subsets (S : Finset (Fin n → ℝ)) :
    FaceClosed {T : Finset (Fin n → ℝ) | T ⊆ S} :=
  fun T hT u => (face_subset u T).trans hT

section Cones

variable {s : Finset ι} {γ : ι → Fin n → ℝ} {V : ι → Finset (Fin n → ℝ)}

theorem faceClosed_coneFamilyUnion : FaceClosed (coneFamilyUnion s γ V) := by
  rintro F ⟨j, hj, hF⟩ u
  exact ⟨j, hj, face_mem_coneFamily hF u⟩

/-- A face of a member other than the cone is again not the cone: members are subsets of the
cone's vertex set. -/
theorem faceClosed_properConeFamily : FaceClosed (properConeFamily s γ V) := by
  rintro F ⟨j, hj, hF, hne⟩ u
  refine ⟨j, hj, face_mem_coneFamily hF u, fun h => hne ?_⟩
  refine Finset.Subset.antisymm (subset_coneVertsOn_of_mem_coneFamily hF) ?_
  rw [← h]
  exact face_subset u F

/-- For full-dimensional cones, the face of a cone-family member in a nonzero direction is not
the cone. -/
theorem face_mem_properConeFamily
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    {F : Finset (Fin n → ℝ)} (hF : F ∈ coneFamilyUnion s γ V) {u : Fin n → ℝ} (hu : u ≠ 0) :
    face u F ∈ properConeFamily s γ V := by
  obtain ⟨j, hj, hF⟩ := hF
  refine ⟨j, hj, face_mem_coneFamily hF u, fun h => ?_⟩
  have htop : vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hfull j hj]; simp)
  have h2 : vectorSpan ℝ (face u F : Set (Fin n → ℝ)) = ⊤ := by
    rw [h]
    exact htop
  exact not_le_vectorSpan_face (exists_mem_top_dot_ne_zero_iff.mpr hu) F h2.ge

/-- **Germ differences of the cones.**  For full-dimensional cones, a germ difference in a
nonzero direction maps the span of the cone families into the span of their proper members. -/
theorem germDiff_mem_FSpan_properConeFamily
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    {f : (Fin n → ℝ) → ℝ} (hf : f ∈ FSpan (coneFamilyUnion s γ V)) {u : Fin n → ℝ}
    (hu : u ≠ 0) : germDiff u f ∈ FSpan (properConeFamily s γ V) := by
  have hle : GSpanRel (coneFamilyUnion s γ V) ⊤ ≤ FSpan (properConeFamily s γ V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, hne, u', hu', rfl⟩
    exact hS_mem_FSpan
      (face_mem_properConeFamily hfull hF (exists_mem_top_dot_ne_zero_iff.mp hu'))
      (face_nonempty hne u')
  rw [germDiff_eq_sub]
  exact Submodule.sub_mem _
    (hle (germ_mem_GSpanRel ⊤ hf (exists_mem_top_dot_ne_zero_iff.mpr hu)))
    (hle (germ_mem_GSpanRel ⊤ hf (exists_mem_top_dot_ne_zero_iff.mpr (neg_ne_zero.mpr hu))))

/-- Iterated germ differences along a nonempty list of nonzero directions map the span of the
cone families into the span of their proper members. -/
theorem iterGermDiff_mem_FSpan_properConeFamily
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    {f : (Fin n → ℝ) → ℝ} (hf : f ∈ FSpan (coneFamilyUnion s γ V)) {us : List (Fin n → ℝ)}
    (hus : us ≠ []) (h0 : ∀ u ∈ us, u ≠ 0) :
    iterGermDiff us f ∈ FSpan (properConeFamily s γ V) := by
  cases us with
  | nil => exact absurd rfl hus
  | cons u us =>
    rw [iterGermDiff_cons]
    exact iterGermDiff_mem_FSpan faceClosed_properConeFamily us
      (germDiff_mem_FSpan_properConeFamily hfull hf (h0 u (List.mem_cons_self u us)))

/-- The cone sum is a combination of support functions of the cone families. -/
theorem coneSum_mem_FSpan (a : ι → ℝ) : coneSum s a γ V ∈ FSpan (coneFamilyUnion s γ V) := by
  have e : coneSum s a γ V = ∑ j in s, a j • hS (coneVertsOn (γ j) (V j)) := by
    funext y
    simp only [coneSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hS_coneVertsOn_eq_paramidOn]
  rw [e]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (hS_mem_FSpan ⟨j, hj, coneVertsOn_mem_coneFamily _ _⟩
      (nonempty_of_mem_coneFamily (coneVertsOn_mem_coneFamily _ _)))

/-- **The generators of the relative Face Lemma.**  Relative to `U = vectorSpan S`, the faces of
the cone-family members are proper members, and the faces of the subsets of `S` are proper
subsets of `S`. -/
theorem GSpanRel_union_subsets_le
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    (S : Finset (Fin n → ℝ)) :
    GSpanRel (coneFamilyUnion s γ V ∪ {T | T ⊆ S}) (vectorSpan ℝ (S : Set (Fin n → ℝ))) ≤
      FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨F, hF, hne, u, hu, rfl⟩
  have hu0 : u ≠ 0 := by
    obtain ⟨w, -, hw⟩ := hu
    exact exists_mem_top_dot_ne_zero_iff.mp ⟨w, Submodule.mem_top, hw⟩
  rcases hF with hF | hF
  · exact Submodule.mem_sup_left
      (hS_mem_FSpan (face_mem_properConeFamily hfull hF hu0) (face_nonempty hne u))
  · have hFS : F ⊆ S := hF
    refine Submodule.mem_sup_right
      (Submodule.subset_span ⟨face u F, ?_, face_nonempty hne u, rfl⟩)
    refine Finset.ssubset_iff_subset_ne.mpr ⟨(face_subset u F).trans hFS, fun h => ?_⟩
    have h2 : vectorSpan ℝ (face u F : Set (Fin n → ℝ)) = vectorSpan ℝ (S : Set (Fin n → ℝ)) := by
      rw [h]
    exact not_le_vectorSpan_face hu F h2.ge

/-! ## The local identity -/

/-- **Local identity at a face of `Δ^n`** (PLAN Section 4.3; S4 Proposition 2.3).  Let `S` be a
set of `|S| ≥ 2` vertices of `Δ^n` and `ks` a list of the other vertices, without repetition.
Under (H), the iterated germ difference of the cone sum along `ks` is `(−1)^|ks| hS S` modulo
proper cone-family members, proper subsets of `S`, and linear forms. -/
theorem iterGermDiff_coneSum_sub_mem (a : ι → ℝ)
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    (hH : coneSum s a γ V - hS (simplexVerts n) ∈ LSpan n (n - 1))
    {S : Finset (Fin n → ℝ)} (hSΔ : S ⊆ simplexVerts n) (hS2 : 2 ≤ S.card)
    {ks : List (Fin n → ℝ)} (hnd : ks.Nodup) (hks : ks.toFinset = simplexVerts n \ S) :
    iterGermDiff (ks.map simplexVertDir) (coneSum s a γ V) - (-1 : ℝ) ^ ks.length • hS S ∈
      FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S ⊔ LSpan n 0 := by
  have hcard := card_simplexVerts n
  have hSle : S.card ≤ n + 1 := (Finset.card_le_of_subset hSΔ).trans_eq hcard
  have hlen : ks.length = n + 1 - S.card := by
    rw [← List.toFinset_card_of_nodup hnd, hks, Finset.card_sdiff hSΔ, hcard]
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hΦF := coneSum_mem_FSpan (s := s) (γ := γ) (V := V) a
  have hΦS : coneSum s a γ V ∈ SSpan n := FSpan_le_SSpan _ hΦF
  have hΔS : hS (simplexVerts n) ∈ SSpan n := GermAux.hS_mem_SSpan (Finset.insert_nonempty _ _)
  obtain ⟨C, hC⟩ : ∃ C, C = iterGermDiff (ks.map simplexVertDir) (coneSum s a γ V) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = iterGermDiff (ks.map simplexVertDir) (hS (simplexVerts n)) :=
    ⟨_, rfl⟩
  rw [← hC]
  -- `r = |ks|` germ differences lower the dimension of (H) by `r`
  have hX : C - D ∈ LSpan n (S.card - 2) := by
    rw [hC, hD, ← iterGermDiff_sub hΦS hΔS]
    apply iterGermDiff_mem_LSpan
    rw [List.length_map, hlen, show S.card - 2 + (n + 1 - S.card) = n - 1 by omega]
    exact hH
  -- on the simplex they give `(−1)^r hS S` up to a linear form
  have hset : simplexVerts n \ ks.toFinset = S := by
    rw [hks, Finset.sdiff_sdiff_eq_self hSΔ]
  have hA : D - (-1 : ℝ) ^ ks.length • hS S ∈ LSpan n 0 := by
    have h := iterGermDiff_simplexVertDir_hS_sub_mem ks (simplexVerts n) hnd subset_rfl
      (fun k hk => (Finset.mem_sdiff.mp
        (show k ∈ simplexVerts n \ S by rw [← hks]; exact List.mem_toFinset.mpr hk)).1)
      (by rw [hset]; exact hSne)
    rwa [hset, ← hD] at h
  -- `Y = C − (−1)^r hS S` is low-dimensional ...
  have hYL : C - (-1 : ℝ) ^ ks.length • hS S ∈ LSpan n (S.card - 2) := by
    have e : C - (-1 : ℝ) ^ ks.length • hS S =
        (C - D) + (D - (-1 : ℝ) ^ ks.length • hS S) := by abel
    rw [e]
    exact Submodule.add_mem _ hX (Sweep.LSpan_mono (Nat.zero_le _) hA)
  -- ... and a combination of support functions of a face-closed family
  have hYF : C - (-1 : ℝ) ^ ks.length • hS S ∈
      FSpan (coneFamilyUnion s γ V ∪ {T | T ⊆ S}) := by
    rw [hC]
    exact Submodule.sub_mem _
      (FSpan_mono (Set.subset_union_left _ _)
        (iterGermDiff_mem_FSpan faceClosed_coneFamilyUnion _ hΦF))
      (Submodule.smul_mem _ _ (FSpan_mono (Set.subset_union_right _ _)
        (hS_mem_FSpan (show S ∈ {T : Finset (Fin n → ℝ) | T ⊆ S} from Finset.Subset.refl S)
          hSne)))
  -- the Face Lemma relative to `vectorSpan S`, of dimension `|S| − 1`
  have hrank : finrank ℝ (vectorSpan ℝ (S : Set (Fin n → ℝ))) = S.card - 1 :=
    finrank_vectorSpan_of_subset_simplexVerts hSΔ (by omega)
  have hfl := face_lemma_rel (vectorSpan ℝ (S : Set (Fin n → ℝ))) (by rw [hrank]; omega)
    (FaceClosed.union (faceClosed_coneFamilyUnion (s := s) (γ := γ) (V := V))
      (faceClosed_subsets S)) hYF
    (by rw [hrank, show S.card - 1 - 1 = S.card - 2 by omega]; exact hYL)
  exact sup_le_sup_right (GSpanRel_union_subsets_le hfull S) _ hfl

/-- **Local identity at a proper face of `Δ^n`.**  Under (H), for a set `S ≠ Δ^n` of `|S| ≥ 2`
vertices, `hS S` is a combination of support functions of proper cone-family members and of
proper subsets of `S`, plus a linear form. -/
theorem hS_mem_of_ne_simplexVerts (hn : 1 ≤ n) (a : ι → ℝ)
    (hfull : ∀ j ∈ s,
      finrank ℝ (vectorSpan ℝ (coneVertsOn (γ j) (V j) : Set (Fin n → ℝ))) = n)
    (hH : coneSum s a γ V - hS (simplexVerts n) ∈ LSpan n (n - 1))
    {S : Finset (Fin n → ℝ)} (hSΔ : S ⊆ simplexVerts n) (hS2 : 2 ≤ S.card)
    (hne : S ≠ simplexVerts n) :
    hS S ∈ FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S ⊔ LSpan n 0 := by
  have hloc := iterGermDiff_coneSum_sub_mem a hfull hH hSΔ hS2 (Finset.nodup_toList _)
    (Finset.toList_toFinset _)
  obtain ⟨k, hk⟩ : (simplexVerts n \ S).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => hne (Finset.Subset.antisymm hSΔ h)
  have hC : iterGermDiff ((simplexVerts n \ S).toList.map simplexVertDir) (coneSum s a γ V) ∈
      FSpan (properConeFamily s γ V) := by
    refine iterGermDiff_mem_FSpan_properConeFamily hfull (coneSum_mem_FSpan a) ?_ ?_
    · rw [Ne, List.map_eq_nil]
      exact List.ne_nil_of_mem (Finset.mem_toList.mpr hk)
    · intro u hu
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hu
      exact simplexVertDir_ne_zero hn (Finset.mem_sdiff.mp (Finset.mem_toList.mp hk')).1
  have hM : (-1 : ℝ) ^ (simplexVerts n \ S).toList.length • hS S ∈
      FSpan (properConeFamily s γ V) ⊔ properSubsetSpan S ⊔ LSpan n 0 := by
    have h := Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hC)) hloc
    rwa [sub_sub_cancel] at h
  have e : hS S = (-1 : ℝ) ^ (simplexVerts n \ S).toList.length •
      ((-1 : ℝ) ^ (simplexVerts n \ S).toList.length • hS S) := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hM

end Cones

end

end MaxNN.ParamidGeom.Faces
