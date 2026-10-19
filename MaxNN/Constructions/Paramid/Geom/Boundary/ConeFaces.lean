import MaxNN.Constructions.Paramid.Geom.Defs

/-!
# Faces of a paramid cone

Helper of `Geom/Boundary.lean` (module `M-Boundary` of
`work/depth2_simplex/lean_core/BLUEPRINT.md`).  For a direction `u`, an apex offset `γ` and a
finite label set `V` in `ℝ^m`, write

* `a = ⟨u, γ⟩`, `b v = ⟨u, v⟩`, `A = a + ∑_{v ∈ V} relu (b v)`,
* `P = {v ∈ V | 0 < b v}`, `Z = {v ∈ V | b v = 0}`.

Over the vertex set `coneVertsOn γ V = {0} ∪ {γ + ∑_{v ∈ I} v | I ⊆ V}`, the functional `⟨u, ·⟩`
takes the value `0` at `0` and its maximum `A` over the parallelepiped exactly at the points
`γ + ∑_P v + ∑_J v` with `J ⊆ Z`.  Hence the face of the cone in direction `u` is

* `{0}` if `A < 0` (`face_coneVertsOn_of_neg`);
* the parallelepiped vertex set `{γ + ∑_P v + ∑_J v | J ⊆ Z}` if `0 < A`
  (`face_coneVertsOn_of_pos`);
* the cone `coneVertsOn (γ + ∑_P v) Z` if `A = 0` (`face_coneVertsOn_of_eq_zero`).

Consequences: dimension bounds (`0`, `≤ |Z|`, `≤ |Z| + 1`), the support functions of the three
faces (`hS_face_coneVertsOn`: `0`, `⟨γ + ∑_P v, ·⟩ + ∑_{v ∈ Z} relu ⟨v, ·⟩`, and
`paramidOn (γ + ∑_P v) Z`), the parallelepiped face in `LSpan m 1` (a point plus segments), and
the facet identification used by the boundary formula: if exactly one label `v₀` is not
orthogonal to `u` and `A = 0`, the face is the cone over `V ∖ {v₀}` with offset `γ + v₀`
(`⟨u, v₀⟩ > 0`) or `γ` (`⟨u, v₀⟩ < 0`) — the two boundary terms `[γ + v₀; L ∖ v₀]`,
`[γ; L ∖ v₀]` of `d [γ; L]` (`face_coneVertsOn_of_single_pos`, `face_coneVertsOn_of_single_neg`).
If `γ` and every label are orthogonal to `u`, the face is the whole cone
(`face_coneVertsOn_of_forall_orth`); if every label is orthogonal to `u` and `⟨u, γ⟩ > 0`, it is
the base parallelepiped (`face_coneVertsOn_of_forall_orth_of_pos`).

Sign convention for the boundary formula (exact computation,
`work/depth2_simplex/lean_core/signs/SIGN_CONVENTION.md`): the realization relative to a frame
`[u₁, …, u_r]` must use `sign det [u₁, …, u_r, v₁, …, v_k, γ]` (frame first), and the chain must
be supported on generators orthogonal to the frame.

Linearity of `dot` and the elementary facts about `coneVertsOn` are private helpers (prefix
`cf_`), so that this file does not clash with `Geom/Germ.lean` or `Geom/Doubling.lean`.
-/

namespace MaxNN.ParamidGeom

open BigOperators FiniteDimensional

variable {m : ℕ}

/-! ## Private helpers: linearity of `dot`, membership in faces and cones -/

private theorem cf_dot_add_right (u p q : Fin m → ℝ) : dot u (p + q) = dot u p + dot u q := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, mul_add]

private theorem cf_dot_add_left (p q y : Fin m → ℝ) : dot (p + q) y = dot p y + dot q y := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

private theorem cf_dot_zero_right (u : Fin m → ℝ) : dot u 0 = 0 := by
  unfold dot
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.zero_apply, mul_zero]

private theorem cf_dot_zero_left (y : Fin m → ℝ) : dot 0 y = 0 := by
  unfold dot
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.zero_apply, zero_mul]

private theorem cf_dot_sum_right {ι : Type*} (u : Fin m → ℝ) (s : Finset ι) (p : ι → Fin m → ℝ) :
    dot u (∑ i in s, p i) = ∑ i in s, dot u (p i) := by
  unfold dot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum]

private theorem cf_dot_sum_left {ι : Type*} (s : Finset ι) (p : ι → Fin m → ℝ) (y : Fin m → ℝ) :
    dot (∑ i in s, p i) y = ∑ i in s, dot (p i) y := by
  unfold dot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_apply, Finset.sum_mul]

private theorem cf_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ face u S ↔ p ∈ S ∧ ∀ q ∈ S, dot u q ≤ dot u p :=
  @Finset.mem_filter _ _ (Classical.decPred _) _ _

private theorem cf_mem_coneVertsOn {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ coneVertsOn γ V ↔ p = 0 ∨ ∃ I, I ⊆ V ∧ γ + ∑ v in I, v = p := by
  unfold coneVertsOn
  rw [Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_powerset]

/-- `∑_{v ∈ V} relu ⟨u, v⟩ = ∑_{v ∈ P} ⟨u, v⟩`. -/
private theorem cf_sum_relu_eq (u : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    ∑ v in V, relu (dot u v) = ∑ v in V.filter (fun v => 0 < dot u v), dot u v := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : 0 < dot u v
  · rw [if_pos h, relu_of_nonneg h.le]
  · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]

/-- Every parallelepiped vertex has `⟨u, ·⟩ ≤ A`. -/
private theorem cf_dot_vertex_le (u γ : Fin m → ℝ) {V I : Finset (Fin m → ℝ)} (hI : I ⊆ V) :
    dot u (γ + ∑ v in I, v) ≤ dot u γ + ∑ v in V, relu (dot u v) := by
  rw [cf_dot_add_right, cf_dot_sum_right]
  apply add_le_add_left
  calc ∑ v in I, dot u v ≤ ∑ v in I, relu (dot u v) :=
        Finset.sum_le_sum fun v _ => le_max_right 0 _
    _ ≤ ∑ v in V, relu (dot u v) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI fun v _ _ => relu_nonneg _

/-- The points `γ + ∑_P v + ∑_J v` (`J ⊆ Z`) have `⟨u, ·⟩ = A`. -/
private theorem cf_dot_top (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) {J : Finset (Fin m → ℝ)}
    (hJ : J ⊆ V.filter (fun v => dot u v = 0)) :
    dot u (γ + ∑ v in V.filter (fun v => 0 < dot u v), v + ∑ v in J, v) =
      dot u γ + ∑ v in V, relu (dot u v) := by
  rw [cf_dot_add_right, cf_dot_add_right, cf_dot_sum_right, cf_dot_sum_right, cf_sum_relu_eq]
  have h0 : ∑ v in J, dot u v = 0 :=
    Finset.sum_eq_zero fun v hv => (Finset.mem_filter.mp (hJ hv)).2
  rw [h0, add_zero]

/-- The points `γ + ∑_P v + ∑_J v` (`J ⊆ Z`) are vertices of the cone. -/
private theorem cf_top_mem (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) {J : Finset (Fin m → ℝ)}
    (hJ : J ⊆ V.filter (fun v => dot u v = 0)) :
    γ + ∑ v in V.filter (fun v => 0 < dot u v), v + ∑ v in J, v ∈ coneVertsOn γ V := by
  have hdisj : Disjoint (V.filter (fun v => 0 < dot u v)) J := by
    rw [Finset.disjoint_left]
    intro v hvP hvJ
    have h1 := (Finset.mem_filter.mp hvP).2
    have h2 := (Finset.mem_filter.mp (hJ hvJ)).2
    rw [h2] at h1
    exact lt_irrefl 0 h1
  refine cf_mem_coneVertsOn.mpr (Or.inr ⟨V.filter (fun v => 0 < dot u v) ∪ J, ?_, ?_⟩)
  · exact Finset.union_subset (Finset.filter_subset _ _)
      (fun v hv => (Finset.mem_filter.mp (hJ hv)).1)
  · rw [Finset.sum_union hdisj, add_assoc]

/-- A parallelepiped vertex attaining `A` is of the form `γ + ∑_P v + ∑_J v` with `J ⊆ Z`. -/
private theorem cf_eq_top (u γ : Fin m → ℝ) {V I : Finset (Fin m → ℝ)} (hI : I ⊆ V)
    (h : dot u (γ + ∑ v in I, v) = dot u γ + ∑ v in V, relu (dot u v)) :
    ∃ J, J ⊆ V.filter (fun v => dot u v = 0) ∧
      γ + ∑ v in I, v = γ + ∑ v in V.filter (fun v => 0 < dot u v), v + ∑ v in J, v := by
  rw [cf_dot_add_right, cf_dot_sum_right, add_right_inj] at h
  have hsplit : ∑ v in V \ I, relu (dot u v) + ∑ v in I, relu (dot u v) =
      ∑ v in V, relu (dot u v) := Finset.sum_sdiff hI
  have hdiff : ∑ v in I, (relu (dot u v) - dot u v) =
      ∑ v in I, relu (dot u v) - ∑ v in I, dot u v := Finset.sum_sub_distrib
  have hn1 : 0 ≤ ∑ v in V \ I, relu (dot u v) := Finset.sum_nonneg fun v _ => relu_nonneg _
  have hn2 : 0 ≤ ∑ v in I, (relu (dot u v) - dot u v) :=
    Finset.sum_nonneg fun v _ => sub_nonneg.mpr (le_max_right 0 _)
  have e1 : ∑ v in V \ I, relu (dot u v) = 0 := by linarith
  have e2 : ∑ v in I, (relu (dot u v) - dot u v) = 0 := by linarith
  have hout : ∀ v ∈ V, v ∉ I → dot u v ≤ 0 := by
    intro v hv hvI
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => relu_nonneg (dot u w))).mp e1 v
      (Finset.mem_sdiff.mpr ⟨hv, hvI⟩)
    have hle : dot u v ≤ relu (dot u v) := le_max_right 0 _
    linarith
  have hin : ∀ v ∈ I, 0 ≤ dot u v := by
    intro v hv
    have h0 : relu (dot u v) - dot u v = 0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => sub_nonneg.mpr (le_max_right 0 (dot u w)))).mp e2 v hv
    have hnn : 0 ≤ relu (dot u v) := relu_nonneg _
    linarith
  refine ⟨I.filter (fun v => dot u v = 0), ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨hI hv.1, hv.2⟩
  · rw [add_assoc]
    congr 1
    have hP : I.filter (fun v => 0 < dot u v) = V.filter (fun v => 0 < dot u v) := by
      ext v
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hI h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hvI
        have h3 := hout v h1 hvI
        linarith
    have hZ : I.filter (fun v => ¬ 0 < dot u v) = I.filter (fun v => dot u v = 0) := by
      refine Finset.filter_congr fun v hv => ?_
      constructor
      · intro h3
        exact le_antisymm (not_lt.mp h3) (hin v hv)
      · intro h3
        rw [h3]
        exact lt_irrefl 0
    rw [← Finset.sum_filter_add_sum_filter_not I (fun v => 0 < dot u v), hP, hZ]

/-! ## The three faces -/

/-- **Face of a cone, `A < 0`**: the apex `0` alone. -/
theorem face_coneVertsOn_of_neg (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : dot u γ + ∑ v in V, relu (dot u v) < 0) :
    face u (coneVertsOn γ V) = {0} := by
  ext p
  rw [cf_mem_face, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hmax⟩
    rcases cf_mem_coneVertsOn.mp hp with h | ⟨I, hI, rfl⟩
    · exact h
    · exfalso
      have h0 := hmax 0 (cf_mem_coneVertsOn.mpr (Or.inl rfl))
      rw [cf_dot_zero_right] at h0
      have h1 := cf_dot_vertex_le u γ hI
      linarith
  · rintro rfl
    refine ⟨cf_mem_coneVertsOn.mpr (Or.inl rfl), fun q hq => ?_⟩
    rw [cf_dot_zero_right]
    rcases cf_mem_coneVertsOn.mp hq with h | ⟨I, hI, rfl⟩
    · rw [h, cf_dot_zero_right]
    · have h1 := cf_dot_vertex_le u γ hI
      linarith

/-- **Face of a cone, `0 < A`**: the parallelepiped face `{γ + ∑_P v + ∑_J v | J ⊆ Z}` of the
base. -/
theorem face_coneVertsOn_of_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : 0 < dot u γ + ∑ v in V, relu (dot u v)) :
    face u (coneVertsOn γ V) =
      (V.filter (fun v => dot u v = 0)).powerset.image
        (fun J => γ + ∑ v in V.filter (fun v => 0 < dot u v), v + ∑ v in J, v) := by
  ext p
  rw [cf_mem_face, Finset.mem_image]
  constructor
  · rintro ⟨hp, hmax⟩
    have htop := hmax _ (cf_top_mem u γ V (Finset.empty_subset _))
    rw [cf_dot_top u γ V (Finset.empty_subset _)] at htop
    rcases cf_mem_coneVertsOn.mp hp with h | ⟨I, hI, rfl⟩
    · rw [h, cf_dot_zero_right] at htop
      linarith
    · have hle := cf_dot_vertex_le u γ hI
      obtain ⟨J, hJ, hEq⟩ := cf_eq_top u γ hI (le_antisymm hle htop)
      exact ⟨J, Finset.mem_powerset.mpr hJ, hEq.symm⟩
  · rintro ⟨J, hJ, rfl⟩
    have hJ' := Finset.mem_powerset.mp hJ
    refine ⟨cf_top_mem u γ V hJ', fun q hq => ?_⟩
    rw [cf_dot_top u γ V hJ']
    rcases cf_mem_coneVertsOn.mp hq with h | ⟨I, hI, rfl⟩
    · rw [h, cf_dot_zero_right]
      exact hA.le
    · exact cf_dot_vertex_le u γ hI

/-- **Face of a cone, `A = 0`**: the cone over the parallelepiped face,
`coneVertsOn (γ + ∑_P v) Z`. -/
theorem face_coneVertsOn_of_eq_zero (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : dot u γ + ∑ v in V, relu (dot u v) = 0) :
    face u (coneVertsOn γ V) =
      coneVertsOn (γ + ∑ v in V.filter (fun v => 0 < dot u v), v)
        (V.filter (fun v => dot u v = 0)) := by
  ext p
  rw [cf_mem_face]
  constructor
  · rintro ⟨hp, hmax⟩
    refine cf_mem_coneVertsOn.mpr ?_
    rcases cf_mem_coneVertsOn.mp hp with h | ⟨I, hI, rfl⟩
    · exact Or.inl h
    · right
      have htop := hmax _ (cf_top_mem u γ V (Finset.empty_subset _))
      rw [cf_dot_top u γ V (Finset.empty_subset _)] at htop
      have hle := cf_dot_vertex_le u γ hI
      obtain ⟨J, hJ, hEq⟩ := cf_eq_top u γ hI (le_antisymm hle htop)
      exact ⟨J, hJ, hEq.symm⟩
  · intro hp
    rcases cf_mem_coneVertsOn.mp hp with h | ⟨J, hJ, rfl⟩
    · subst h
      refine ⟨cf_mem_coneVertsOn.mpr (Or.inl rfl), fun q hq => ?_⟩
      rw [cf_dot_zero_right]
      rcases cf_mem_coneVertsOn.mp hq with h | ⟨I, hI, rfl⟩
      · rw [h, cf_dot_zero_right]
      · have h1 := cf_dot_vertex_le u γ hI
        linarith
    · refine ⟨cf_top_mem u γ V hJ, fun q hq => ?_⟩
      rw [cf_dot_top u γ V hJ]
      rcases cf_mem_coneVertsOn.mp hq with h | ⟨I, hI, rfl⟩
      · rw [h, cf_dot_zero_right]
        exact hA.ge
      · exact cf_dot_vertex_le u γ hI

/-! ## Dimensions of the faces -/

private theorem cf_vectorSpan_image_le (c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    vectorSpan ℝ ((Z.powerset.image (fun J => c + ∑ v in J, v) : Finset (Fin m → ℝ)) :
      Set (Fin m → ℝ)) ≤ Submodule.span ℝ (Z : Set (Fin m → ℝ)) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro x ⟨p, q, hp, hq, rfl⟩
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
  obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
  have h : (c + ∑ v in J, v) - (c + ∑ v in J', v) ∈ Submodule.span ℝ (Z : Set (Fin m → ℝ)) := by
    have e : (c + ∑ v in J, v) - (c + ∑ v in J', v) = ∑ v in J, v - ∑ v in J', v := by abel
    rw [e]
    exact Submodule.sub_mem _
      (Submodule.sum_mem _ fun v hv => Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_powerset.mp hJ hv)))
      (Submodule.sum_mem _ fun v hv => Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_powerset.mp hJ' hv)))
  exact h

private theorem cf_finrank_image_le (c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ ((Z.powerset.image (fun J => c + ∑ v in J, v) :
      Finset (Fin m → ℝ)) : Set (Fin m → ℝ))) ≤ Z.card :=
  le_trans (Submodule.finrank_mono (cf_vectorSpan_image_le c Z))
    (finrank_span_finset_le_card (K := ℝ) Z)

private theorem cf_vectorSpan_coneVertsOn_le (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ)) ≤
      Submodule.span ℝ ((insert γ V : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
  have hmem : ∀ r ∈ coneVertsOn γ V,
      r ∈ Submodule.span ℝ ((insert γ V : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
    intro r hr
    rcases cf_mem_coneVertsOn.mp hr with h | ⟨I, hI, rfl⟩
    · rw [h]
      exact Submodule.zero_mem _
    · refine Submodule.add_mem _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self γ V))) ?_
      exact Submodule.sum_mem _ fun v hv => Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hI hv)))
  rw [vectorSpan_def, Submodule.span_le]
  rintro x ⟨p, q, hp, hq, rfl⟩
  have h : p - q ∈ Submodule.span ℝ ((insert γ V : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    Submodule.sub_mem _ (hmem p (Finset.mem_coe.mp hp)) (hmem q (Finset.mem_coe.mp hq))
  exact h

private theorem cf_finrank_coneVertsOn_le (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ (coneVertsOn γ V : Set (Fin m → ℝ))) ≤ V.card + 1 :=
  le_trans (Submodule.finrank_mono (cf_vectorSpan_coneVertsOn_le γ V))
    (le_trans (finrank_span_finset_le_card (K := ℝ) (insert γ V)) (Finset.card_insert_le γ V))

/-- `A < 0`: the face is a point. -/
theorem finrank_vectorSpan_face_coneVertsOn_of_neg (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : dot u γ + ∑ v in V, relu (dot u v) < 0) :
    finrank ℝ (vectorSpan ℝ (face u (coneVertsOn γ V) : Set (Fin m → ℝ))) = 0 := by
  rw [face_coneVertsOn_of_neg u γ V hA, Finset.coe_singleton, vectorSpan_singleton, finrank_bot]

/-- `0 < A`: the parallelepiped face has dimension at most `|Z|`. -/
theorem finrank_vectorSpan_face_coneVertsOn_of_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : 0 < dot u γ + ∑ v in V, relu (dot u v)) :
    finrank ℝ (vectorSpan ℝ (face u (coneVertsOn γ V) : Set (Fin m → ℝ))) ≤
      (V.filter (fun v => dot u v = 0)).card := by
  rw [face_coneVertsOn_of_pos u γ V hA]
  exact cf_finrank_image_le _ _

/-- `A = 0`: the cone face has dimension at most `|Z| + 1`. -/
theorem finrank_vectorSpan_face_coneVertsOn_of_eq_zero (u γ : Fin m → ℝ)
    (V : Finset (Fin m → ℝ)) (hA : dot u γ + ∑ v in V, relu (dot u v) = 0) :
    finrank ℝ (vectorSpan ℝ (face u (coneVertsOn γ V) : Set (Fin m → ℝ))) ≤
      (V.filter (fun v => dot u v = 0)).card + 1 := by
  rw [face_coneVertsOn_of_eq_zero u γ V hA]
  exact cf_finrank_coneVertsOn_le _ _

/-- In every case the face has dimension at most `|Z| + 1`. -/
theorem finrank_vectorSpan_face_coneVertsOn_le (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ (face u (coneVertsOn γ V) : Set (Fin m → ℝ))) ≤
      (V.filter (fun v => dot u v = 0)).card + 1 := by
  rcases lt_trichotomy (dot u γ + ∑ v in V, relu (dot u v)) 0 with h | h | h
  · rw [finrank_vectorSpan_face_coneVertsOn_of_neg u γ V h]
    exact Nat.zero_le _
  · exact finrank_vectorSpan_face_coneVertsOn_of_eq_zero u γ V h
  · exact le_trans (finrank_vectorSpan_face_coneVertsOn_of_pos u γ V h) (Nat.le_succ _)

/-! ## Support functions of the faces -/

/-- Support function of the parallelepiped vertex set `{c + ∑_{v ∈ J} v | J ⊆ Z}`:
`⟨c, y⟩ + ∑_{v ∈ Z} relu ⟨v, y⟩`. -/
theorem hS_powerset_image_add_sum (c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    hS (Z.powerset.image (fun J => c + ∑ v in J, v)) =
      fun y => dot c y + ∑ v in Z, relu (dot v y) := by
  funext y
  have hne : (Z.powerset.image (fun J => c + ∑ v in J, v)).Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.empty_mem_powerset Z)⟩
  rw [hS_of_nonempty hne y]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hp
    rw [cf_dot_add_left, cf_dot_sum_left]
    apply add_le_add_left
    calc ∑ v in J, dot v y ≤ ∑ v in J, relu (dot v y) :=
          Finset.sum_le_sum fun v _ => le_max_right 0 _
      _ ≤ ∑ v in Z, relu (dot v y) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.mem_powerset.mp hJ)
            fun v _ _ => relu_nonneg _
  · have hJ : Z.filter (fun v => 0 < dot v y) ∈ Z.powerset :=
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    have hmem := Finset.mem_image_of_mem (fun J => c + ∑ v in J, v) hJ
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun p => dot p y) hmem)
    show dot c y + ∑ v in Z, relu (dot v y) =
      dot (c + ∑ v in Z.filter (fun v => 0 < dot v y), v) y
    rw [cf_dot_add_left, cf_dot_sum_left, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : 0 < dot v y
    · rw [if_pos h, relu_of_nonneg h.le]
    · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]

/-- The support function of a cone vertex set is the paramid unit. -/
theorem hS_coneVertsOn_eq_paramidOn (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    hS (coneVertsOn γ V) = paramidOn γ V := by
  funext y
  have hne : (coneVertsOn γ V).Nonempty := ⟨0, cf_mem_coneVertsOn.mpr (Or.inl rfl)⟩
  rw [hS_of_nonempty hne y]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    rcases cf_mem_coneVertsOn.mp hp with h | ⟨I, hI, rfl⟩
    · rw [h, cf_dot_zero_left]
      exact relu_nonneg _
    · rw [cf_dot_add_left, cf_dot_sum_left]
      refine le_trans ?_ (le_max_right 0 _)
      apply add_le_add_left
      calc ∑ v in I, dot v y ≤ ∑ v in I, relu (dot v y) :=
            Finset.sum_le_sum fun v _ => le_max_right 0 _
        _ ≤ ∑ v in V, relu (dot v y) :=
            Finset.sum_le_sum_of_subset_of_nonneg hI fun v _ _ => relu_nonneg _
  · refine max_le ?_ ?_
    · have h0 : (0 : Fin m → ℝ) ∈ coneVertsOn γ V := cf_mem_coneVertsOn.mpr (Or.inl rfl)
      calc (0 : ℝ) = dot 0 y := (cf_dot_zero_left y).symm
        _ ≤ _ := Finset.le_sup' (fun p => dot p y) h0
    · have hI : γ + ∑ v in V.filter (fun v => 0 < dot v y), v ∈ coneVertsOn γ V :=
        cf_mem_coneVertsOn.mpr (Or.inr ⟨_, Finset.filter_subset _ _, rfl⟩)
      have hval : dot (γ + ∑ v in V.filter (fun v => 0 < dot v y), v) y =
          dot γ y + ∑ v in V, relu (dot v y) := by
        rw [cf_dot_add_left, cf_dot_sum_left, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : 0 < dot v y
        · rw [if_pos h, relu_of_nonneg h.le]
        · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]
      rw [← hval]
      exact Finset.le_sup' (fun p => dot p y) hI

/-- `A < 0`: the face `{0}` has support function `0`. -/
theorem hS_face_coneVertsOn_of_neg (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : dot u γ + ∑ v in V, relu (dot u v) < 0) :
    hS (face u (coneVertsOn γ V)) = 0 := by
  rw [face_coneVertsOn_of_neg u γ V hA]
  funext y
  rw [hS_of_nonempty (Finset.singleton_nonempty 0) y, Finset.sup'_singleton, cf_dot_zero_left,
    Pi.zero_apply]

/-- `0 < A`: the parallelepiped face has support function
`⟨γ + ∑_P v, ·⟩ + ∑_{v ∈ Z} relu ⟨v, ·⟩`. -/
theorem hS_face_coneVertsOn_of_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : 0 < dot u γ + ∑ v in V, relu (dot u v)) :
    hS (face u (coneVertsOn γ V)) =
      fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot u v), v) y +
        ∑ v in V.filter (fun v => dot u v = 0), relu (dot v y) := by
  rw [face_coneVertsOn_of_pos u γ V hA, hS_powerset_image_add_sum]

/-- `A = 0`: the cone face has support function `paramidOn (γ + ∑_P v) Z`. -/
theorem hS_face_coneVertsOn_of_eq_zero (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : dot u γ + ∑ v in V, relu (dot u v) = 0) :
    hS (face u (coneVertsOn γ V)) =
      paramidOn (γ + ∑ v in V.filter (fun v => 0 < dot u v), v)
        (V.filter (fun v => dot u v = 0)) := by
  rw [face_coneVertsOn_of_eq_zero u γ V hA, hS_coneVertsOn_eq_paramidOn]

/-- **Support function of the face of a cone, all three cases** (the germ of `paramidOn γ V` in
direction `u`): with `A = ⟨u, γ⟩ + ∑_{v ∈ V} relu ⟨u, v⟩`, `P = {0 < ⟨u, ·⟩}`, `Z = {⟨u, ·⟩ = 0}`,
`hS (face u (coneVertsOn γ V))` is `0` if `A < 0`, `⟨γ + ∑_P v, ·⟩ + ∑_{v ∈ Z} relu ⟨v, ·⟩` if
`0 < A`, and `paramidOn (γ + ∑_P v) Z` if `A = 0`. -/
theorem hS_face_coneVertsOn (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    hS (face u (coneVertsOn γ V)) =
      if dot u γ + ∑ v in V, relu (dot u v) < 0 then 0
      else if 0 < dot u γ + ∑ v in V, relu (dot u v) then
        fun y => dot (γ + ∑ v in V.filter (fun v => 0 < dot u v), v) y +
          ∑ v in V.filter (fun v => dot u v = 0), relu (dot v y)
      else paramidOn (γ + ∑ v in V.filter (fun v => 0 < dot u v), v)
        (V.filter (fun v => dot u v = 0)) := by
  split_ifs with h1 h2
  · exact hS_face_coneVertsOn_of_neg u γ V h1
  · exact hS_face_coneVertsOn_of_pos u γ V h2
  · exact hS_face_coneVertsOn_of_eq_zero u γ V (le_antisymm (not_lt.mp h2) (not_lt.mp h1))

/-! ## The parallelepiped face is a point plus segments: `LSpan m 1` -/

/-- `relu ⟨v, ·⟩` is the support function of the segment `{0, v}`. -/
private theorem cf_relu_dot_mem_lowerDimSupport (v : Fin m → ℝ) :
    (fun y => relu (dot v y)) ∈ LowerDimSupport m 1 := by
  refine ⟨{0, v}, Finset.insert_nonempty 0 {v}, ?_, ?_⟩
  · rw [Finset.coe_insert, Finset.coe_singleton, vectorSpan_pair]
    have h1 := finrank_span_finset_le_card (K := ℝ)
      ({(0 : Fin m → ℝ) -ᵥ v} : Finset (Fin m → ℝ))
    rw [Finset.coe_singleton, Finset.card_singleton] at h1
    exact h1
  · intro y
    show relu (dot v y) = _
    apply le_antisymm
    · refine max_le ?_ ?_
      · calc (0 : ℝ) = dot 0 y := (cf_dot_zero_left y).symm
          _ ≤ _ := Finset.le_sup' (fun p => dot p y) (Finset.mem_insert_self 0 {v})
      · exact Finset.le_sup' (fun p => dot p y)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    · refine Finset.sup'_le _ _ fun p hp => ?_
      rcases Finset.mem_insert.mp hp with h | h
      · rw [h, cf_dot_zero_left]
        exact relu_nonneg _
      · rw [Finset.mem_singleton.mp h]
        exact le_max_right 0 _

/-- The support function of a parallelepiped vertex set is a point plus segments, hence lies in
`LSpan m 1`. -/
theorem hS_powerset_image_add_sum_mem_LSpan (c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    hS (Z.powerset.image (fun J => c + ∑ v in J, v)) ∈ LSpan m 1 := by
  rw [hS_powerset_image_add_sum]
  have hfun : (fun y => dot c y + ∑ v in Z, relu (dot v y)) =
      dot c + ∑ v in Z, (fun y => relu (dot v y)) := by
    funext y
    rw [Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  unfold LSpan
  refine Submodule.add_mem _ (Submodule.subset_span (dot_mem_lowerDimSupport c 1)) ?_
  exact Submodule.sum_mem _ fun v _ =>
    Submodule.subset_span (cf_relu_dot_mem_lowerDimSupport v)

/-- `0 < A`: the face lies in `LSpan m 1`. -/
theorem hS_face_coneVertsOn_of_pos_mem_LSpan (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hA : 0 < dot u γ + ∑ v in V, relu (dot u v)) :
    hS (face u (coneVertsOn γ V)) ∈ LSpan m 1 := by
  rw [face_coneVertsOn_of_pos u γ V hA]
  exact hS_powerset_image_add_sum_mem_LSpan _ _

/-- In every case the support function of the face lies in `LSpan m (|Z| + 1)`. -/
theorem hS_face_coneVertsOn_mem_LSpan (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    hS (face u (coneVertsOn γ V)) ∈ LSpan m ((V.filter (fun v => dot u v = 0)).card + 1) := by
  have hne : (face u (coneVertsOn γ V)).Nonempty := by
    rcases lt_trichotomy (dot u γ + ∑ v in V, relu (dot u v)) 0 with h | h | h
    · rw [face_coneVertsOn_of_neg u γ V h]
      exact Finset.singleton_nonempty 0
    · rw [face_coneVertsOn_of_eq_zero u γ V h]
      exact ⟨0, cf_mem_coneVertsOn.mpr (Or.inl rfl)⟩
    · rw [face_coneVertsOn_of_pos u γ V h]
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.empty_mem_powerset _)⟩
  unfold LSpan
  exact Submodule.subset_span ⟨face u (coneVertsOn γ V), hne,
    finrank_vectorSpan_face_coneVertsOn_le u γ V, fun y => hS_of_nonempty hne y⟩

/-! ## Facets: exactly one label not orthogonal to `u` -/

/-- If `v₀ ∈ V` is the only label not orthogonal to `u` and `⟨u, v₀⟩ > 0`, then `P = {v₀}`. -/
theorem filter_pos_eq_singleton_of_single (u : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hv₀ : v₀ ∈ V) (hb : 0 < dot u v₀)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) :
    V.filter (fun v => 0 < dot u v) = {v₀} := by
  ext v
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hpos⟩
    by_contra hne
    rw [hrest v hv hne] at hpos
    exact lt_irrefl 0 hpos
  · rintro rfl
    exact ⟨hv₀, hb⟩

/-- If `v₀` is the only label not orthogonal to `u` and `⟨u, v₀⟩ < 0`, then `P = ∅`. -/
theorem filter_pos_eq_empty_of_single_neg (u : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hb : dot u v₀ < 0) (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) :
    V.filter (fun v => 0 < dot u v) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro v hv hpos
  by_cases hne : v = v₀
  · rw [hne] at hpos
    linarith
  · rw [hrest v hv hne] at hpos
    exact lt_irrefl 0 hpos

/-- If `v₀` is the only label not orthogonal to `u`, then `Z = V ∖ {v₀}`. -/
theorem filter_zero_eq_erase_of_single (u : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hb : dot u v₀ ≠ 0) (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) :
    V.filter (fun v => dot u v = 0) = V.erase v₀ := by
  ext v
  rw [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hv, hz⟩
    refine ⟨?_, hv⟩
    rintro rfl
    exact hb hz
  · rintro ⟨hne, hv⟩
    exact ⟨hv, hrest v hv hne⟩

/-- **Lateral facet through `γ + v₀`.**  If `⟨u, v₀⟩ > 0`, every other label is orthogonal to
`u`, and `⟨u, γ + v₀⟩ = 0`, the face is the cone `[γ + v₀; V ∖ v₀]`. -/
theorem face_coneVertsOn_of_single_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hv₀ : v₀ ∈ V) (hb : 0 < dot u v₀)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) (hA : dot u γ + dot u v₀ = 0) :
    face u (coneVertsOn γ V) = coneVertsOn (γ + v₀) (V.erase v₀) := by
  have hP := filter_pos_eq_singleton_of_single u V hv₀ hb hrest
  have hZ := filter_zero_eq_erase_of_single u V (ne_of_gt hb) hrest
  have hA' : dot u γ + ∑ v in V, relu (dot u v) = 0 := by
    rw [cf_sum_relu_eq, hP, Finset.sum_singleton]
    exact hA
  rw [face_coneVertsOn_of_eq_zero u γ V hA', hP, hZ, Finset.sum_singleton]

/-- **Lateral facet through `γ`.**  If `⟨u, v₀⟩ < 0`, every other label is orthogonal to `u`,
and `⟨u, γ⟩ = 0`, the face is the cone `[γ; V ∖ v₀]`. -/
theorem face_coneVertsOn_of_single_neg (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hb : dot u v₀ < 0)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) (hA : dot u γ = 0) :
    face u (coneVertsOn γ V) = coneVertsOn γ (V.erase v₀) := by
  have hP := filter_pos_eq_empty_of_single_neg u V hb hrest
  have hZ := filter_zero_eq_erase_of_single u V (ne_of_lt hb) hrest
  have hA' : dot u γ + ∑ v in V, relu (dot u v) = 0 := by
    rw [cf_sum_relu_eq, hP, Finset.sum_empty, hA, add_zero]
  rw [face_coneVertsOn_of_eq_zero u γ V hA', hP, hZ, Finset.sum_empty, add_zero]

/-- **Cone inside `u^⊥`.**  If `γ` and every label are orthogonal to `u`, the face is the whole
cone (so the faces in directions `u` and `-u` agree). -/
theorem face_coneVertsOn_of_forall_orth (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hV : ∀ v ∈ V, dot u v = 0) (hγ : dot u γ = 0) :
    face u (coneVertsOn γ V) = coneVertsOn γ V := by
  have hP : V.filter (fun v => 0 < dot u v) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hpos
    rw [hV v hv] at hpos
    exact lt_irrefl 0 hpos
  have hZ : V.filter (fun v => dot u v = 0) = V := Finset.filter_true_of_mem hV
  have hA : dot u γ + ∑ v in V, relu (dot u v) = 0 := by
    rw [cf_sum_relu_eq, hP, Finset.sum_empty, hγ, add_zero]
  rw [face_coneVertsOn_of_eq_zero u γ V hA, hP, hZ, Finset.sum_empty, add_zero]

/-- **Base.**  If every label is orthogonal to `u` and `⟨u, γ⟩ > 0`, the face is the base
parallelepiped `{γ + ∑_{v ∈ J} v | J ⊆ V}`. -/
theorem face_coneVertsOn_of_forall_orth_of_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    (hV : ∀ v ∈ V, dot u v = 0) (hγ : 0 < dot u γ) :
    face u (coneVertsOn γ V) = V.powerset.image (fun J => γ + ∑ v in J, v) := by
  have hP : V.filter (fun v => 0 < dot u v) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv hpos
    rw [hV v hv] at hpos
    exact lt_irrefl 0 hpos
  have hZ : V.filter (fun v => dot u v = 0) = V := Finset.filter_true_of_mem hV
  have hA : 0 < dot u γ + ∑ v in V, relu (dot u v) := by
    rw [cf_sum_relu_eq, hP, Finset.sum_empty, add_zero]
    exact hγ
  rw [face_coneVertsOn_of_pos u γ V hA, hP, hZ]
  simp only [Finset.sum_empty, add_zero]

/-- Support function of the lateral facet through `γ + v₀`: `paramidOn (γ + v₀) (V ∖ v₀)`. -/
theorem hS_face_coneVertsOn_of_single_pos (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hv₀ : v₀ ∈ V) (hb : 0 < dot u v₀)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) (hA : dot u γ + dot u v₀ = 0) :
    hS (face u (coneVertsOn γ V)) = paramidOn (γ + v₀) (V.erase v₀) := by
  rw [face_coneVertsOn_of_single_pos u γ V hv₀ hb hrest hA, hS_coneVertsOn_eq_paramidOn]

/-- Support function of the lateral facet through `γ`: `paramidOn γ (V ∖ v₀)`. -/
theorem hS_face_coneVertsOn_of_single_neg (u γ : Fin m → ℝ) (V : Finset (Fin m → ℝ))
    {v₀ : Fin m → ℝ} (hb : dot u v₀ < 0)
    (hrest : ∀ v ∈ V, v ≠ v₀ → dot u v = 0) (hA : dot u γ = 0) :
    hS (face u (coneVertsOn γ V)) = paramidOn γ (V.erase v₀) := by
  rw [face_coneVertsOn_of_single_neg u γ V hb hrest hA, hS_coneVertsOn_eq_paramidOn]

end MaxNN.ParamidGeom
