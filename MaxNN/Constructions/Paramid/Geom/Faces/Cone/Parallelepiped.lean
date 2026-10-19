import MaxNN.Constructions.Paramid.Geom.Boundary.ConeFaces

/-!
# Faces of a parallelepiped vertex set

Helper of `Geom/Faces/Cone.lean` (module L7 of
`work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md`, Section 8).

For an offset `c`, a finite label set `Z` and a direction `u` in `ℝ^m`, write
`Z⁺ = {v ∈ Z | 0 < ⟨u, v⟩}` and `Z⁰ = {v ∈ Z | ⟨u, v⟩ = 0}`.  Over the parallelepiped vertex set
`{c + ∑_{v ∈ J} v | J ⊆ Z}` the functional `⟨u, ·⟩` is at most `⟨u, c⟩ + ∑_{v ∈ Z} relu ⟨u, v⟩`,
with equality exactly at the points `c + ∑_{Z⁺} v + ∑_{v ∈ J} v`, `J ⊆ Z⁰`.  Hence, for every
direction `u`,

  `face u {c + ∑_J v | J ⊆ Z} = {c + ∑_{Z⁺} v + ∑_J v | J ⊆ Z⁰}`   (`face_powerset_image_add_sum`).

This is the parallelepiped analogue of `face_coneVertsOn_of_pos` (`Geom/Boundary/ConeFaces.lean`),
whose helpers are private; the elementary facts about `dot` used here are private copies (prefix
`pp_`), so that this file cannot clash with helpers of sibling modules.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators

variable {m : ℕ}

/-! ## Private helpers -/

private theorem pp_dot_add_right (u p q : Fin m → ℝ) : dot u (p + q) = dot u p + dot u q := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, mul_add]

private theorem pp_dot_sum_right {ι : Type*} (u : Fin m → ℝ) (s : Finset ι)
    (p : ι → Fin m → ℝ) : dot u (∑ i in s, p i) = ∑ i in s, dot u (p i) := by
  unfold dot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum]

private theorem pp_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ face u S ↔ p ∈ S ∧ ∀ q ∈ S, dot u q ≤ dot u p :=
  @Finset.mem_filter _ _ (Classical.decPred _) _ _

/-- `∑_{v ∈ Z} relu ⟨u, v⟩ = ∑_{v ∈ Z⁺} ⟨u, v⟩`. -/
private theorem pp_sum_relu_eq (u : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    ∑ v in Z, relu (dot u v) = ∑ v in Z.filter (fun v => 0 < dot u v), dot u v := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : 0 < dot u v
  · rw [if_pos h, relu_of_nonneg h.le]
  · rw [if_neg h, relu_of_nonpos (not_lt.mp h)]

/-- Every parallelepiped vertex has `⟨u, ·⟩ ≤ ⟨u, c⟩ + ∑_{v ∈ Z} relu ⟨u, v⟩`. -/
private theorem pp_dot_vertex_le (u c : Fin m → ℝ) {Z I : Finset (Fin m → ℝ)} (hI : I ⊆ Z) :
    dot u (c + ∑ v in I, v) ≤ dot u c + ∑ v in Z, relu (dot u v) := by
  rw [pp_dot_add_right, pp_dot_sum_right]
  apply add_le_add_left
  calc ∑ v in I, dot u v ≤ ∑ v in I, relu (dot u v) :=
        Finset.sum_le_sum fun v _ => le_max_right 0 _
    _ ≤ ∑ v in Z, relu (dot u v) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI fun v _ _ => relu_nonneg _

/-- The points `c + ∑_{Z⁺} v + ∑_J v` (`J ⊆ Z⁰`) attain the bound. -/
private theorem pp_dot_top (u c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) {J : Finset (Fin m → ℝ)}
    (hJ : J ⊆ Z.filter (fun v => dot u v = 0)) :
    dot u (c + ∑ v in Z.filter (fun v => 0 < dot u v), v + ∑ v in J, v) =
      dot u c + ∑ v in Z, relu (dot u v) := by
  rw [pp_dot_add_right, pp_dot_add_right, pp_dot_sum_right, pp_dot_sum_right, pp_sum_relu_eq]
  have h0 : ∑ v in J, dot u v = 0 :=
    Finset.sum_eq_zero fun v hv => (Finset.mem_filter.mp (hJ hv)).2
  rw [h0, add_zero]

/-- The points `c + ∑_{Z⁺} v + ∑_J v` (`J ⊆ Z⁰`) are parallelepiped vertices. -/
private theorem pp_top_mem (u c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) {J : Finset (Fin m → ℝ)}
    (hJ : J ⊆ Z.filter (fun v => dot u v = 0)) :
    c + ∑ v in Z.filter (fun v => 0 < dot u v), v + ∑ v in J, v ∈
      Z.powerset.image (fun I => c + ∑ v in I, v) := by
  have hdisj : Disjoint (Z.filter (fun v => 0 < dot u v)) J := by
    rw [Finset.disjoint_left]
    intro v hvP hvJ
    have h1 := (Finset.mem_filter.mp hvP).2
    have h2 := (Finset.mem_filter.mp (hJ hvJ)).2
    rw [h2] at h1
    exact lt_irrefl 0 h1
  refine Finset.mem_image.mpr ⟨Z.filter (fun v => 0 < dot u v) ∪ J, ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.union_subset (Finset.filter_subset _ _)
      (fun v hv => (Finset.mem_filter.mp (hJ hv)).1))
  · show c + ∑ v in Z.filter (fun v => 0 < dot u v) ∪ J, v = _
    rw [Finset.sum_union hdisj, add_assoc]

/-- A parallelepiped vertex attaining the bound is of the form `c + ∑_{Z⁺} v + ∑_J v`,
`J ⊆ Z⁰`. -/
private theorem pp_eq_top (u c : Fin m → ℝ) {Z I : Finset (Fin m → ℝ)} (hI : I ⊆ Z)
    (h : dot u (c + ∑ v in I, v) = dot u c + ∑ v in Z, relu (dot u v)) :
    ∃ J, J ⊆ Z.filter (fun v => dot u v = 0) ∧
      c + ∑ v in I, v = c + ∑ v in Z.filter (fun v => 0 < dot u v), v + ∑ v in J, v := by
  rw [pp_dot_add_right, pp_dot_sum_right, add_right_inj] at h
  have hsplit : ∑ v in Z \ I, relu (dot u v) + ∑ v in I, relu (dot u v) =
      ∑ v in Z, relu (dot u v) := Finset.sum_sdiff hI
  have hdiff : ∑ v in I, (relu (dot u v) - dot u v) =
      ∑ v in I, relu (dot u v) - ∑ v in I, dot u v := Finset.sum_sub_distrib
  have hn1 : 0 ≤ ∑ v in Z \ I, relu (dot u v) := Finset.sum_nonneg fun v _ => relu_nonneg _
  have hn2 : 0 ≤ ∑ v in I, (relu (dot u v) - dot u v) :=
    Finset.sum_nonneg fun v _ => sub_nonneg.mpr (le_max_right 0 _)
  have e1 : ∑ v in Z \ I, relu (dot u v) = 0 := by linarith
  have e2 : ∑ v in I, (relu (dot u v) - dot u v) = 0 := by linarith
  have hout : ∀ v ∈ Z, v ∉ I → dot u v ≤ 0 := by
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
    have hP : I.filter (fun v => 0 < dot u v) = Z.filter (fun v => 0 < dot u v) := by
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

/-! ## The face of a parallelepiped -/

/-- **Face of a parallelepiped vertex set**, every direction `u`:
`face u {c + ∑_J v | J ⊆ Z} = {c + ∑_{Z⁺} v + ∑_J v | J ⊆ Z⁰}` with
`Z⁺ = {v ∈ Z | 0 < ⟨u, v⟩}`, `Z⁰ = {v ∈ Z | ⟨u, v⟩ = 0}`. -/
theorem face_powerset_image_add_sum (u c : Fin m → ℝ) (Z : Finset (Fin m → ℝ)) :
    face u (Z.powerset.image (fun J => c + ∑ v in J, v)) =
      (Z.filter (fun v => dot u v = 0)).powerset.image
        (fun J => c + ∑ v in Z.filter (fun v => 0 < dot u v), v + ∑ v in J, v) := by
  ext p
  rw [pp_mem_face]
  constructor
  · rintro ⟨hp, hmax⟩
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hp
    have hI' := Finset.mem_powerset.mp hI
    have htop := hmax _ (pp_top_mem u c Z (Finset.empty_subset _))
    rw [pp_dot_top u c Z (Finset.empty_subset _)] at htop
    have hle := pp_dot_vertex_le u c hI'
    obtain ⟨J, hJ, hEq⟩ := pp_eq_top u c hI' (le_antisymm hle htop)
    exact Finset.mem_image.mpr ⟨J, Finset.mem_powerset.mpr hJ, hEq.symm⟩
  · intro hp
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hp
    have hJ' := Finset.mem_powerset.mp hJ
    refine ⟨pp_top_mem u c Z hJ', fun q hq => ?_⟩
    rw [pp_dot_top u c Z hJ']
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
    exact pp_dot_vertex_le u c (Finset.mem_powerset.mp hI)

end MaxNN.ParamidGeom.Faces
