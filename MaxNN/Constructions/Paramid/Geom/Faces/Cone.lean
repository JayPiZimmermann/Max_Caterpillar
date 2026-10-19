import MaxNN.Constructions.Paramid.Geom.Faces.Cone.Parallelepiped

/-!
# The faces of a paramid cone

Module L7 of `work/depth2_simplex/smallest/PLAN_SMALLEST_GENERAL_N_2026-10-14.md` (Section 8.1,
Group B).  For an apex offset `γ` and a finite label set `V` in `ℝ^m`, the family
`coneFamily γ V` consists of

* the cones `coneVertsOn (γ + ∑_P v) Z`, with support function `paramidOn (γ + ∑_P v) Z`: the
  unit of `coneVertsOn γ V` with the hinges of `P` frozen to the identity and those of
  `V ∖ (P ∪ Z)` frozen to `0`;
* the base parallelepipeds `{γ + ∑_P v + ∑_{v ∈ J} v | J ⊆ Z}`, with support function
  `⟨γ + ∑_P v, ·⟩ + ∑_{v ∈ Z} relu ⟨v, ·⟩`: a linear form plus label hinges;

for all disjoint `P, Z ⊆ V`, and the apex `{0}`, with support function `0`.

Main results:

* `faceClosed_coneFamily`: the family is closed under faces.  The face of a member in direction
  `u` moves the labels `v ∈ Z` with `⟨u, v⟩ > 0` into `P` and keeps those with `⟨u, v⟩ = 0`
  (`face_coneVertsOn_of_neg`, `face_coneVertsOn_of_pos`, `face_coneVertsOn_of_eq_zero` of
  `Geom/Boundary/ConeFaces.lean`; `face_powerset_image_add_sum` of
  `Faces/Cone/Parallelepiped.lean`).
* `hS_of_mem_coneFamily`: the trichotomy of support functions above
  (`hS_coneVertsOn_eq_paramidOn`, `hS_powerset_image_add_sum`).
* `coneVertsOn_mem_coneFamily`, `nonempty_of_mem_coneFamily`,
  `subset_coneVertsOn_of_mem_coneFamily`: the family contains the cone, and its members are
  nonempty subsets of the cone's vertex set.  So it contains every iterated face of the cone.  For
  degenerate `V` it may also contain sets that are not faces of the cone; the Face Lemma only uses
  face-closure.

`faceClosed_coneFamily` is stated in unfolded form,
`∀ F ∈ coneFamily γ V, ∀ u, face u F ∈ coneFamily γ V`, which is definitionally
`FaceClosed (coneFamily γ V)` for the predicate `FaceClosed` of `Geom/Faces/Defs.lean`
(PLAN Section 8.1, module L5); this file does not import that module.
-/

namespace MaxNN.ParamidGeom.Faces

open BigOperators

variable {m : ℕ}

/-! ## The family -/

/-- A face-closed family of vertex sets containing the paramid cone `coneVertsOn γ V`: the cones
`coneVertsOn (γ + ∑_P v) Z` and the base parallelepipeds `{γ + ∑_P v + ∑_{v ∈ J} v | J ⊆ Z}` for
disjoint `P, Z ⊆ V`, and the apex `{0}`. -/
def coneFamily (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) : Set (Finset (Fin m → ℝ)) :=
  {F | (∃ P Z : Finset (Fin m → ℝ), P ⊆ V ∧ Z ⊆ V ∧ Disjoint P Z ∧
      F = coneVertsOn (γ + ∑ v in P, v) Z) ∨
    (∃ P Z : Finset (Fin m → ℝ), P ⊆ V ∧ Z ⊆ V ∧ Disjoint P Z ∧
      F = Z.powerset.image (fun J => γ + ∑ v in P, v + ∑ v in J, v)) ∨
    F = {0}}

theorem mem_coneFamily_iff {γ : Fin m → ℝ} {V F : Finset (Fin m → ℝ)} :
    F ∈ coneFamily γ V ↔
      (∃ P Z : Finset (Fin m → ℝ), P ⊆ V ∧ Z ⊆ V ∧ Disjoint P Z ∧
        F = coneVertsOn (γ + ∑ v in P, v) Z) ∨
      (∃ P Z : Finset (Fin m → ℝ), P ⊆ V ∧ Z ⊆ V ∧ Disjoint P Z ∧
        F = Z.powerset.image (fun J => γ + ∑ v in P, v + ∑ v in J, v)) ∨
      F = {0} :=
  Iff.rfl

/-! ## Private helpers -/

private theorem fc_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ face u S ↔ p ∈ S ∧ ∀ q ∈ S, dot u q ≤ dot u p :=
  @Finset.mem_filter _ _ (Classical.decPred _) _ _

private theorem fc_mem_coneVertsOn {γ : Fin m → ℝ} {V : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ coneVertsOn γ V ↔ p = 0 ∨ ∃ I, I ⊆ V ∧ γ + ∑ v in I, v = p := by
  unfold coneVertsOn
  rw [Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_powerset]

/-- The face of a singleton is the singleton. -/
private theorem fc_face_singleton (u p : Fin m → ℝ) :
    face u ({p} : Finset (Fin m → ℝ)) = {p} := by
  ext q
  rw [fc_mem_face]
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, fun r hr => ?_⟩
    rw [Finset.mem_singleton.mp hr, Finset.mem_singleton.mp hq]

/-- The apex has support function `0`. -/
private theorem fc_hS_zero : hS ({0} : Finset (Fin m → ℝ)) = 0 := by
  funext y
  rw [hS_of_nonempty (Finset.singleton_nonempty 0) y, Finset.sup'_singleton]
  show dot 0 y = 0
  unfold dot
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, zero_mul]

/-- Moving the labels `v ∈ Z` with `⟨u, v⟩ > 0` into `P` and keeping those with `⟨u, v⟩ = 0`
keeps the data admissible: `P ∪ Z⁺ ⊆ V`, `Z⁰ ⊆ V`, and `P ∪ Z⁺`, `Z⁰` are disjoint. -/
private theorem fc_admissible {V P Z : Finset (Fin m → ℝ)} (hP : P ⊆ V) (hZ : Z ⊆ V)
    (hPZ : Disjoint P Z) (u : Fin m → ℝ) :
    P ∪ Z.filter (fun v => 0 < dot u v) ⊆ V ∧ Z.filter (fun v => dot u v = 0) ⊆ V ∧
      Disjoint (P ∪ Z.filter (fun v => 0 < dot u v)) (Z.filter (fun v => dot u v = 0)) := by
  refine ⟨Finset.union_subset hP (Finset.Subset.trans (Finset.filter_subset _ _) hZ),
    Finset.Subset.trans (Finset.filter_subset _ _) hZ, ?_⟩
  rw [Finset.disjoint_union_left]
  refine ⟨Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hPZ, ?_⟩
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  have h1 := (Finset.mem_filter.mp hv1).2
  have h2 := (Finset.mem_filter.mp hv2).2
  rw [h2] at h1
  exact lt_irrefl 0 h1

/-- `γ + ∑_P v + ∑_{Z⁺} v = γ + ∑_{P ∪ Z⁺} v` for disjoint `P`, `Z`. -/
private theorem fc_add_sum_union (γ : Fin m → ℝ) {P Z : Finset (Fin m → ℝ)}
    (hPZ : Disjoint P Z) (u : Fin m → ℝ) :
    γ + ∑ v in P, v + ∑ v in Z.filter (fun v => 0 < dot u v), v =
      γ + ∑ v in P ∪ Z.filter (fun v => 0 < dot u v), v := by
  rw [Finset.sum_union (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hPZ),
    add_assoc]

/-! ## Basic members -/

/-- The cone itself is a member (`P = ∅`, `Z = V`). -/
theorem coneVertsOn_mem_coneFamily (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    coneVertsOn γ V ∈ coneFamily γ V := by
  refine mem_coneFamily_iff.mpr (Or.inl ⟨∅, V, Finset.empty_subset _, Finset.Subset.refl _,
    Finset.disjoint_empty_left _, ?_⟩)
  rw [Finset.sum_empty, add_zero]

/-- The apex is a member. -/
theorem zero_mem_coneFamily (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    ({0} : Finset (Fin m → ℝ)) ∈ coneFamily γ V :=
  mem_coneFamily_iff.mpr (Or.inr (Or.inr rfl))

/-- Every member is nonempty. -/
theorem nonempty_of_mem_coneFamily {γ : Fin m → ℝ} {V F : Finset (Fin m → ℝ)}
    (hF : F ∈ coneFamily γ V) : F.Nonempty := by
  rcases mem_coneFamily_iff.mp hF with ⟨P, Z, -, -, -, rfl⟩ | ⟨P, Z, -, -, -, rfl⟩ | rfl
  · exact ⟨0, fc_mem_coneVertsOn.mpr (Or.inl rfl)⟩
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.empty_mem_powerset Z)⟩
  · exact Finset.singleton_nonempty 0

/-- Every member is a subset of the vertex set of the cone. -/
theorem subset_coneVertsOn_of_mem_coneFamily {γ : Fin m → ℝ} {V F : Finset (Fin m → ℝ)}
    (hF : F ∈ coneFamily γ V) : F ⊆ coneVertsOn γ V := by
  rcases mem_coneFamily_iff.mp hF with ⟨P, Z, hP, hZ, hPZ, rfl⟩ | ⟨P, Z, hP, hZ, hPZ, rfl⟩ | rfl
  · intro p hp
    rcases fc_mem_coneVertsOn.mp hp with h | ⟨I, hI, rfl⟩
    · exact fc_mem_coneVertsOn.mpr (Or.inl h)
    · refine fc_mem_coneVertsOn.mpr (Or.inr ⟨P ∪ I, Finset.union_subset hP
        (Finset.Subset.trans hI hZ), ?_⟩)
      rw [Finset.sum_union (Finset.disjoint_of_subset_right hI hPZ), add_assoc]
  · intro p hp
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hp
    have hJ' := Finset.mem_powerset.mp hJ
    refine fc_mem_coneVertsOn.mpr (Or.inr ⟨P ∪ J, Finset.union_subset hP
      (Finset.Subset.trans hJ' hZ), ?_⟩)
    rw [Finset.sum_union (Finset.disjoint_of_subset_right hJ' hPZ), add_assoc]
  · intro p hp
    rw [Finset.mem_singleton.mp hp]
    exact fc_mem_coneVertsOn.mpr (Or.inl rfl)

/-! ## Face closure -/

/-- **The cone family is closed under faces.**  This is `FaceClosed (coneFamily γ V)` for the
predicate `FaceClosed` of `Geom/Faces/Defs.lean`, stated unfolded. -/
theorem faceClosed_coneFamily (γ : Fin m → ℝ) (V : Finset (Fin m → ℝ)) :
    ∀ F ∈ coneFamily γ V, ∀ u, face u F ∈ coneFamily γ V := by
  intro F hF u
  rcases mem_coneFamily_iff.mp hF with ⟨P, Z, hP, hZ, hPZ, rfl⟩ | ⟨P, Z, hP, hZ, hPZ, rfl⟩ | rfl
  · obtain ⟨h1, h2, h3⟩ := fc_admissible hP hZ hPZ u
    rcases lt_trichotomy (dot u (γ + ∑ v in P, v) + ∑ v in Z, relu (dot u v)) 0 with h | h | h
    · rw [face_coneVertsOn_of_neg u _ Z h]
      exact zero_mem_coneFamily γ V
    · rw [face_coneVertsOn_of_eq_zero u _ Z h, fc_add_sum_union γ hPZ u]
      exact mem_coneFamily_iff.mpr (Or.inl ⟨_, _, h1, h2, h3, rfl⟩)
    · rw [face_coneVertsOn_of_pos u _ Z h, fc_add_sum_union γ hPZ u]
      exact mem_coneFamily_iff.mpr (Or.inr (Or.inl ⟨_, _, h1, h2, h3, rfl⟩))
  · obtain ⟨h1, h2, h3⟩ := fc_admissible hP hZ hPZ u
    rw [face_powerset_image_add_sum u (γ + ∑ v in P, v) Z, fc_add_sum_union γ hPZ u]
    exact mem_coneFamily_iff.mpr (Or.inr (Or.inl ⟨_, _, h1, h2, h3, rfl⟩))
  · rw [fc_face_singleton]
    exact zero_mem_coneFamily γ V

/-- Pointwise form of `faceClosed_coneFamily`. -/
theorem face_mem_coneFamily {γ : Fin m → ℝ} {V F : Finset (Fin m → ℝ)}
    (hF : F ∈ coneFamily γ V) (u : Fin m → ℝ) : face u F ∈ coneFamily γ V :=
  faceClosed_coneFamily γ V F hF u

/-! ## Support functions -/

/-- **Support functions of the members**: a paramid unit `paramidOn (γ + ∑_P v) Z` (a cone face:
the hinges of `P` frozen to the identity, those of `V ∖ (P ∪ Z)` frozen to `0`), a linear form
plus label hinges (a base face), or `0` (the apex). -/
theorem hS_of_mem_coneFamily {γ : Fin m → ℝ} {V F : Finset (Fin m → ℝ)}
    (hF : F ∈ coneFamily γ V) :
    (∃ P Z, P ⊆ V ∧ Z ⊆ V ∧ Disjoint P Z ∧ hS F = paramidOn (γ + ∑ v in P, v) Z) ∨
    (∃ c Z, Z ⊆ V ∧ hS F = fun y => dot c y + ∑ v in Z, relu (dot v y)) ∨ hS F = 0 := by
  rcases mem_coneFamily_iff.mp hF with ⟨P, Z, hP, hZ, hPZ, rfl⟩ | ⟨P, Z, -, hZ, -, rfl⟩ | rfl
  · exact Or.inl ⟨P, Z, hP, hZ, hPZ, hS_coneVertsOn_eq_paramidOn _ _⟩
  · exact Or.inr (Or.inl ⟨γ + ∑ v in P, v, Z, hZ, hS_powerset_image_add_sum _ _⟩)
  · exact Or.inr (Or.inr fc_hS_zero)

end MaxNN.ParamidGeom.Faces
