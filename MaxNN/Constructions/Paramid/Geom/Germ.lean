import MaxNN.Constructions.Paramid.Geom.Defs
import MaxNN.PolyhedralGeometry.SupportCut.Dot

/-!
# Germs of support functions

Module `M-Germ` of the geometric core (`work/depth2_simplex/lean_core/BLUEPRINT.md`).

`IsGerm f u g` says that for every `y` the difference quotient `(f (u + t • y) − f u) / t`
tends to `g y` as `t → 0⁺`; then `germ f u = g` (`germ_eq_of_isGerm`).

* Along a short ray a support function is affine:
  `hS S (u + t • y) = hS S u + t · hS (face u S) y` for all small `t > 0`
  (`eventually_hS_add_smul`), hence `IsGerm (hS S) u (hS (face u S))` (`isGerm_hS`).
* `IsGerm` is stable under sums, scalar multiples, finite sums and linear substitutions
  `y ↦ B y`, so every `f ∈ SSpan m` has a germ in `SSpan m` at every `u`
  (`isGerm_germ_of_mem_SSpan`, `germ_mem_SSpan`), and `germ`, `germDiff` are linear on
  `SSpan m`.
* `germDiff u (hS S) = hS (face u S) − hS (face (−u) S)` (`germDiff_hS`).
* Transport through a matrix: `hS (A S) y = hS S (Aᵀ y)` (`hS_image_mulVec`) and
  `germDiff u (f ∘ Aᵀ) = germDiff (Aᵀ u) f ∘ Aᵀ` (`germDiff_comp_mulVec`).
* `germ f (c • u) = germ f u` for `c > 0` (`germ_pos_smul`), and `LSpan m k ≤ SSpan m`.
* Germs through `relu` (`IsGerm.relu_of_pos`, `IsGerm.relu_of_neg`,
  `IsGerm.relu_of_eq_zero`), for the germs of paramid units.

Generic facts about `hS`, `dot` and limits that other modules of the geometric core may also
need live in the sub-namespace `GermAux`, so that they cannot collide with helpers of the same
name in sibling modules of `MaxNN.ParamidGeom`.
-/

namespace MaxNN.ParamidGeom

open BigOperators Filter Topology
open scoped Matrix

variable {m n : ℕ}

/-! ## Generic helpers -/

namespace GermAux

/-- `t ↦ a + t * b` tends to `a` at `0`. -/
theorem tendsto_add_mul_nhds_zero (a b : ℝ) :
    Tendsto (fun t : ℝ => a + t * b) (nhds 0) (nhds a) := by
  have h : Tendsto (fun t : ℝ => a + t * b) (nhds 0) (nhds (a + 0 * b)) :=
    tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
  rwa [zero_mul, add_zero] at h

/-- `(a + t * b − a) / t = b` for `t ≠ 0`. -/
theorem add_mul_sub_div_self {t : ℝ} (ht : t ≠ 0) (a b : ℝ) : (a + t * b - a) / t = b := by
  rw [add_sub_cancel']
  exact mul_div_cancel_left b ht

/-- `relu (a / t) = relu a / t` for `t > 0`. -/
theorem relu_div_of_pos {t : ℝ} (ht : 0 < t) (a : ℝ) : relu (a / t) = relu a / t := by
  rcases le_total 0 a with ha | ha
  · rw [relu_of_nonneg ha, relu_of_nonneg (div_nonneg ha ht.le)]
  · rw [relu_of_nonpos ha, relu_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha ht.le),
      zero_div]

theorem hS_empty (y : Fin m → ℝ) : hS (∅ : Finset (Fin m → ℝ)) y = 0 := by
  unfold hS
  exact dif_neg Finset.not_nonempty_empty

theorem dot_le_hS {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ} (hp : p ∈ S) (y : Fin m → ℝ) :
    dot p y ≤ hS S y := by
  rw [hS_of_nonempty ⟨p, hp⟩]
  exact Finset.le_sup' (fun q => dot q y) hp

theorem exists_mem_hS_eq {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (y : Fin m → ℝ) :
    ∃ p ∈ S, hS S y = dot p y := by
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' h (fun q => dot q y)
  exact ⟨p, hp, by rw [hS_of_nonempty h]; exact hpe⟩

theorem hS_singleton (p : Fin m → ℝ) : hS ({p} : Finset (Fin m → ℝ)) = dot p := by
  funext y
  rw [hS_of_nonempty (Finset.singleton_nonempty p), Finset.sup'_singleton]

theorem hS_mem_SSpan {S : Finset (Fin m → ℝ)} (h : S.Nonempty) : hS S ∈ SSpan m :=
  Submodule.subset_span ⟨S, h, rfl⟩

theorem dot_mem_SSpan (p : Fin m → ℝ) : dot p ∈ SSpan m := by
  rw [← hS_singleton]
  exact hS_mem_SSpan (Finset.singleton_nonempty p)

/-- `⟨A p, y⟩ = ⟨p, Aᵀ y⟩`. -/
theorem dot_mulVec (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) (y : Fin m → ℝ) :
    dot (A.mulVec p) y = dot p (Aᵀ.mulVec y) := by
  show Matrix.dotProduct (A.mulVec p) y = Matrix.dotProduct p (Aᵀ.mulVec y)
  rw [Matrix.dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose,
    Matrix.dotProduct_comm]

end GermAux

open GermAux

/-! ## The germ predicate -/

/-- `g` is the germ of `f` at `u`: for every `y`, the difference quotient
`(f (u + t • y) − f u) / t` tends to `g y` as `t → 0⁺`. -/
def IsGerm (f : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ y, Filter.Tendsto (fun t : ℝ => (f (u + t • y) - f u) / t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (g y))

/-- A germ in the sense of `IsGerm` is the value of `germ`. -/
theorem germ_eq_of_isGerm {f : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} {g : (Fin m → ℝ) → ℝ}
    (h : IsGerm f u g) : germ f u = g := by
  funext y
  exact (h y).limUnder_eq

theorem IsGerm.unique {f g₁ g₂ : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (h₁ : IsGerm f u g₁) (h₂ : IsGerm f u g₂) : g₁ = g₂ :=
  (germ_eq_of_isGerm h₁).symm.trans (germ_eq_of_isGerm h₂)

/-! ## Faces -/

theorem mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ} :
    p ∈ face u S ↔ p ∈ S ∧ ∀ q ∈ S, dot u q ≤ dot u p :=
  @Finset.mem_filter _ _ (Classical.decPred _) _ _

theorem face_subset (u : Fin m → ℝ) (S : Finset (Fin m → ℝ)) : face u S ⊆ S := fun _ hp =>
  (mem_face.mp hp).1

theorem face_nonempty {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (u : Fin m → ℝ) :
    (face u S).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun q => dot u q) h
  exact ⟨p, mem_face.mpr ⟨hp, hmax⟩⟩

theorem face_singleton (u p : Fin m → ℝ) : face u ({p} : Finset (Fin m → ℝ)) = {p} := by
  ext q
  rw [mem_face]
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, fun r hr => ?_⟩
    rw [Finset.mem_singleton.mp hr, Finset.mem_singleton.mp hq]

/-- On the face in direction `u`, the support function at `u` is attained. -/
theorem hS_eq_dot_of_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ}
    (hp : p ∈ face u S) : hS S u = dot p u := by
  obtain ⟨hpS, hmax⟩ := mem_face.mp hp
  apply le_antisymm
  · rw [hS_of_nonempty ⟨p, hpS⟩]
    refine Finset.sup'_le _ _ (fun q hq => ?_)
    show dot q u ≤ dot p u
    rw [SupportCut.dot_comm q u, SupportCut.dot_comm p u]
    exact hmax q hq
  · exact dot_le_hS hpS u

/-- Off the face in direction `u`, the value at `u` is strictly below the support function. -/
theorem dot_lt_hS_of_not_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p : Fin m → ℝ}
    (hpS : p ∈ S) (hpF : p ∉ face u S) : dot p u < hS S u := by
  have hex : ∃ q ∈ S, dot u p < dot u q := by
    by_contra hcon
    push_neg at hcon
    exact hpF (mem_face.mpr ⟨hpS, hcon⟩)
  obtain ⟨q, hq, hlt⟩ := hex
  calc dot p u = dot u p := SupportCut.dot_comm p u
    _ < dot u q := hlt
    _ = dot q u := SupportCut.dot_comm u q
    _ ≤ hS S u := dot_le_hS hq u

/-- Faces do not see positive rescaling of the direction. -/
theorem face_smul_of_pos {c : ℝ} (hc : 0 < c) (u : Fin m → ℝ) (S : Finset (Fin m → ℝ)) :
    face (c • u) S = face u S := by
  ext p
  rw [mem_face, mem_face]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun q hq => ?_⟩
    have hq' := h q hq
    rw [SupportCut.dot_smul_left, SupportCut.dot_smul_left] at hq'
    exact (mul_le_mul_left hc).mp hq'
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun q hq => ?_⟩
    rw [SupportCut.dot_smul_left, SupportCut.dot_smul_left]
    exact mul_le_mul_of_nonneg_left (h q hq) hc.le

/-! ## The germ of a support function -/

/-- **A support function is affine along short rays.**  For nonempty `S`, every small
`t > 0` satisfies `hS S (u + t • y) = hS S u + t · hS (face u S) y`. -/
theorem eventually_hS_add_smul {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (u y : Fin m → ℝ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      hS S (u + t • y) = hS S u + t * hS (face u S) y := by
  have hev : ∀ᶠ t in nhds (0 : ℝ), ∀ p ∈ S, p ∉ face u S →
      dot p (u + t • y) < hS S u + t * hS (face u S) y := by
    refine (Filter.eventually_all_finset S).mpr (fun p hp => ?_)
    by_cases hpF : p ∈ face u S
    · exact Filter.eventually_of_forall (fun _ hn => absurd hpF hn)
    · have hlt : dot p u < hS S u := dot_lt_hS_of_not_mem_face hp hpF
      have h1 : Tendsto (fun t : ℝ => dot p (u + t • y)) (nhds 0) (nhds (dot p u)) := by
        have e : (fun t : ℝ => dot p (u + t • y)) = fun t => dot p u + t * dot p y := by
          funext t
          rw [SupportCut.dot_add_right, SupportCut.dot_smul_right]
        rw [e]
        exact tendsto_add_mul_nhds_zero _ _
      have h2 := tendsto_add_mul_nhds_zero (hS S u) (hS (face u S) y)
      exact (h1.eventually_lt h2 hlt).mono (fun t ht _ => ht)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hev] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  apply le_antisymm
  · rw [hS_of_nonempty h (u + t • y)]
    refine Finset.sup'_le _ _ (fun p hp => ?_)
    show dot p (u + t • y) ≤ hS S u + t * hS (face u S) y
    by_cases hpF : p ∈ face u S
    · rw [SupportCut.dot_add_right, SupportCut.dot_smul_right, ← hS_eq_dot_of_mem_face hpF]
      exact add_le_add_left (mul_le_mul_of_nonneg_left (dot_le_hS hpF y) htpos'.le) _
    · exact le_of_lt (ht p hp hpF)
  · obtain ⟨q, hqF, hq⟩ := exists_mem_hS_eq (face_nonempty h u) y
    rw [hq, hS_eq_dot_of_mem_face hqF, ← SupportCut.dot_smul_right, ← SupportCut.dot_add_right]
    exact dot_le_hS (face_subset u S hqF) (u + t • y)

/-- **Germ of a support function**: the support function of the face. -/
theorem isGerm_hS {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (u : Fin m → ℝ) :
    IsGerm (hS S) u (hS (face u S)) := by
  intro y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_hS_add_smul h u y, self_mem_nhdsWithin] with t ht htpos
  rw [ht, add_mul_sub_div_self (ne_of_gt htpos)]

/-! ## The germ calculus -/

theorem isGerm_zero (u : Fin m → ℝ) : IsGerm (0 : (Fin m → ℝ) → ℝ) u 0 := by
  intro y
  refine tendsto_const_nhds.congr (fun t => ?_)
  show (0 : ℝ) = (0 - 0) / t
  rw [sub_self, zero_div]

theorem IsGerm.add {f₁ f₂ g₁ g₂ : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (h₁ : IsGerm f₁ u g₁) (h₂ : IsGerm f₂ u g₂) : IsGerm (f₁ + f₂) u (g₁ + g₂) := by
  intro y
  refine ((h₁ y).add (h₂ y)).congr (fun t => ?_)
  show (f₁ (u + t • y) - f₁ u) / t + (f₂ (u + t • y) - f₂ u) / t =
    (f₁ (u + t • y) + f₂ (u + t • y) - (f₁ u + f₂ u)) / t
  ring

theorem IsGerm.smul {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (c : ℝ) (h : IsGerm f u g) :
    IsGerm (c • f) u (c • g) := by
  intro y
  refine ((h y).const_mul c).congr (fun t => ?_)
  show c * ((f (u + t • y) - f u) / t) = (c * f (u + t • y) - c * f u) / t
  ring

theorem IsGerm.const_mul {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (c : ℝ) (h : IsGerm f u g) :
    IsGerm (fun y => c * f y) u (fun y => c * g y) :=
  h.smul c

theorem IsGerm.neg {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g) :
    IsGerm (-f) u (-g) := by
  intro y
  refine (h y).neg.congr (fun t => ?_)
  show -((f (u + t • y) - f u) / t) = (-f (u + t • y) - -f u) / t
  ring

theorem IsGerm.sub {f₁ f₂ g₁ g₂ : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (h₁ : IsGerm f₁ u g₁) (h₂ : IsGerm f₂ u g₂) : IsGerm (f₁ - f₂) u (g₁ - g₂) := by
  intro y
  refine ((h₁ y).sub (h₂ y)).congr (fun t => ?_)
  show (f₁ (u + t • y) - f₁ u) / t - (f₂ (u + t • y) - f₂ u) / t =
    (f₁ (u + t • y) - f₂ (u + t • y) - (f₁ u - f₂ u)) / t
  ring

theorem IsGerm.sum {ι : Type*} (s : Finset ι) {f g : ι → (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (h : ∀ i ∈ s, IsGerm (f i) u (g i)) :
    IsGerm (fun y => ∑ i in s, f i y) u (fun y => ∑ i in s, g i y) := by
  intro y
  refine (tendsto_finset_sum s (fun i hi => h i hi y)).congr (fun t => ?_)
  show ∑ i in s, (f i (u + t • y) - f i u) / t =
    ((∑ i in s, f i (u + t • y)) - ∑ i in s, f i u) / t
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- A linear form is its own germ everywhere. -/
theorem isGerm_dot (p u : Fin m → ℝ) : IsGerm (dot p) u (dot p) := by
  intro y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  show dot p y = (dot p (u + t • y) - dot p u) / t
  rw [SupportCut.dot_add_right, SupportCut.dot_smul_right,
    add_mul_sub_div_self (ne_of_gt ht)]

/-- A linear substitution `y ↦ B y` transports germs. -/
theorem IsGerm.comp_mulVec (B : Matrix (Fin n) (Fin m) ℝ) {f g : (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ} (h : IsGerm f (B.mulVec u) g) :
    IsGerm (fun y => f (B.mulVec y)) u (fun y => g (B.mulVec y)) := by
  intro y
  refine (h (B.mulVec y)).congr (fun t => ?_)
  show (f (B.mulVec u + t • B.mulVec y) - f (B.mulVec u)) / t =
    (f (B.mulVec (u + t • y)) - f (B.mulVec u)) / t
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- A function with a germ at `u` is right-continuous along every ray from `u`. -/
theorem IsGerm.tendsto_ray {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g)
    (y : Fin m → ℝ) :
    Tendsto (fun t : ℝ => f (u + t • y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f u)) := by
  have h0 : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : Tendsto (fun t : ℝ => f u + t * ((f (u + t • y) - f u) / t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f u + 0 * g y)) :=
    tendsto_const_nhds.add (h0.mul (h y))
  rw [zero_mul, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := ne_of_gt ht
  rw [mul_div_cancel' _ htne]
  ring

/-- Germ of `relu ∘ f` where `f u > 0`. -/
theorem IsGerm.relu_of_pos {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g)
    (hu : 0 < f u) : IsGerm (fun y => relu (f y)) u g := by
  intro y
  refine (h y).congr' ?_
  filter_upwards [eventually_gt_of_tendsto_gt hu (h.tendsto_ray y)] with t ht
  show (f (u + t • y) - f u) / t = (relu (f (u + t • y)) - relu (f u)) / t
  rw [relu_of_nonneg ht.le, relu_of_nonneg hu.le]

/-- Germ of `relu ∘ f` where `f u < 0`. -/
theorem IsGerm.relu_of_neg {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g)
    (hu : f u < 0) : IsGerm (fun y => relu (f y)) u 0 := by
  intro y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_of_tendsto_lt hu (h.tendsto_ray y)] with t ht
  show (0 : ℝ) = (relu (f (u + t • y)) - relu (f u)) / t
  rw [relu_of_nonpos ht.le, relu_of_nonpos hu.le, sub_self, zero_div]

/-- Germ of `relu ∘ f` where `f u = 0`. -/
theorem IsGerm.relu_of_eq_zero {f g : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (h : IsGerm f u g)
    (hu : f u = 0) : IsGerm (fun y => relu (f y)) u (fun y => relu (g y)) := by
  intro y
  have hcont : Continuous relu := continuous_const.max continuous_id
  refine ((hcont.tendsto (g y)).comp (h y)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  show relu ((f (u + t • y) - f u) / t) = (relu (f (u + t • y)) - relu (f u)) / t
  rw [hu, sub_zero, relu_of_nonneg (le_refl (0 : ℝ)), sub_zero]
  exact relu_div_of_pos ht _

/-! ## Germs on the span of support functions -/

/-- Every function in `SSpan m` has, at every `u`, a germ lying in `SSpan m`. -/
theorem exists_isGerm_mem_SSpan {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    ∃ g ∈ SSpan m, IsGerm f u g := by
  refine Submodule.span_induction (p := fun f => ∃ g ∈ SSpan m, IsGerm f u g) hf ?_ ?_ ?_ ?_
  · rintro _ ⟨S, hSne, rfl⟩
    exact ⟨hS (face u S), hS_mem_SSpan (face_nonempty hSne u), isGerm_hS hSne u⟩
  · exact ⟨0, Submodule.zero_mem _, isGerm_zero u⟩
  · rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, h₁.add h₂⟩
  · rintro c f ⟨g, hg, h⟩
    exact ⟨c • g, Submodule.smul_mem _ c hg, h.smul c⟩

theorem isGerm_germ_of_mem_SSpan {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    IsGerm f u (germ f u) := by
  obtain ⟨g, -, hg⟩ := exists_isGerm_mem_SSpan hf u
  rw [germ_eq_of_isGerm hg]
  exact hg

theorem germ_mem_SSpan {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germ f u ∈ SSpan m := by
  obtain ⟨g, hgS, hg⟩ := exists_isGerm_mem_SSpan hf u
  rw [germ_eq_of_isGerm hg]
  exact hgS

theorem germ_hS {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (u : Fin m → ℝ) :
    germ (hS S) u = hS (face u S) :=
  germ_eq_of_isGerm (isGerm_hS h u)

theorem germ_dot (p u : Fin m → ℝ) : germ (dot p) u = dot p :=
  germ_eq_of_isGerm (isGerm_dot p u)

theorem germ_zero (u : Fin m → ℝ) : germ (0 : (Fin m → ℝ) → ℝ) u = 0 :=
  germ_eq_of_isGerm (isGerm_zero u)

theorem germ_add {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (u : Fin m → ℝ) : germ (f + g) u = germ f u + germ g u :=
  germ_eq_of_isGerm ((isGerm_germ_of_mem_SSpan hf u).add (isGerm_germ_of_mem_SSpan hg u))

theorem germ_smul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germ (c • f) u = c • germ f u :=
  germ_eq_of_isGerm ((isGerm_germ_of_mem_SSpan hf u).smul c)

theorem germ_neg {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germ (-f) u = -germ f u :=
  germ_eq_of_isGerm (isGerm_germ_of_mem_SSpan hf u).neg

theorem germ_sub {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (u : Fin m → ℝ) : germ (f - g) u = germ f u - germ g u :=
  germ_eq_of_isGerm ((isGerm_germ_of_mem_SSpan hf u).sub (isGerm_germ_of_mem_SSpan hg u))

theorem germ_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin m → ℝ) → ℝ}
    (hf : ∀ i ∈ s, f i ∈ SSpan m) (u : Fin m → ℝ) :
    germ (fun y => ∑ i in s, f i y) u = fun y => ∑ i in s, germ (f i) u y :=
  germ_eq_of_isGerm (IsGerm.sum s (fun i hi => isGerm_germ_of_mem_SSpan (hf i hi) u))

/-- The germ depends only on the ray of the base point. -/
theorem germ_pos_smul {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) {c : ℝ} (hc : 0 < c)
    (u : Fin m → ℝ) : germ f (c • u) = germ f u := by
  have key : ∃ g, IsGerm f u g ∧ IsGerm f (c • u) g := by
    refine Submodule.span_induction
      (p := fun f => ∃ g, IsGerm f u g ∧ IsGerm f (c • u) g) hf ?_ ?_ ?_ ?_
    · rintro _ ⟨S, hSne, rfl⟩
      refine ⟨hS (face u S), isGerm_hS hSne u, ?_⟩
      have hc' := isGerm_hS hSne (c • u)
      rwa [face_smul_of_pos hc u S] at hc'
    · exact ⟨0, isGerm_zero u, isGerm_zero (c • u)⟩
    · rintro f₁ f₂ ⟨g₁, h₁, h₁'⟩ ⟨g₂, h₂, h₂'⟩
      exact ⟨g₁ + g₂, h₁.add h₂, h₁'.add h₂'⟩
    · rintro a f ⟨g, h, h'⟩
      exact ⟨a • g, h.smul a, h'.smul a⟩
  obtain ⟨g, h, h'⟩ := key
  rw [germ_eq_of_isGerm h, germ_eq_of_isGerm h']

/-! ## Germ differences -/

theorem germDiff_eq_sub (u : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    germDiff u f = germ f u - germ f (-u) := rfl

theorem germDiff_add {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (u : Fin m → ℝ) : germDiff u (f + g) = germDiff u f + germDiff u g := by
  rw [germDiff_eq_sub, germDiff_eq_sub, germDiff_eq_sub, germ_add hf hg, germ_add hf hg]
  abel

theorem germDiff_smul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germDiff u (c • f) = c • germDiff u f := by
  rw [germDiff_eq_sub, germDiff_eq_sub, germ_smul c hf, germ_smul c hf, smul_sub]

theorem germDiff_neg {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germDiff u (-f) = -germDiff u f := by
  rw [germDiff_eq_sub, germDiff_eq_sub, germ_neg hf, germ_neg hf]
  abel

theorem germDiff_sub {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (u : Fin m → ℝ) : germDiff u (f - g) = germDiff u f - germDiff u g := by
  rw [germDiff_eq_sub, germDiff_eq_sub, germDiff_eq_sub, germ_sub hf hg, germ_sub hf hg]
  abel

theorem germDiff_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin m → ℝ) → ℝ}
    (hf : ∀ i ∈ s, f i ∈ SSpan m) (u : Fin m → ℝ) :
    germDiff u (fun y => ∑ i in s, f i y) = fun y => ∑ i in s, germDiff u (f i) y := by
  rw [germDiff_eq_sub, germ_sum s hf u, germ_sum s hf (-u)]
  funext y
  show ∑ i in s, germ (f i) u y - ∑ i in s, germ (f i) (-u) y =
    ∑ i in s, (germ (f i) u y - germ (f i) (-u) y)
  rw [Finset.sum_sub_distrib]

theorem germDiff_zero (u : Fin m → ℝ) : germDiff u (0 : (Fin m → ℝ) → ℝ) = 0 := by
  rw [germDiff_eq_sub, germ_zero, germ_zero, sub_self]

/-- Linear forms have no facet datum. -/
theorem germDiff_dot (p u : Fin m → ℝ) : germDiff u (dot p) = 0 := by
  rw [germDiff_eq_sub, germ_dot, germ_dot, sub_self]

theorem germDiff_mem_SSpan {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (u : Fin m → ℝ) :
    germDiff u f ∈ SSpan m := by
  rw [germDiff_eq_sub]
  exact Submodule.sub_mem _ (germ_mem_SSpan hf u) (germ_mem_SSpan hf (-u))

/-- **Facet datum of a support function**: the difference of the support functions of the
two opposite faces. -/
theorem germDiff_hS {S : Finset (Fin m → ℝ)} (h : S.Nonempty) (u : Fin m → ℝ) :
    germDiff u (hS S) = hS (face u S) - hS (face (-u) S) := by
  rw [germDiff_eq_sub, germ_hS h, germ_hS h]

/-- The facet datum depends only on the ray of the direction. -/
theorem germDiff_pos_smul {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) {c : ℝ} (hc : 0 < c)
    (u : Fin m → ℝ) : germDiff (c • u) f = germDiff u f := by
  rw [germDiff_eq_sub, germDiff_eq_sub, germ_pos_smul hf hc, ← smul_neg,
    germ_pos_smul hf hc]

/-! ## Linear changes of variables -/

/-- The support function of a linear image: `hS (A S) y = hS S (Aᵀ y)`. -/
theorem hS_image_mulVec (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n → ℝ))
    (y : Fin m → ℝ) : hS (S.image A.mulVec) y = hS S (Aᵀ.mulVec y) := by
  by_cases h : S.Nonempty
  · rw [hS_of_nonempty (h.image A.mulVec), hS_of_nonempty h, Finset.sup'_image]
    have e : (fun p : Fin m → ℝ => dot p y) ∘ A.mulVec = fun p => dot p (Aᵀ.mulVec y) :=
      funext fun p => dot_mulVec A p y
    rw [e]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.image_empty, hS_empty, hS_empty]

/-- Germs commute with the substitution `y ↦ Aᵀ y`. -/
theorem germ_comp_mulVec (A : Matrix (Fin m) (Fin n) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) (u : Fin m → ℝ) :
    germ (fun y => f (Aᵀ.mulVec y)) u = fun y => germ f (Aᵀ.mulVec u) (Aᵀ.mulVec y) :=
  germ_eq_of_isGerm ((isGerm_germ_of_mem_SSpan hf (Aᵀ.mulVec u)).comp_mulVec Aᵀ)

/-- Germ differences commute with the substitution `y ↦ Aᵀ y`. -/
theorem germDiff_comp_mulVec (A : Matrix (Fin m) (Fin n) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) (u : Fin m → ℝ) :
    germDiff u (fun y => f (Aᵀ.mulVec y)) =
      fun y => germDiff (Aᵀ.mulVec u) f (Aᵀ.mulVec y) := by
  funext y
  show germ (fun y => f (Aᵀ.mulVec y)) u y - germ (fun y => f (Aᵀ.mulVec y)) (-u) y =
    germ f (Aᵀ.mulVec u) (Aᵀ.mulVec y) - germ f (-Aᵀ.mulVec u) (Aᵀ.mulVec y)
  rw [germ_comp_mulVec A hf u, germ_comp_mulVec A hf (-u), Matrix.mulVec_neg]

/-- `SSpan` is stable under the substitution `y ↦ Aᵀ y`. -/
theorem comp_mulVec_mem_SSpan (A : Matrix (Fin m) (Fin n) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) : (fun y => f (Aᵀ.mulVec y)) ∈ SSpan m := by
  refine Submodule.span_induction
    (p := fun f : (Fin n → ℝ) → ℝ => (fun y => f (Aᵀ.mulVec y)) ∈ SSpan m) hf ?_ ?_ ?_ ?_
  · rintro _ ⟨S, hSne, rfl⟩
    show (fun y => hS S (Aᵀ.mulVec y)) ∈ SSpan m
    have e : (fun y => hS S (Aᵀ.mulVec y)) = hS (S.image A.mulVec) :=
      funext fun y => (hS_image_mulVec A S y).symm
    rw [e]
    exact hS_mem_SSpan (hSne.image _)
  · exact Submodule.zero_mem _
  · intro f₁ f₂ h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  · intro c f h
    exact Submodule.smul_mem _ c h

/-! ## `LSpan ≤ SSpan` -/

/-- Lower-dimensional support functions are support functions. -/
theorem LSpan_le_SSpan (m k : ℕ) : LSpan m k ≤ SSpan m := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨S, hSne, -, hfS⟩
  refine Submodule.subset_span ⟨S, hSne, ?_⟩
  funext y
  rw [hfS y, hS_of_nonempty hSne]

end MaxNN.ParamidGeom
