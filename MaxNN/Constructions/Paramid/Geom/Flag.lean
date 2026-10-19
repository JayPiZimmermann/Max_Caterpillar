import MaxNN.Constructions.Paramid.Geom.Germ

/-!
# Flag functionals

Module `M-Flag` of the geometric core (`work/depth2_simplex/lean_core/BLUEPRINT.md`).

The flag functional `flagFun us` (`Geom/Defs.lean`) applies the facet data
`germDiff u₁, …, germDiff u_r` in turn and evaluates the result at the last direction `u_r`.
This file proves the properties of flag functionals that the geometric core uses.

* **Dimension count.**  If `⟨u, ·⟩` is constant on a point set `S`, both faces `face (±u) S`
  are `S` itself (`face_eq_self_of_orth`) and the germ difference of `hS S` vanishes; otherwise
  both faces have strictly smaller affine dimension (`finrank_vectorSpan_face_lt`).  Hence
  `germDiff u` maps `LSpan m (k + 1)` into `LSpan m k` (`germDiff_mem_LSpan`) and kills
  `LSpan m 0` (`germDiff_eq_zero_of_mem_LSpan_zero`), and a flag functional of length
  `≥ k + 1` kills `LSpan m k` (`iterGermDiff_eq_zero_of_mem_LSpan`,
  `flagFun_eq_zero_of_mem_LSpan`).
* **Linearity** on the span `SSpan m` of support functions (`iterGermDiff_add`, `_smul`,
  `_sum`, `flagFun_add`, `_smul`, `_sum`, `_sub`, …), and invariance under adding a linear form
  (`flagFun_add_dot`).
* **Transport** through a linear substitution `y ↦ Aᵀ y`: the flag `us` becomes `us.map Aᵀ`
  (`iterGermDiff_comp_mulVec`, `flagFun_comp_mulVec`).  A flag `u :: us` of `ℝ^{n+1}` restricts
  to the flag `us.map B` of `ℝ^n` when `ker B` lies on the line through `u`
  (`isFlag_map_mulVec_of_isFlag_cons`), and conversely (`isFlag_cons_of_isFlag_map_mulVec`).
* **List bookkeeping**: `flagFun_cons` (peel off the first direction of a flag of length
  `≥ 2`), `flagFun_append`, `iterGermDiff_append`, `flagFun_singleton`; the first direction
  only matters up to positive scaling, and reversing it changes the sign (`flagFun_cons_neg`,
  `flagFun_cons_pos_smul`, `germDiff_neg_dir`).
* **Length one** (the base case of the completeness theorem): `Λ_{[u]} (hS S)` is the width
  `hS S u + hS S (−u)` of `S` in direction `u` (`flagFun_singleton_hS`), and the flags of `ℝ¹`
  are the nonzero directions (`isFlag_singleton_iff`).  Nonvacuity: the flag functional of the
  unit segment of `ℝ` is `1` (`flagFun_unit_segment`).

Generic helpers live in the sub-namespace `FlagAux`, so that they cannot collide with helpers of
the same name in sibling modules of `MaxNN.ParamidGeom`.
-/

namespace MaxNN.ParamidGeom

open BigOperators FiniteDimensional
open scoped Matrix

variable {m n : ℕ}

/-! ## Generic helpers -/

namespace FlagAux

/-- `⟨−u, y⟩ = −⟨u, y⟩`. -/
theorem dot_neg_left (u y : Fin m → ℝ) : dot (-u) y = -dot u y := by
  show ∑ i, (-u) i * y i = -∑ i, u i * y i
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => neg_mul (u i) (y i)

/-- The last entry of a mapped list is the image of the last entry. -/
theorem getLast?_map {α β : Type*} (g : α → β) :
    ∀ l : List α, (l.map g).getLast? = (l.getLast?).map g
  | [] => rfl
  | [_] => rfl
  | _ :: b :: l => getLast?_map g (b :: l)

/-- The evaluation point of a flag functional, after mapping the flag by `g` with `g a = b`. -/
theorem getLast?_getD_map {α β : Type*} (g : α → β) {a : α} {b : β} (hab : g a = b)
    (l : List α) : ((l.map g).getLast?).getD b = g ((l.getLast?).getD a) := by
  subst hab
  rw [getLast?_map]
  exact Option.getD_map g a _

/-- A support function of a nonempty point set of affine dimension `≤ k` lies in `LSpan m k`. -/
theorem hS_mem_LSpan {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) {k : ℕ}
    (hdim : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k) : hS S ∈ LSpan m k :=
  Submodule.subset_span ⟨S, hne, hdim, fun y => hS_of_nonempty hne y⟩

/-- A linear form lies in every `LSpan m k` (a single point has dimension `0`). -/
theorem dot_mem_LSpan (t : Fin m → ℝ) (k : ℕ) : dot t ∈ LSpan m k :=
  Submodule.subset_span (dot_mem_lowerDimSupport t k)

/-- Two points of the same face have the same value of `⟨u, ·⟩`. -/
theorem dot_eq_of_mem_face {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} {p q : Fin m → ℝ}
    (hp : p ∈ face u S) (hq : q ∈ face u S) : dot u p = dot u q :=
  le_antisymm ((mem_face.mp hq).2 p (mem_face.mp hp).1) ((mem_face.mp hp).2 q (mem_face.mp hq).1)

/-- The direction space of a face in direction `u` is orthogonal to `u`. -/
theorem vectorSpan_face_le_ker (u : Fin m → ℝ) (S : Finset (Fin m → ℝ)) :
    vectorSpan ℝ (face u S : Set (Fin m → ℝ)) ≤ LinearMap.ker (SupportCut.dotL u) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro x ⟨p, q, hp, hq, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, SupportCut.dotL_apply]
  show dot u (p - q) = 0
  rw [SupportCut.dot_sub_right, dot_eq_of_mem_face hp hq, sub_self]

/-- Linear independence of the entries of `u :: us`: the entries of `us` are independent and
`u` is not in their span. -/
theorem linearIndependent_get_cons_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (u : V)
    (us : List V) :
    LinearIndependent ℝ (fun i : Fin (u :: us).length => (u :: us).get i) ↔
      LinearIndependent ℝ (fun i : Fin us.length => us.get i) ∧
        u ∉ Submodule.span ℝ (Set.range (fun i : Fin us.length => us.get i)) :=
  linearIndependent_fin_succ

/-- The entries of a mapped list are the images of the entries, reindexed along
`List.length_map`. -/
theorem get_map_eq_comp {α β : Type*} (g : α → β) (l : List α) :
    (fun i : Fin (l.map g).length => (l.map g).get i) =
      (g ∘ fun i : Fin l.length => l.get i) ∘ finCongr (List.length_map l g) := by
  funext i
  simp only [Function.comp_apply, List.get_map]
  rfl

end FlagAux

open FlagAux

/-! ## Faces and dimension -/

/-- If `⟨u, ·⟩` is constant on `S`, the face of `S` in direction `u` is all of `S`. -/
theorem face_eq_self_of_orth {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)}
    (h : ∀ p ∈ S, ∀ q ∈ S, dot u (p - q) = 0) : face u S = S := by
  ext p
  rw [mem_face]
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, fun q hq => ?_⟩⟩
  have hpq := h p hp q hq
  rw [SupportCut.dot_sub_right, sub_eq_zero] at hpq
  exact le_of_eq hpq.symm

/-- A face has affine dimension at most that of the point set. -/
theorem finrank_vectorSpan_face_le (u : Fin m → ℝ) (S : Finset (Fin m → ℝ)) :
    finrank ℝ (vectorSpan ℝ (face u S : Set (Fin m → ℝ))) ≤
      finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) :=
  Submodule.finrank_mono (vectorSpan_mono ℝ (Finset.coe_subset.mpr (face_subset u S)))

/-- **A proper face drops the dimension.**  If `⟨u, ·⟩` is not constant on `S`, the face of `S`
in direction `u` has strictly smaller affine dimension than `S`. -/
theorem finrank_vectorSpan_face_lt {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)} (_hne : S.Nonempty)
    (h : ∃ p ∈ S, ∃ q ∈ S, dot u (p - q) ≠ 0) :
    finrank ℝ (vectorSpan ℝ (face u S : Set (Fin m → ℝ))) <
      finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  refine Submodule.finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.mpr
    ⟨vectorSpan_mono ℝ (Finset.coe_subset.mpr (face_subset u S)), p - q, ?_,
      fun hmem => hpq ?_⟩)
  · rw [← vsub_eq_sub]
    exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq)
  · have h' := vectorSpan_face_le_ker u S hmem
    rwa [LinearMap.mem_ker, SupportCut.dotL_apply] at h'

/-- At the direction `u` itself, the support function of the face `face u S` is that of `S`. -/
theorem hS_face_apply_self {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) (u : Fin m → ℝ) :
    hS (face u S) u = hS S u := by
  obtain ⟨p, hp, hpe⟩ := GermAux.exists_mem_hS_eq (face_nonempty hne u) u
  rw [hpe, hS_eq_dot_of_mem_face hp]

/-- At the direction `u`, the support function of the opposite face `face (−u) S` is
`−hS S (−u)`, the minimum of `⟨·, u⟩` on `S`. -/
theorem hS_face_neg_apply {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) (u : Fin m → ℝ) :
    hS (face (-u) S) u = -hS S (-u) := by
  obtain ⟨p, hp, hpe⟩ := GermAux.exists_mem_hS_eq (face_nonempty hne (-u)) u
  rw [hpe, hS_eq_dot_of_mem_face hp, SupportCut.dot_comm p (-u), dot_neg_left, neg_neg,
    SupportCut.dot_comm]

/-! ## A germ difference lowers the dimension by one -/

/-- Reversing the direction negates the facet datum. -/
theorem germDiff_neg_dir (u : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    germDiff (-u) f = -germDiff u f := by
  funext y
  show germ f (-u) y - germ f (- -u) y = -(germ f u y - germ f (-u) y)
  rw [neg_neg]
  ring

/-- If `⟨u, ·⟩` is constant on `S`, the facet datum of `hS S` in direction `u` vanishes. -/
theorem germDiff_hS_eq_zero_of_orth {u : Fin m → ℝ} {S : Finset (Fin m → ℝ)}
    (hne : S.Nonempty) (h : ∀ p ∈ S, ∀ q ∈ S, dot u (p - q) = 0) : germDiff u (hS S) = 0 := by
  have h' : ∀ p ∈ S, ∀ q ∈ S, dot (-u) (p - q) = 0 := fun p hp q hq => by
    rw [dot_neg_left, h p hp q hq, neg_zero]
  rw [germDiff_hS hne u, face_eq_self_of_orth h, face_eq_self_of_orth h', sub_self]

/-- The facet datum of the support function of a point set of affine dimension `≤ k + 1` lies
in `LSpan m k`. -/
theorem germDiff_hS_mem_LSpan {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) {k : ℕ}
    (hdim : finrank ℝ (vectorSpan ℝ (S : Set (Fin m → ℝ))) ≤ k + 1) (u : Fin m → ℝ) :
    germDiff u (hS S) ∈ LSpan m k := by
  by_cases h : ∃ p ∈ S, ∃ q ∈ S, dot u (p - q) ≠ 0
  · have h' : ∃ p ∈ S, ∃ q ∈ S, dot (-u) (p - q) ≠ 0 := by
      obtain ⟨p, hp, q, hq, hpq⟩ := h
      exact ⟨p, hp, q, hq, by rw [dot_neg_left]; exact neg_ne_zero.mpr hpq⟩
    rw [germDiff_hS hne u]
    exact Submodule.sub_mem _
      (hS_mem_LSpan (face_nonempty hne u)
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (finrank_vectorSpan_face_lt hne h) hdim)))
      (hS_mem_LSpan (face_nonempty hne (-u))
        (Nat.lt_succ_iff.mp (lt_of_lt_of_le (finrank_vectorSpan_face_lt hne h') hdim)))
  · push_neg at h
    rw [germDiff_hS_eq_zero_of_orth hne h]
    exact Submodule.zero_mem _

/-- **A germ difference lowers the dimension by one**: `germDiff u` maps `LSpan m (k + 1)` into
`LSpan m k`. -/
theorem germDiff_mem_LSpan {f : (Fin m → ℝ) → ℝ} {k : ℕ} (hf : f ∈ LSpan m (k + 1))
    (u : Fin m → ℝ) : germDiff u f ∈ LSpan m k := by
  have key : f ∈ SSpan m ∧ germDiff u f ∈ LSpan m k := by
    refine Submodule.span_induction
      (p := fun g => g ∈ SSpan m ∧ germDiff u g ∈ LSpan m k) hf ?_ ?_ ?_ ?_
    · rintro g ⟨S, hne, hdim, hgS⟩
      obtain rfl : g = hS S := funext fun y => by rw [hgS y, hS_of_nonempty hne]
      exact ⟨GermAux.hS_mem_SSpan hne, germDiff_hS_mem_LSpan hne hdim u⟩
    · refine ⟨Submodule.zero_mem _, ?_⟩
      rw [germDiff_zero]
      exact Submodule.zero_mem _
    · rintro g₁ g₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
      refine ⟨Submodule.add_mem _ h₁ h₂, ?_⟩
      rw [germDiff_add h₁ h₂]
      exact Submodule.add_mem _ h₁' h₂'
    · rintro c g ⟨h, h'⟩
      refine ⟨Submodule.smul_mem _ c h, ?_⟩
      rw [germDiff_smul c h]
      exact Submodule.smul_mem _ c h'
  exact key.2

/-- **A germ difference kills zero-dimensional support functions** (the linear forms). -/
theorem germDiff_eq_zero_of_mem_LSpan_zero {f : (Fin m → ℝ) → ℝ} (hf : f ∈ LSpan m 0)
    (u : Fin m → ℝ) : germDiff u f = 0 := by
  have key : f ∈ SSpan m ∧ germDiff u f = 0 := by
    refine Submodule.span_induction
      (p := fun g => g ∈ SSpan m ∧ germDiff u g = 0) hf ?_ ?_ ?_ ?_
    · rintro g ⟨S, hne, hdim, hgS⟩
      obtain rfl : g = hS S := funext fun y => by rw [hgS y, hS_of_nonempty hne]
      refine ⟨GermAux.hS_mem_SSpan hne, germDiff_hS_eq_zero_of_orth hne ?_⟩
      by_contra hcon
      push_neg at hcon
      exact Nat.not_lt_zero _ (lt_of_lt_of_le (finrank_vectorSpan_face_lt hne hcon) hdim)
    · exact ⟨Submodule.zero_mem _, germDiff_zero u⟩
    · rintro g₁ g₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
      exact ⟨Submodule.add_mem _ h₁ h₂, by rw [germDiff_add h₁ h₂, h₁', h₂', add_zero]⟩
    · rintro c g ⟨h, h'⟩
      exact ⟨Submodule.smul_mem _ c h, by rw [germDiff_smul c h, h', smul_zero]⟩
  exact key.2

/-! ## Iterated germ differences -/

theorem iterGermDiff_mem_SSpan {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (us : List (Fin m → ℝ)) : iterGermDiff us f ∈ SSpan m := by
  induction us generalizing f with
  | nil => exact hf
  | cons u _ ih => exact ih (germDiff_mem_SSpan hf u)

theorem iterGermDiff_zero (us : List (Fin m → ℝ)) :
    iterGermDiff us (0 : (Fin m → ℝ) → ℝ) = 0 := by
  induction us with
  | nil => rfl
  | cons u us ih => rw [iterGermDiff_cons, germDiff_zero, ih]

theorem iterGermDiff_add {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (us : List (Fin m → ℝ)) :
    iterGermDiff us (f + g) = iterGermDiff us f + iterGermDiff us g := by
  induction us generalizing f g with
  | nil => rfl
  | cons u us ih =>
    rw [iterGermDiff_cons, iterGermDiff_cons, iterGermDiff_cons, germDiff_add hf hg u]
    exact ih (germDiff_mem_SSpan hf u) (germDiff_mem_SSpan hg u)

theorem iterGermDiff_smul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (us : List (Fin m → ℝ)) : iterGermDiff us (c • f) = c • iterGermDiff us f := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    rw [iterGermDiff_cons, iterGermDiff_cons, germDiff_smul c hf u]
    exact ih (germDiff_mem_SSpan hf u)

theorem iterGermDiff_const_mul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (us : List (Fin m → ℝ)) :
    iterGermDiff us (fun y => c * f y) = fun y => c * iterGermDiff us f y :=
  iterGermDiff_smul c hf us

theorem iterGermDiff_neg {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (us : List (Fin m → ℝ)) :
    iterGermDiff us (-f) = -iterGermDiff us f := by
  have h := iterGermDiff_smul (-1) hf us
  rwa [neg_one_smul, neg_one_smul] at h

theorem iterGermDiff_sub {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (us : List (Fin m → ℝ)) :
    iterGermDiff us (f - g) = iterGermDiff us f - iterGermDiff us g := by
  rw [sub_eq_add_neg, iterGermDiff_add hf (Submodule.neg_mem _ hg), iterGermDiff_neg hg,
    ← sub_eq_add_neg]

theorem iterGermDiff_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin m → ℝ) → ℝ}
    (hf : ∀ i ∈ s, f i ∈ SSpan m) (us : List (Fin m → ℝ)) :
    iterGermDiff us (fun y => ∑ i in s, f i y) = fun y => ∑ i in s, iterGermDiff us (f i) y := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    rw [iterGermDiff_cons, germDiff_sum s hf u]
    exact ih (f := fun i => germDiff u (f i)) (fun i hi => germDiff_mem_SSpan (hf i hi) u)

/-- Iterated germ differences along a concatenation: first `us`, then `vs`. -/
theorem iterGermDiff_append (us vs : List (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) :
    iterGermDiff (us ++ vs) f = iterGermDiff vs (iterGermDiff us f) := by
  induction us generalizing f with
  | nil => rfl
  | cons u _ ih => exact ih (germDiff u f)

/-- `r` germ differences lower the dimension by `r`. -/
theorem iterGermDiff_mem_LSpan {f : (Fin m → ℝ) → ℝ} {k : ℕ} (us : List (Fin m → ℝ))
    (hf : f ∈ LSpan m (k + us.length)) : iterGermDiff us f ∈ LSpan m k := by
  induction us generalizing f with
  | nil => exact hf
  | cons u us ih => exact ih (germDiff_mem_LSpan (k := k + us.length) hf u)

/-- **Iterated germ differences kill lower-dimensional support functions**: at least `k + 1`
germ differences vanish on `LSpan m k`. -/
theorem iterGermDiff_eq_zero_of_mem_LSpan {f : (Fin m → ℝ) → ℝ} {k : ℕ} (hf : f ∈ LSpan m k)
    (us : List (Fin m → ℝ)) (h : k + 1 ≤ us.length) : iterGermDiff us f = 0 := by
  induction us generalizing f k with
  | nil => exact absurd h (Nat.not_succ_le_zero k)
  | cons u us ih =>
    cases k with
    | zero =>
      show iterGermDiff us (germDiff u f) = 0
      rw [germDiff_eq_zero_of_mem_LSpan_zero hf u, iterGermDiff_zero]
    | succ k => exact ih (germDiff_mem_LSpan hf u) (Nat.le_of_succ_le_succ h)

/-- Iterated germ differences agree on two functions whose difference is lower-dimensional. -/
theorem iterGermDiff_eq_of_sub_mem_LSpan {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (hg : g ∈ SSpan m) {k : ℕ} (hfg : f - g ∈ LSpan m k) (us : List (Fin m → ℝ))
    (h : k + 1 ≤ us.length) : iterGermDiff us f = iterGermDiff us g := by
  have h0 := iterGermDiff_eq_zero_of_mem_LSpan hfg us h
  rw [iterGermDiff_sub hf hg] at h0
  exact sub_eq_zero.mp h0

/-- Adding a linear form does not change a nonempty iterated germ difference. -/
theorem iterGermDiff_add_dot {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (t : Fin m → ℝ)
    (us : List (Fin m → ℝ)) (h : 1 ≤ us.length) :
    iterGermDiff us (f + dot t) = iterGermDiff us f := by
  rw [iterGermDiff_add hf (GermAux.dot_mem_SSpan t) us,
    iterGermDiff_eq_zero_of_mem_LSpan (k := 0) (dot_mem_LSpan t 0) us h, add_zero]

/-- **Transport of iterated germ differences** through the substitution `y ↦ Aᵀ y`. -/
theorem iterGermDiff_comp_mulVec (A : Matrix (Fin m) (Fin n) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) (us : List (Fin m → ℝ)) :
    iterGermDiff us (fun y => f (Aᵀ.mulVec y)) =
      fun y => iterGermDiff (us.map Aᵀ.mulVec) f (Aᵀ.mulVec y) := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    rw [iterGermDiff_cons, germDiff_comp_mulVec A hf u]
    exact ih (germDiff_mem_SSpan hf (Aᵀ.mulVec u))

/-! ## Flag functionals -/

theorem flagFun_def (us : List (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) :
    flagFun us f = iterGermDiff us f ((us.getLast?).getD 0) := rfl

theorem flagFun_nil (f : (Fin m → ℝ) → ℝ) : flagFun [] f = f 0 := rfl

theorem flagFun_singleton (u : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ) :
    flagFun [u] f = germDiff u f u := rfl

/-- A flag functional along `us ++ vs` (`vs ≠ []`) is the flag functional along `vs` of the
iterated germ difference along `us`. -/
theorem flagFun_append (us vs : List (Fin m → ℝ)) (hvs : vs ≠ []) (f : (Fin m → ℝ) → ℝ) :
    flagFun (us ++ vs) f = flagFun vs (iterGermDiff us f) := by
  show iterGermDiff (us ++ vs) f _ = iterGermDiff vs (iterGermDiff us f) _
  rw [iterGermDiff_append, List.getLast?_append_of_ne_nil us hvs]

/-- Peeling off the first direction of a flag functional of length `≥ 2`. -/
theorem flagFun_cons (u : Fin m → ℝ) (us : List (Fin m → ℝ)) (hus : us ≠ [])
    (f : (Fin m → ℝ) → ℝ) : flagFun (u :: us) f = flagFun us (germDiff u f) :=
  flagFun_append [u] us hus f

theorem flagFun_zero (us : List (Fin m → ℝ)) : flagFun us (0 : (Fin m → ℝ) → ℝ) = 0 :=
  congrFun (iterGermDiff_zero us) ((us.getLast?).getD 0)

theorem flagFun_add {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (us : List (Fin m → ℝ)) : flagFun us (f + g) = flagFun us f + flagFun us g :=
  congrFun (iterGermDiff_add hf hg us) ((us.getLast?).getD 0)

theorem flagFun_smul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (us : List (Fin m → ℝ)) : flagFun us (c • f) = c * flagFun us f :=
  congrFun (iterGermDiff_smul c hf us) ((us.getLast?).getD 0)

theorem flagFun_const_mul (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (us : List (Fin m → ℝ)) : flagFun us (fun y => c * f y) = c * flagFun us f :=
  flagFun_smul c hf us

theorem flagFun_neg {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (us : List (Fin m → ℝ)) :
    flagFun us (-f) = -flagFun us f :=
  congrFun (iterGermDiff_neg hf us) ((us.getLast?).getD 0)

theorem flagFun_sub {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (hg : g ∈ SSpan m)
    (us : List (Fin m → ℝ)) : flagFun us (f - g) = flagFun us f - flagFun us g :=
  congrFun (iterGermDiff_sub hf hg us) ((us.getLast?).getD 0)

theorem flagFun_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin m → ℝ) → ℝ}
    (hf : ∀ i ∈ s, f i ∈ SSpan m) (us : List (Fin m → ℝ)) :
    flagFun us (fun y => ∑ i in s, f i y) = ∑ i in s, flagFun us (f i) :=
  congrFun (iterGermDiff_sum s hf us) ((us.getLast?).getD 0)

/-- **Flag functionals kill lower-dimensional support functions**: a flag functional of length
`≥ k + 1` vanishes on `LSpan m k`. -/
theorem flagFun_eq_zero_of_mem_LSpan {f : (Fin m → ℝ) → ℝ} {k : ℕ} (hf : f ∈ LSpan m k)
    (us : List (Fin m → ℝ)) (h : k + 1 ≤ us.length) : flagFun us f = 0 :=
  congrFun (iterGermDiff_eq_zero_of_mem_LSpan hf us h) ((us.getLast?).getD 0)

/-- Every flag functional of `ℝ^m` (`m ≥ 1`) kills `LSpan m (m − 1)`. -/
theorem flagFun_eq_zero_of_isFlag {us : List (Fin m → ℝ)} (hus : IsFlag us) (hm : 1 ≤ m)
    {f : (Fin m → ℝ) → ℝ} (hf : f ∈ LSpan m (m - 1)) : flagFun us f = 0 :=
  flagFun_eq_zero_of_mem_LSpan hf us (by rw [hus.1]; omega)

/-- Flag functionals of length `≥ k + 1` do not see differences in `LSpan m k`. -/
theorem flagFun_eq_of_sub_mem_LSpan {f g : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m)
    (hg : g ∈ SSpan m) {k : ℕ} (hfg : f - g ∈ LSpan m k) (us : List (Fin m → ℝ))
    (h : k + 1 ≤ us.length) : flagFun us f = flagFun us g :=
  congrFun (iterGermDiff_eq_of_sub_mem_LSpan hf hg hfg us h) ((us.getLast?).getD 0)

/-- **Transport of flag functionals** through the substitution `y ↦ Aᵀ y`: the flag `us` of
`ℝ^m` becomes the list `us.map Aᵀ` of `ℝ^n`. -/
theorem flagFun_comp_mulVec (A : Matrix (Fin m) (Fin n) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) (us : List (Fin m → ℝ)) :
    flagFun us (fun y => f (Aᵀ.mulVec y)) = flagFun (us.map Aᵀ.mulVec) f := by
  show iterGermDiff us (fun y => f (Aᵀ.mulVec y)) _ = iterGermDiff (us.map Aᵀ.mulVec) f _
  rw [iterGermDiff_comp_mulVec A hf us,
    getLast?_getD_map Aᵀ.mulVec (Matrix.mulVec_zero Aᵀ) us]

/-- Adding a linear form does not change a flag functional of length `≥ 1`. -/
theorem flagFun_add_dot {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) (t : Fin m → ℝ)
    (us : List (Fin m → ℝ)) (h : 1 ≤ us.length) : flagFun us (f + dot t) = flagFun us f :=
  congrFun (iterGermDiff_add_dot hf t us h) ((us.getLast?).getD 0)

/-- Reversing the first direction of a flag functional of length `≥ 2` changes its sign. -/
theorem flagFun_cons_neg (u : Fin m → ℝ) {us : List (Fin m → ℝ)} (hus : us ≠ [])
    {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) : flagFun (-u :: us) f = -flagFun (u :: us) f := by
  rw [flagFun_cons _ _ hus, flagFun_cons _ _ hus, germDiff_neg_dir,
    flagFun_neg (germDiff_mem_SSpan hf u)]

/-- Rescaling the first direction of a flag functional of length `≥ 2` by `c > 0` does not
change it. -/
theorem flagFun_cons_pos_smul {c : ℝ} (hc : 0 < c) (u : Fin m → ℝ) {us : List (Fin m → ℝ)}
    (hus : us ≠ []) {f : (Fin m → ℝ) → ℝ} (hf : f ∈ SSpan m) :
    flagFun (c • u :: us) f = flagFun (u :: us) f := by
  rw [flagFun_cons _ _ hus, flagFun_cons _ _ hus, germDiff_pos_smul hf hc]

/-- **A flag functional along one direction is a width**:
`Λ_{[u]} (hS S) = hS S u + hS S (−u)`, the maximum minus the minimum of `⟨·, u⟩` on `S`. -/
theorem flagFun_singleton_hS {S : Finset (Fin m → ℝ)} (hne : S.Nonempty) (u : Fin m → ℝ) :
    flagFun [u] (hS S) = hS S u + hS S (-u) := by
  rw [flagFun_singleton, germDiff_hS hne u]
  show hS (face u S) u - hS (face (-u) S) u = hS S u + hS S (-u)
  rw [hS_face_apply_self hne u, hS_face_neg_apply hne u, sub_neg_eq_add]

/-! ## Flags of a hyperplane -/

/-- **Restricting a flag to a hyperplane.**  If `u :: us` is a flag of `ℝ^{n+1}` and the kernel
of `B : ℝ^{n+1} → ℝ^n` lies on the line through `u`, then `B` maps `us` to a flag of `ℝ^n`. -/
theorem isFlag_map_mulVec_of_isFlag_cons (B : Matrix (Fin n) (Fin m) ℝ) {u : Fin m → ℝ}
    {us : List (Fin m → ℝ)} (hflag : IsFlag (u :: us)) (hmn : m = n + 1)
    (hker : ∀ x, B.mulVec x = 0 → ∃ c : ℝ, x = c • u) : IsFlag (us.map B.mulVec) := by
  obtain ⟨hlen, hli⟩ := hflag
  obtain ⟨hv, hu⟩ := (linearIndependent_get_cons_iff u us).mp hli
  refine ⟨?_, ?_⟩
  · rw [List.length_map]
    rw [List.length_cons] at hlen
    omega
  · have hdisj : Disjoint (Submodule.span ℝ (Set.range (fun i : Fin us.length => us.get i)))
        (LinearMap.ker (Matrix.mulVecLin B)) := by
      refine Disjoint.mono_right ?_
        (Submodule.disjoint_span_singleton.mpr (fun h => absurd h hu))
      intro x hx
      obtain ⟨c, rfl⟩ := hker x (LinearMap.mem_ker.mp hx)
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)
    rw [get_map_eq_comp]
    exact (hv.map hdisj).comp _ (finCongr (List.length_map us B.mulVec)).injective

/-- **Extending a flag of a hyperplane.**  If `B : ℝ^{n+1} → ℝ^n` maps `us` to a flag of `ℝ^n`
and kills the nonzero vector `u`, then `u :: us` is a flag of `ℝ^{n+1}`. -/
theorem isFlag_cons_of_isFlag_map_mulVec (B : Matrix (Fin n) (Fin m) ℝ) {u : Fin m → ℝ}
    {us : List (Fin m → ℝ)} (hflag : IsFlag (us.map B.mulVec)) (hmn : m = n + 1)
    (hu : u ≠ 0) (hBu : B.mulVec u = 0) : IsFlag (u :: us) := by
  obtain ⟨hlen, hli⟩ := hflag
  rw [get_map_eq_comp] at hli
  have hcomp : LinearIndependent ℝ (B.mulVec ∘ fun i : Fin us.length => us.get i) :=
    (linearIndependent_equiv (finCongr (List.length_map us B.mulVec))).mp hli
  refine ⟨?_, ?_⟩
  · rw [List.length_map] at hlen
    rw [List.length_cons]
    omega
  · refine (linearIndependent_get_cons_iff u us).mpr
      ⟨LinearIndependent.of_comp (Matrix.mulVecLin B) hcomp, fun hmem => hu ?_⟩
    obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp hmem
    have h0 : ∑ i, c i • (B.mulVec ∘ fun i : Fin us.length => us.get i) i = 0 := by
      have e : ∑ i, c i • (B.mulVec ∘ fun i : Fin us.length => us.get i) i =
          Matrix.mulVecLin B (∑ i, c i • us.get i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smul]
        rfl
      rw [e, hc]
      exact hBu
    have hc0 := Fintype.linearIndependent_iff.mp hcomp c h0
    rw [← hc]
    exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]

/-- The flags of `ℝ¹` are the nonzero directions. -/
theorem isFlag_singleton_iff (u : Fin 1 → ℝ) : IsFlag [u] ↔ u ≠ 0 := by
  haveI : IsEmpty (Fin ([] : List (Fin 1 → ℝ)).length) := Fin.isEmpty'
  rw [IsFlag, linearIndependent_get_cons_iff, Set.range_eq_empty, Submodule.span_empty,
    Submodule.mem_bot]
  exact ⟨fun h => h.2.2, fun h => ⟨rfl, linearIndependent_empty_type, h⟩⟩

/-! ## Nonvacuity -/

/-- **Nonvacuity**: along the flag `[1]` of `ℝ`, the flag functional of the unit segment
`{0, 1}` is its length `1`; flag functionals do not vanish identically on `SSpan 1`. -/
theorem flagFun_unit_segment :
    flagFun [(1 : Fin 1 → ℝ)] (hS ({0, 1} : Finset (Fin 1 → ℝ))) = 1 := by
  rw [flagFun_singleton_hS (Finset.insert_nonempty _ _), hS_of_nonempty, hS_of_nonempty,
    Finset.sup'_insert, Finset.sup'_insert, Finset.sup'_singleton, Finset.sup'_singleton]
  · simp [dot]
  all_goals simp

end MaxNN.ParamidGeom
