import MaxNN.Constructions.Paramid.Geom.Flag
import MaxNN.Constructions.Paramid.Geom.Reconstruct

/-!
# Hyperplane charts and bookkeeping (helper for `Geom/Complete.lean`)

The completeness theorem (`Geom/Complete.lean`) groups the facets of a family of `m`-simplices by
their direction `ν` and reads each group inside its hyperplane `{⟨ν, ·⟩ = c}`, a copy of
`ℝ^{m−1}`.  This file provides the chart and the bookkeeping, in the sub-namespace
`MaxNN.ParamidGeom.CompleteAux`.

## The chart of the hyperplanes orthogonal to `ν` (`ν 0 = 1`)

The coordinate projection `Fin.tail : ℝ^{n+1} → ℝ^n` (delete the coordinate `0`) is injective on
every hyperplane `{⟨ν, ·⟩ = c}`, because `⟨ν, e₀⟩ = 1 ≠ 0`.  Its inverse on `ν^⊥` is the transpose
of `chartT ν : Matrix (Fin n) (Fin (n + 1)) ℝ`, `chartT ν y = (y_{j+1} − ν_{j+1} y_0)_j`
(`chartT_mulVec`):

* `dot_eq_dot_tail_chartT`: `⟨p, y⟩ = ⟨tail p, chartT ν y⟩ + ⟨ν, p⟩ y_0`;
* `chartT_mulVec_self`: `chartT ν ν = 0`; `chartT_mulVec_cons_zero`: `chartT ν (0, z) = z`;
* `chartT_transpose_mulVec_tail`: `(chartT ν)ᵀ (tail p) = p − ⟨ν, p⟩ e₀`;
* `hS_image_univ_eq_chartT`: a point set `S` in the hyperplane `{⟨ν, ·⟩ = c}` has
  `h_S y = h_{tail S} (chartT ν y) + c y_0`;
* `affineIndependent_tail`: deleting the coordinate `0` keeps such a point set affinely
  independent;
* `isFlag_cons_map_cons_zero`: a flag `us` of `ℝ^n` lifts to the flag `ν :: (0, us)` of
  `ℝ^{n+1}`, and `chartT ν` maps `(0, us)` back to `us` (`map_cons_zero_map_chartT`).

## Linear substitutions

`comp_mulVec_mem_LSpan`: `LSpan` is stable under `y ↦ Aᵀ y` (a linear image of a point set has at
most its affine dimension, `finrank_vectorSpan_image_mulVec_le`); the variants `…'` are stated for
`y ↦ M y` directly, as are `comp_mulVec_mem_SSpan'` and `flagFun_comp_mulVec'`.

## Bookkeeping

`sum_mul_mem`, `sum_fun_mem` (finite combinations stay in a submodule of functions),
`sum_mul_sum_filter_eq_sum_subtype` (reindexing a filtered double sum by a subtype),
`germDiff_sum_mul_hS` (the facet datum of a combination of support functions),
`hS_smul_of_nonneg` (positive homogeneity of support functions).
-/

namespace MaxNN.ParamidGeom

open BigOperators
open scoped Matrix

noncomputable section

namespace CompleteAux

variable {m n : ℕ}

/-! ## Finite combinations -/

/-- A finite combination `y ↦ ∑ c_x f_x(y)` of functions of a submodule lies in it. -/
theorem sum_mul_mem {S : Submodule ℝ ((Fin m → ℝ) → ℝ)} {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    {f : κ → (Fin m → ℝ) → ℝ} (hf : ∀ x ∈ s, f x ∈ S) :
    (fun y => ∑ x in s, c x * f x y) ∈ S := by
  have e : (fun y => ∑ x in s, c x * f x y) = ∑ x in s, c x • f x := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (hf x hx)

/-- A finite sum `y ↦ ∑ f_x(y)` of functions of a submodule lies in it. -/
theorem sum_fun_mem {S : Submodule ℝ ((Fin m → ℝ) → ℝ)} {κ : Type*} (s : Finset κ)
    {f : κ → (Fin m → ℝ) → ℝ} (hf : ∀ x ∈ s, f x ∈ S) : (fun y => ∑ x in s, f x y) ∈ S := by
  have e : (fun y => ∑ x in s, f x y) = ∑ x in s, f x := by
    funext y
    rw [Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ hf

/-- Reindexing a filtered double sum by the subtype of the filtered pairs. -/
theorem sum_mul_sum_filter_eq_sum_subtype {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ → Prop) [∀ i, DecidablePred (p i)] (a : ι → ℝ) (T : ι → κ → ℝ) :
    ∑ i, a i * ∑ j in Finset.univ.filter (p i), T i j =
      ∑ x : {x : ι × κ // p x.1 x.2}, a x.1.1 * T x.1.1 x.1.2 := by
  have h1 : ∑ i, a i * ∑ j in Finset.univ.filter (p i), T i j =
      ∑ x in Finset.univ.filter (fun x : ι × κ => p x.1 x.2), a x.1 * T x.1 x.2 := by
    rw [Finset.sum_filter,
      Fintype.sum_prod_type' (f := fun i j => if p i j then a i * T i j else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [h1]
  exact Finset.sum_subtype _ (fun x => by simp) (fun x : ι × κ => a x.1 * T x.1 x.2)

/-! ## Support functions -/

/-- The facets of a simplex are nonempty. -/
theorem facet_nonempty {k : ℕ} (p : Fin (k + 1 + 1) → Fin m → ℝ) (j : Fin (k + 1 + 1)) :
    ((Finset.univ.erase j).image p).Nonempty := by
  rw [← FacetGermAux.image_univ_comp_succAbove]
  exact Finset.univ_nonempty.image _

/-- Positive homogeneity of support functions. -/
theorem hS_smul_of_nonneg (S : Finset (Fin m → ℝ)) {c : ℝ} (hc : 0 ≤ c) (y : Fin m → ℝ) :
    hS S (c • y) = c * hS S y := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [GermAux.hS_empty, GermAux.hS_empty, mul_zero]
  · apply le_antisymm
    · rw [hS_of_nonempty hne (c • y)]
      refine Finset.sup'_le _ _ fun p hp => ?_
      show dot p (c • y) ≤ c * hS S y
      rw [SupportCut.dot_smul_right]
      exact mul_le_mul_of_nonneg_left (GermAux.dot_le_hS hp y) hc
    · obtain ⟨p, hp, hpe⟩ := GermAux.exists_mem_hS_eq hne y
      rw [hpe, ← SupportCut.dot_smul_right]
      exact GermAux.dot_le_hS hp (c • y)

/-- The facet datum of a finite combination of support functions. -/
theorem germDiff_sum_mul_hS {κ : Type*} (s : Finset κ) (a : κ → ℝ) (S : κ → Finset (Fin m → ℝ))
    (hne : ∀ i, (S i).Nonempty) (u : Fin m → ℝ) :
    germDiff u (fun y => ∑ i in s, a i * hS (S i) y) =
      fun y => ∑ i in s, a i * germDiff u (hS (S i)) y := by
  rw [germDiff_sum s (f := fun i y => a i * hS (S i) y)
    (fun i _ => Submodule.smul_mem _ (a i) (GermAux.hS_mem_SSpan (hne i))) u]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (fun y => a i * hS (S i) y) = a i • hS (S i) := rfl
  rw [e, germDiff_smul (a i) (GermAux.hS_mem_SSpan (hne i)) u]
  rfl

/-! ## Linear substitutions -/

/-- A linear image of a point set has at most its affine dimension. -/
theorem finrank_vectorSpan_image_mulVec_le (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n → ℝ)) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ ((S.image A.mulVec : Finset (Fin m → ℝ)) : Set (Fin m → ℝ))) ≤
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (S : Set (Fin n → ℝ))) := by
  have e : ((S.image A.mulVec : Finset (Fin m → ℝ)) : Set (Fin m → ℝ)) =
      (Matrix.mulVecLin A).toAffineMap '' (S : Set (Fin n → ℝ)) := by
    rw [Finset.coe_image, LinearMap.coe_toAffineMap]
    rfl
  rw [e, ← AffineMap.vectorSpan_image_eq_submodule_map]
  exact Submodule.finrank_map_le _ _

/-- `LSpan` is stable under the substitution `y ↦ Aᵀ y`. -/
theorem comp_mulVec_mem_LSpan (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ LSpan n k) : (fun y => f (Aᵀ.mulVec y)) ∈ LSpan m k := by
  refine Submodule.span_induction
    (p := fun f : (Fin n → ℝ) → ℝ => (fun y => f (Aᵀ.mulVec y)) ∈ LSpan m k) hf ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨S, hne, hdim, rfl⟩ := Sweep.eq_hS_of_mem_lowerDimSupport hg
    show (fun y => hS S (Aᵀ.mulVec y)) ∈ LSpan m k
    have e : (fun y => hS S (Aᵀ.mulVec y)) = hS (S.image A.mulVec) :=
      funext fun y => (hS_image_mulVec A S y).symm
    rw [e]
    exact Sweep.hS_mem_LSpan (hne.image _) (le_trans (finrank_vectorSpan_image_mulVec_le A S) hdim)
  · exact Submodule.zero_mem _
  · intro f₁ f₂ h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  · intro c f h
    exact Submodule.smul_mem _ c h

/-- `LSpan` is stable under the substitution `y ↦ M y`. -/
theorem comp_mulVec_mem_LSpan' (M : Matrix (Fin n) (Fin m) ℝ) {k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ LSpan n k) : (fun y => f (M.mulVec y)) ∈ LSpan m k := by
  have h := comp_mulVec_mem_LSpan Mᵀ hf
  rwa [Matrix.transpose_transpose] at h

/-- `SSpan` is stable under the substitution `y ↦ M y`. -/
theorem comp_mulVec_mem_SSpan' (M : Matrix (Fin n) (Fin m) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) : (fun y => f (M.mulVec y)) ∈ SSpan m := by
  have h := comp_mulVec_mem_SSpan Mᵀ hf
  rwa [Matrix.transpose_transpose] at h

/-- Transport of flag functionals through the substitution `y ↦ M y`. -/
theorem flagFun_comp_mulVec' (M : Matrix (Fin n) (Fin m) ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ SSpan n) (us : List (Fin m → ℝ)) :
    flagFun us (fun y => f (M.mulVec y)) = flagFun (us.map M.mulVec) f := by
  have h := flagFun_comp_mulVec Mᵀ hf us
  rwa [Matrix.transpose_transpose] at h

/-! ## The chart of the hyperplanes orthogonal to `ν` -/

/-- `⟨e_k, y⟩ = y_k`. -/
theorem dot_single_left (k : Fin m) (y : Fin m → ℝ) : dot (Pi.single k 1) y = y k := by
  rw [SupportCut.dot_comm]
  exact FacetGermAux.dot_single y k

/-- The transposed chart of the hyperplanes orthogonal to `ν`:
`chartT ν y = (y_{j+1} − ν_{j+1} y_0)_j` (`chartT_mulVec`).  For `ν 0 = 1` its transpose maps
`ℝ^n` isomorphically onto `ν^⊥`, inverting the deletion of the coordinate `0`. -/
def chartT (ν : Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin (n + 1)) ℝ :=
  Matrix.of fun j => Pi.single j.succ 1 - ν j.succ • Pi.single 0 1

theorem chartT_mulVec (ν y : Fin (n + 1) → ℝ) :
    (chartT ν).mulVec y = fun j => y j.succ - ν j.succ * y 0 := by
  funext j
  show dot (Pi.single j.succ 1 - ν j.succ • Pi.single 0 1) y = y j.succ - ν j.succ * y 0
  rw [SupportCut.dot_sub_left, SupportCut.dot_smul_left, dot_single_left, dot_single_left]

/-- `⟨p, y⟩ = ⟨tail p, chartT ν y⟩ + ⟨ν, p⟩ y_0` (for `ν 0 = 1`). -/
theorem dot_eq_dot_tail_chartT {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1) (p y : Fin (n + 1) → ℝ) :
    dot p y = dot (Fin.tail p) ((chartT ν).mulVec y) + dot ν p * y 0 := by
  rw [chartT_mulVec]
  have h1 : ∑ j : Fin n, p j.succ * (ν j.succ * y 0) =
      (∑ j : Fin n, ν j.succ * p j.succ) * y 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : dot (Fin.tail p) (fun j => y j.succ - ν j.succ * y 0) =
      ∑ j : Fin n, p j.succ * y j.succ - ∑ j : Fin n, p j.succ * (ν j.succ * y 0) := by
    show ∑ j : Fin n, p j.succ * (y j.succ - ν j.succ * y 0) = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : dot p y = p 0 * y 0 + ∑ j : Fin n, p j.succ * y j.succ := Fin.sum_univ_succ _
  have h4 : dot ν p = ν 0 * p 0 + ∑ j : Fin n, ν j.succ * p j.succ := Fin.sum_univ_succ _
  rw [h2, h3, h4, h1, hν0]
  ring

/-- `chartT ν` kills `ν` (for `ν 0 = 1`). -/
theorem chartT_mulVec_self {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1) : (chartT ν).mulVec ν = 0 := by
  rw [chartT_mulVec]
  funext j
  show ν j.succ - ν j.succ * ν 0 = 0
  rw [hν0, mul_one, sub_self]

/-- `chartT ν (0, z) = z`. -/
theorem chartT_mulVec_cons_zero (ν : Fin (n + 1) → ℝ) (z : Fin n → ℝ) :
    (chartT ν).mulVec (Fin.cons 0 z : Fin (n + 1) → ℝ) = z := by
  rw [chartT_mulVec]
  funext j
  show (Fin.cons 0 z : Fin (n + 1) → ℝ) j.succ - ν j.succ * (Fin.cons 0 z : Fin (n + 1) → ℝ) 0 =
    z j
  rw [Fin.cons_succ, Fin.cons_zero, mul_zero, sub_zero]

/-- The inverse chart: `(chartT ν)ᵀ (tail p) = p − ⟨ν, p⟩ e₀` (for `ν 0 = 1`). -/
theorem chartT_transpose_mulVec_tail {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1)
    (p : Fin (n + 1) → ℝ) :
    (chartT ν)ᵀ.mulVec (Fin.tail p) = p - dot ν p • (Pi.single 0 1 : Fin (n + 1) → ℝ) := by
  refine FacetGermAux.eq_of_forall_dot_eq fun x => ?_
  rw [GermAux.dot_mulVec, Matrix.transpose_transpose, SupportCut.dot_sub_left,
    SupportCut.dot_smul_left, dot_single_left, dot_eq_dot_tail_chartT hν0 p x]
  ring

/-- **A point set in the hyperplane `{⟨ν, ·⟩ = c}`, read in the chart:**
`h_S y = h_{tail S} (chartT ν y) + c y_0`. -/
theorem hS_image_univ_eq_chartT {k : ℕ} {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1)
    (q : Fin (k + 1) → Fin (n + 1) → ℝ) {c : ℝ} (hc : ∀ l, dot ν (q l) = c)
    (y : Fin (n + 1) → ℝ) :
    hS (Finset.univ.image q) y =
      hS (Finset.univ.image fun l => Fin.tail (q l)) ((chartT ν).mulVec y) + c * y 0 := by
  rw [hS_of_nonempty (Finset.univ_nonempty.image q),
    hS_of_nonempty (Finset.univ_nonempty.image fun l => Fin.tail (q l)),
    Finset.sup'_image, Finset.sup'_image, ← Sweep.sup'_add_const]
  refine Finset.sup'_congr _ rfl fun l _ => ?_
  simp only [Function.comp_apply]
  rw [dot_eq_dot_tail_chartT hν0 (q l) y, hc l]

/-- Translating a family of points keeps it affinely independent. -/
theorem affineIndependent_add_const {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    {q : Fin (k + 1) → V} (hq : AffineIndependent ℝ q) (t : V) :
    AffineIndependent ℝ (fun l => q l + t) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (k + 1))] at hq ⊢
  convert hq using 1
  funext i
  simp only [vsub_eq_sub, add_sub_add_right_eq_sub]

/-- **Deleting the coordinate `0` keeps a point set of the hyperplane `{⟨ν, ·⟩ = c}` affinely
independent** (for `ν 0 = 1`). -/
theorem affineIndependent_tail {k : ℕ} {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1)
    {q : Fin (k + 1) → Fin (n + 1) → ℝ} (hq : AffineIndependent ℝ q) {c : ℝ}
    (hc : ∀ l, dot ν (q l) = c) : AffineIndependent ℝ (fun l => Fin.tail (q l)) := by
  refine AffineIndependent.of_comp (Matrix.mulVecLin (chartT ν)ᵀ).toAffineMap ?_
  have e : ((Matrix.mulVecLin (chartT ν)ᵀ).toAffineMap ∘ fun l => Fin.tail (q l)) =
      fun l => q l + -(c • (Pi.single 0 1 : Fin (n + 1) → ℝ)) := by
    funext l
    show (chartT ν)ᵀ.mulVec (Fin.tail (q l)) = _
    rw [chartT_transpose_mulVec_tail hν0, hc l, sub_eq_add_neg]
  rw [e]
  exact affineIndependent_add_const hq _

/-! ## Lifting flags of `ℝ^n` to `ℝ^{n+1}` -/

/-- `chartT ν` maps the lifted list `(0, us)` back to `us`. -/
theorem map_cons_zero_map_chartT (ν : Fin (n + 1) → ℝ) (us : List (Fin n → ℝ)) :
    (us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ)).map (chartT ν).mulVec = us := by
  rw [List.map_map]
  exact List.map_id'' (fun z => chartT_mulVec_cons_zero ν z) us

/-- **Lifting a flag:** if `us` is a flag of `ℝ^n` and `ν 0 = 1`, then `ν :: (0, us)` is a flag
of `ℝ^{n+1}`. -/
theorem isFlag_cons_map_cons_zero {ν : Fin (n + 1) → ℝ} (hν0 : ν 0 = 1)
    {us : List (Fin n → ℝ)} (hus : IsFlag us) :
    IsFlag (ν :: us.map fun z => (Fin.cons 0 z : Fin (n + 1) → ℝ)) := by
  have hν : ν ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [hν0] at h0
    exact one_ne_zero h0
  refine isFlag_cons_of_isFlag_map_mulVec (chartT ν) ?_ rfl hν (chartT_mulVec_self hν0)
  rw [map_cons_zero_map_chartT]
  exact hus

end CompleteAux

end

end MaxNN.ParamidGeom
