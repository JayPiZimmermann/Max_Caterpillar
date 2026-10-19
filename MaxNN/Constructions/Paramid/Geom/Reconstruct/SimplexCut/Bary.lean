import MaxNN.Constructions.Paramid.Geom.Defs
import MaxNN.PolyhedralGeometry.SupportCut
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Sign

/-!
# Barycentric coordinates of a simplex (helper for `Geom/Reconstruct/SimplexCut.lean`)

For `m + 1` affinely independent points `p : Fin (m + 1) → ℝ^m` (an `m`-simplex),
`simplexBasis p hp` is the affine basis they form and `β_j = (simplexBasis p hp).coord j` are the
barycentric coordinates.  `baryLin p hp v j = (β_j)'(v)` is the rate of change of `β_j` along a
direction `v`.  The facet `F_j = conv (p i)_{i ≠ j}` is the zero set of `β_j` on the simplex, and
its sign in direction `v` is `facetSign p hp v j = − sign (β_j)'(v)`: `+1` for an upper facet
(moving along `v` one leaves the simplex through `F_j`), `−1` for a lower facet, `0` for a vertical
facet.

* `sum_baryLin`: `∑_j (β_j)'(v) = 0`; `sum_baryLin_smul`: `∑_j (β_j)'(v) • p_j = v`;
  `baryLin_eq_of_sum_smul`: these two identities characterize the rates.
* `exists_baryLin_neg`, `exists_baryLin_pos`, `exists_facetSign_eq_one`,
  `exists_facetSign_eq_neg_one`: for `v ≠ 0` there is an upper and a lower facet.
* `SimplexCut.affineIndependent_update_of_eq`, `SimplexCut.baryLin_update_of_eq`: replacing the
  vertex `p_k` by a point `q = (1 − t) p_j + t p_k` (`t ≠ 0`) of the line through an edge keeps a
  simplex, and the rates of the new simplex are explicit.
* `SimplexCut.dualVec`: the coefficient vector of a linear functional on `ℝ^m`
  (`⟨dualVec φ, x⟩ = φ x`).

Generic helpers live in the sub-namespace `MaxNN.ParamidGeom.SimplexCut`; the facet vocabulary
(`simplexBasis`, `baryLin`, `facetSign` and their basic lemmas) lives in `MaxNN.ParamidGeom`.
-/

namespace MaxNN.ParamidGeom

open BigOperators

noncomputable section

variable {m : ℕ}

/-! ## Generic helpers (sub-namespace `SimplexCut`, to keep the shared namespace clean) -/

namespace SimplexCut

/-- `∑ᵢ fᵢ = f_j + f_k + ∑_{i ≠ j, k} fᵢ`. -/
theorem sum_split_pair {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] {j k : ι}
    (hjk : j ≠ k) (f : ι → M) :
    ∑ i, f i = f j + f k + ∑ i in (Finset.univ.erase j).erase k, f i := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ j),
    ← Finset.add_sum_erase (Finset.univ.erase j) f
      (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩), add_assoc]

theorem ne_ne_of_mem_erase_erase {ι : Type*} [DecidableEq ι] {s : Finset ι} {i j k : ι}
    (h : i ∈ (s.erase j).erase k) : i ≠ j ∧ i ≠ k :=
  ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩

/-- The linear part of an affine functional on `ℝ^m`: `f.linear x = f x − f 0`. -/
theorem affine_linear_eq_sub (f : (Fin m → ℝ) →ᵃ[ℝ] ℝ) (x : Fin m → ℝ) :
    f.linear x = f x - f 0 := by
  have h := f.linearMap_vsub x 0
  simpa only [vsub_eq_sub, sub_zero] using h

/-- The coefficient vector of a linear functional on `ℝ^m`. -/
def dualVec (φ : (Fin m → ℝ) →ₗ[ℝ] ℝ) : Fin m → ℝ :=
  fun i => φ fun j => if i = j then 1 else 0

theorem dot_dualVec (φ : (Fin m → ℝ) →ₗ[ℝ] ℝ) (x : Fin m → ℝ) : dot (dualVec φ) x = φ x := by
  rw [LinearMap.pi_apply_eq_sum_univ φ x]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [dualVec, smul_eq_mul]
    ring

end SimplexCut

open SimplexCut

/-! ## The affine basis of a simplex -/

/-- The affine basis of `ℝ^m` formed by the `m + 1` affinely independent vertices of an
`m`-simplex. -/
def simplexBasis (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) :
    AffineBasis (Fin (m + 1)) ℝ (Fin m → ℝ) :=
  ⟨p, hp, hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
    rw [Fintype.card_fin, FiniteDimensional.finrank_fin_fun])⟩

theorem coe_simplexBasis (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) :
    ⇑(simplexBasis p hp) = p :=
  rfl

/-- The rate `(β_j)'(v)` of the `j`-th barycentric coordinate of the simplex `p` along `v`. -/
def baryLin (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) (v : Fin m → ℝ)
    (j : Fin (m + 1)) : ℝ :=
  ((simplexBasis p hp).coord j).linear v

theorem baryLin_eq_sub (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) (j : Fin (m + 1)) :
    baryLin p hp v j = (simplexBasis p hp).coord j v - (simplexBasis p hp).coord j 0 :=
  affine_linear_eq_sub _ v

theorem coord_simplexBasis_vertex (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (j i : Fin (m + 1)) : (simplexBasis p hp).coord j (p i) = if j = i then 1 else 0 :=
  (simplexBasis p hp).coord_apply j i

/-- `∑_j (β_j)'(v) = 0`. -/
theorem sum_baryLin (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) : ∑ j, baryLin p hp v j = 0 := by
  simp only [baryLin_eq_sub, Finset.sum_sub_distrib, AffineBasis.sum_coord_apply_eq_one,
    sub_self]

/-- `∑_j (β_j)'(v) • p_j = v`. -/
theorem sum_baryLin_smul (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) : ∑ j, baryLin p hp v j • p j = v := by
  have h1 := (simplexBasis p hp).linear_combination_coord_eq_self v
  have h0 := (simplexBasis p hp).linear_combination_coord_eq_self 0
  rw [coe_simplexBasis] at h1 h0
  simp only [baryLin_eq_sub, sub_smul, Finset.sum_sub_distrib, h1, h0, sub_zero]

/-- The rates are characterized by `∑_i κ_i = 0` and `∑_i κ_i • p_i = v`. -/
theorem baryLin_eq_of_sum_smul (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (κ : Fin (m + 1) → ℝ) (hκ : ∑ i, κ i = 0) (hv : ∑ i, κ i • p i = v)
    (l : Fin (m + 1)) : baryLin p hp v l = κ l := by
  rw [← hv, baryLin, map_sum]
  have h : ∀ i, ((simplexBasis p hp).coord l).linear (κ i • p i) =
      κ i * (if l = i then 1 else 0) - κ i * (simplexBasis p hp).coord l 0 := by
    intro i
    rw [map_smul, smul_eq_mul, affine_linear_eq_sub, coord_simplexBasis_vertex, mul_sub]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.sum_mul, hκ,
    zero_mul, sub_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## Facet signs -/

/-- The sign of the facet `F_j = conv (p i)_{i ≠ j}` of the simplex `p` in direction `v`:
`−sign ((β_j).linear v)` for the barycentric coordinate `β_j`, i.e. `+1` for an upper facet, `−1`
for a lower facet and `0` for a vertical facet. -/
def facetSign (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p) (v : Fin m → ℝ)
    (j : Fin (m + 1)) : ℝ :=
  -((SignType.sign (((simplexBasis p hp).coord j).linear v) : SignType) : ℝ)

theorem facetSign_eq (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    (v : Fin m → ℝ) (j : Fin (m + 1)) :
    facetSign p hp v j = -((SignType.sign (baryLin p hp v j) : SignType) : ℝ) :=
  rfl

section FacetSign

variable {p : Fin (m + 1) → Fin m → ℝ} {hp : AffineIndependent ℝ p} {v : Fin m → ℝ}
  {j : Fin (m + 1)}

theorem facetSign_of_neg (h : baryLin p hp v j < 0) : facetSign p hp v j = 1 := by
  rw [facetSign_eq, sign_neg h, SignType.coe_neg_one, neg_neg]

theorem facetSign_of_pos (h : 0 < baryLin p hp v j) : facetSign p hp v j = -1 := by
  rw [facetSign_eq, sign_pos h, SignType.coe_one]

theorem facetSign_of_eq_zero (h : baryLin p hp v j = 0) : facetSign p hp v j = 0 := by
  rw [facetSign_eq, h, sign_zero, SignType.coe_zero, neg_zero]

theorem facetSign_eq_one_iff : facetSign p hp v j = 1 ↔ baryLin p hp v j < 0 := by
  refine ⟨fun hs => ?_, facetSign_of_neg⟩
  rcases lt_trichotomy (baryLin p hp v j) 0 with h | h | h
  · exact h
  · rw [facetSign_of_eq_zero h] at hs
    norm_num at hs
  · rw [facetSign_of_pos h] at hs
    norm_num at hs

theorem facetSign_eq_neg_one_iff : facetSign p hp v j = -1 ↔ 0 < baryLin p hp v j := by
  refine ⟨fun hs => ?_, facetSign_of_pos⟩
  rcases lt_trichotomy (baryLin p hp v j) 0 with h | h | h
  · rw [facetSign_of_neg h] at hs
    norm_num at hs
  · rw [facetSign_of_eq_zero h] at hs
    norm_num at hs
  · exact h

theorem facetSign_eq_zero_iff : facetSign p hp v j = 0 ↔ baryLin p hp v j = 0 := by
  refine ⟨fun hs => ?_, facetSign_of_eq_zero⟩
  rcases lt_trichotomy (baryLin p hp v j) 0 with h | h | h
  · rw [facetSign_of_neg h] at hs
    norm_num at hs
  · exact h
  · rw [facetSign_of_pos h] at hs
    norm_num at hs

end FacetSign

/-! ## Every nonzero direction has an upper and a lower facet -/

theorem exists_baryLin_ne_zero (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (hv : v ≠ 0) : ∃ j, baryLin p hp v j ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  rw [← sum_baryLin_smul p hp v]
  exact Finset.sum_eq_zero fun j _ => by rw [h j, zero_smul]

theorem exists_baryLin_neg (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (hv : v ≠ 0) : ∃ j, baryLin p hp v j < 0 := by
  by_contra h
  push_neg at h
  obtain ⟨j, hj⟩ := exists_baryLin_ne_zero p hp hv
  exact hj ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => h i).mp (sum_baryLin p hp v) j
    (Finset.mem_univ j))

theorem exists_baryLin_pos (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (hv : v ≠ 0) : ∃ j, 0 < baryLin p hp v j := by
  by_contra h
  push_neg at h
  obtain ⟨j, hj⟩ := exists_baryLin_ne_zero p hp hv
  have hsum : ∑ i, -baryLin p hp v i = 0 := by
    rw [Finset.sum_neg_distrib, sum_baryLin, neg_zero]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => neg_nonneg.mpr (h i)).mp hsum j
    (Finset.mem_univ j)
  exact hj (neg_eq_zero.mp h0)

/-- A nonzero direction has an upper facet (`facetSign = 1`). -/
theorem exists_facetSign_eq_one (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (hv : v ≠ 0) : ∃ j, facetSign p hp v j = 1 :=
  let ⟨j, hj⟩ := exists_baryLin_neg p hp hv
  ⟨j, facetSign_of_neg hj⟩

/-- A nonzero direction has a lower facet (`facetSign = −1`). -/
theorem exists_facetSign_eq_neg_one (p : Fin (m + 1) → Fin m → ℝ) (hp : AffineIndependent ℝ p)
    {v : Fin m → ℝ} (hv : v ≠ 0) : ∃ j, facetSign p hp v j = -1 :=
  let ⟨j, hj⟩ := exists_baryLin_pos p hp hv
  ⟨j, facetSign_of_pos hj⟩

/-! ## Moving one vertex along an edge line -/

namespace SimplexCut

/-- Replacing the vertex `p_k` by a point `q = (1 − t) p_j + t p_k` with `t ≠ 0` keeps the
vertices affinely independent. -/
theorem affineIndependent_update_of_eq {p : Fin (m + 1) → Fin m → ℝ}
    (hp : AffineIndependent ℝ p) {j k : Fin (m + 1)} (hjk : j ≠ k) {t : ℝ} (ht : t ≠ 0)
    {q : Fin m → ℝ} (hq : q = (1 - t) • p j + t • p k) :
    AffineIndependent ℝ (Function.update p k q) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ j] at hp ⊢
  have hu := hp.units_smul fun i : { x // x ≠ j } =>
    if (i : Fin (m + 1)) = k then Units.mk0 t ht else 1
  have he : (fun i : { x // x ≠ j } =>
      (Function.update p k q i -ᵥ Function.update p k q j : Fin m → ℝ)) =
      (fun i : { x // x ≠ j } => if (i : Fin (m + 1)) = k then Units.mk0 t ht else 1) •
        fun i : { x // x ≠ j } => (p i -ᵥ p j : Fin m → ℝ) := by
    funext i
    simp only [Pi.smul_apply', vsub_eq_sub, Function.update_noteq hjk]
    by_cases hik : (i : Fin (m + 1)) = k
    · rw [if_pos hik, Units.smul_mk0, hik, Function.update_same, hq]
      funext l
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg hik, one_smul, Function.update_noteq hik]
  rw [he]
  exact hu

/-- The rates of the simplex obtained by replacing `p_k` with `q = (1 − t) p_j + t p_k`
(`t ≠ 0`): `(β'_k)'(v) = (β_k)'(v) / t`, `(β'_j)'(v) = (β_j)'(v) − (β_k)'(v) (1 − t) / t`, and
`(β'_i)'(v) = (β_i)'(v)` for `i ≠ j, k`. -/
theorem baryLin_update_of_eq {p : Fin (m + 1) → Fin m → ℝ} (hp : AffineIndependent ℝ p)
    {j k : Fin (m + 1)} (hjk : j ≠ k) {t : ℝ} (ht : t ≠ 0) {q : Fin m → ℝ}
    (hq : q = (1 - t) • p j + t • p k) (hp' : AffineIndependent ℝ (Function.update p k q))
    (v : Fin m → ℝ) (i : Fin (m + 1)) :
    baryLin (Function.update p k q) hp' v i =
      if i = k then baryLin p hp v k / t
      else if i = j then baryLin p hp v j - baryLin p hp v k * (1 - t) / t
      else baryLin p hp v i := by
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (m + 1) → ℝ, κ = fun i => if i = k then baryLin p hp v k / t
      else if i = j then baryLin p hp v j - baryLin p hp v k * (1 - t) / t
      else baryLin p hp v i := ⟨_, rfl⟩
  have hκj : κ j = baryLin p hp v j - baryLin p hp v k * (1 - t) / t := by
    rw [hκ]
    show (if j = k then _ else if j = j then _ else _) = _
    rw [if_neg hjk, if_pos rfl]
  have hκk : κ k = baryLin p hp v k / t := by
    rw [hκ]
    show (if k = k then _ else _) = _
    rw [if_pos rfl]
  have hκr : ∀ i ∈ (Finset.univ.erase j).erase k, κ i = baryLin p hp v i := by
    intro i hi
    obtain ⟨hij, hik⟩ := ne_ne_of_mem_erase_erase hi
    rw [hκ]
    show (if i = k then _ else if i = j then _ else _) = _
    rw [if_neg hik, if_neg hij]
  have hsum : ∑ i, κ i = 0 := by
    rw [sum_split_pair hjk, hκj, hκk, Finset.sum_congr rfl hκr]
    have h0 := sum_baryLin p hp v
    rw [sum_split_pair hjk] at h0
    have e : baryLin p hp v j - baryLin p hp v k * (1 - t) / t + baryLin p hp v k / t =
        baryLin p hp v j + baryLin p hp v k := by
      field_simp
      ring
    rw [e]
    exact h0
  have hvec : ∑ i, κ i • Function.update p k q i = v := by
    conv_rhs => rw [← sum_baryLin_smul p hp v]
    rw [sum_split_pair hjk (fun i => κ i • Function.update p k q i),
      sum_split_pair hjk (fun i => baryLin p hp v i • p i)]
    have hrest : ∑ i in (Finset.univ.erase j).erase k, κ i • Function.update p k q i =
        ∑ i in (Finset.univ.erase j).erase k, baryLin p hp v i • p i :=
      Finset.sum_congr rfl fun i hi => by
        rw [hκr i hi, Function.update_noteq (ne_ne_of_mem_erase_erase hi).2]
    show κ j • Function.update p k q j + κ k • Function.update p k q k +
        ∑ i in (Finset.univ.erase j).erase k, κ i • Function.update p k q i =
      baryLin p hp v j • p j + baryLin p hp v k • p k +
        ∑ i in (Finset.univ.erase j).erase k, baryLin p hp v i • p i
    rw [hrest, Function.update_noteq hjk, Function.update_same, hκj, hκk, hq]
    congr 1
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [baryLin_eq_of_sum_smul _ hp' κ hsum hvec i, hκ]

end SimplexCut

end

end MaxNN.ParamidGeom
