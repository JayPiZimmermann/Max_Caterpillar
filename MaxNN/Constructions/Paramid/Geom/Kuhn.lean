import MaxNN.Constructions.Paramid.Geom.Kuhn.Staircase
import MaxNN.Constructions.Paramid.Geom.Kuhn.Chain

/-!
# M-Kuhn: a paramid cone is the sum of its Kuhn simplices, modulo lower dimension

Let `γ ∈ ℝ^m` and `v : Fin k → ℝ^m` with `k + 1 = m`.  The paramid unit `paramidUnit γ v` is the
support function of the cone from `0` over the parallelepiped `γ + ∑ᵢ [0, v i]`.  When the frame
`(v 0, …, v (k−1), γ)` is a basis, write `x = s γ + ∑ τ_i v_i`; the cone is
`{0 ≤ τ_i ≤ s ≤ 1}`, and the `k!` Kuhn simplices are its pieces
`{0 ≤ τ_{σ(k−1)} ≤ … ≤ τ_{σ 0} ≤ s ≤ 1}`, with vertices
`0, γ, γ + v (σ 0), γ + v (σ 0) + v (σ 1), …, γ + ∑ v` (`kuhnVerts γ v σ`).

## Main results

* `kuhnVerts_affineIndependent`: the Kuhn vertices are affinely independent.
* `paramidUnit_sub_kuhn_mem_LSpan`: `paramidUnit γ v − ∑_σ hS (Kuhn simplex σ) ∈ LSpan m (m − 1)`.
* `paramidUnit_mem_LSpan_of_not_linearIndependent`: a degenerate cone (dependent frame) has
  dimension `≤ m − 1`, so its unit lies in `LSpan m (m − 1)`.

## Proof

The cone is cut by the hyperplanes `τ_t = τ_y`, inserting the indices one at a time
(`Kuhn/Staircase.lean`: each insertion is a staircase of cuts whose leaves are the insertions
`List.permutations'Aux`; each cut costs a section of dimension `≤ m − 1`,
`SupportCut.support_cut_identity`).  The leaf of the order `σ` has convex hull
`conv (cone) ∩ {τ_{σ 0} ≥ … ≥ τ_{σ(k−1)}}` (`SupportCut.convexHull_inter_halfspace_*`), which is
the Kuhn simplex (`convexHull_kuhn_eq`: one inclusion by the vertices, the other by the explicit
convex combination of `Kuhn/Chain.lean`), and `hS` only sees the convex hull
(`Kuhn/Hull.lean`).  Helpers live in `Geom/Kuhn/` (namespace `MaxNN.ParamidGeom.Kuhn`).
-/

namespace MaxNN.ParamidGeom

open BigOperators MaxNN.SupportCut

noncomputable section

variable {m k : ℕ}

/-- The vertices `0, γ, γ + v (σ 0), γ + v (σ 0) + v (σ 1), …, γ + ∑ v` of the Kuhn simplex of
the order `σ`: vertex `0` is the origin and vertex `r + 1` is `γ + ∑_{p < r} v (σ p)`. -/
def kuhnVerts (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) (σ : Equiv.Perm (Fin k)) :
    Fin (k + 2) → (Fin m → ℝ) :=
  Fin.cons 0 (Kuhn.chainPt γ (fun p => v (σ p)))

@[simp]
theorem kuhnVerts_zero (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) (σ : Equiv.Perm (Fin k)) :
    kuhnVerts γ v σ 0 = 0 := by
  rw [kuhnVerts, Fin.cons_zero]

theorem kuhnVerts_succ (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) (σ : Equiv.Perm (Fin k))
    (r : Fin (k + 1)) :
    kuhnVerts γ v σ r.succ = γ + ∑ p : Fin k, if (p : ℕ) < (r : ℕ) then v (σ p) else 0 := by
  rw [kuhnVerts, Fin.cons_succ]
  rfl

namespace Kuhn

/-! ## The vertex set of the paramid cone -/

/-- Vertex set of the cone from `0` over the parallelepiped `γ + ∑ᵢ [0, v i]` (labels as a
family, so repeated labels are allowed). -/
def coneVertsFam (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) : Finset (Fin m → ℝ) :=
  insert 0 ((Finset.univ : Finset (Finset (Fin k))).image (fun I => γ + ∑ i in I, v i))

theorem dot_finset_sum_left (I : Finset (Fin k)) (v : Fin k → Fin m → ℝ) (y : Fin m → ℝ) :
    dot (∑ i in I, v i) y = ∑ i in I, dot (v i) y := by
  rw [dot_comm, ← dotL_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [dotL_apply, dot_comm]

theorem dot_zero_left (y : Fin m → ℝ) : dot (0 : Fin m → ℝ) y = 0 := by
  simp [dot]

/-- The paramid unit is the support function of the vertex set of its cone. -/
theorem paramidUnit_eq_hS_coneVertsFam (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) :
    paramidUnit γ v = hS (coneVertsFam γ v) := by
  funext y
  have hne' : ((Finset.univ : Finset (Finset (Fin k))).image
      (fun I => γ + ∑ i in I, v i)).Nonempty := Finset.univ_nonempty.image _
  rw [paramidUnit_eq_max_vertices]
  show _ = hS (insert 0 ((Finset.univ : Finset (Finset (Fin k))).image
    (fun I => γ + ∑ i in I, v i))) y
  rw [hS_of_nonempty (Finset.insert_nonempty _ _), Finset.sup'_insert hne',
    Finset.sup'_image hne', dot_zero_left]
  have hcomp : ((fun p => dot p y) ∘ (fun I : Finset (Fin k) => γ + ∑ i in I, v i)) =
      fun I => dot γ y + ∑ j in I, dot (v j) y := by
    funext I
    simp only [Function.comp_apply, dot_add_left, dot_finset_sum_left]
  rw [hcomp]
  rfl

theorem mem_span_of_mem_coneVertsFam {γ : Fin m → ℝ} {v : Fin k → Fin m → ℝ}
    {p : Fin m → ℝ} (hp : p ∈ coneVertsFam γ v) :
    p ∈ Submodule.span ℝ (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)) := by
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact Submodule.zero_mem _
  · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hp
    refine Submodule.add_mem _ (Submodule.subset_span ⟨Fin.last k, Fin.snoc_last _ _⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Fin.castSucc i, ?_⟩)
    exact Fin.snoc_castSucc (α := fun _ => Fin m → ℝ) γ v i

/-! ## Coordinates in the frame basis -/

/-- The basis `(v 0, …, v (k−1), γ)` of `ℝ^m` given by a linearly independent frame with
`k + 1 = m`. -/
def frameBasis (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ)
    (h : LinearIndependent ℝ (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)) (hm : k + 1 = m) :
    Basis (Fin (k + 1)) ℝ (Fin m → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank h
    (by rw [Fintype.card_fin, FiniteDimensional.finrank_fin_fun, hm])

theorem frameBasis_apply (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ)
    (h : LinearIndependent ℝ (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)) (hm : k + 1 = m)
    (j : Fin (k + 1)) :
    frameBasis γ v h hm j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j := by
  unfold frameBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The vector of the `j`-th coordinate functional of a basis of `ℝ^m`. -/
def coordVec (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) (j : Fin (k + 1)) : Fin m → ℝ :=
  fun l => b.coord j (fun l' => if l = l' then 1 else 0)

theorem dot_coordVec (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) (j : Fin (k + 1))
    (x : Fin m → ℝ) : dot (coordVec b j) x = b.coord j x := by
  rw [LinearMap.pi_apply_eq_sum_univ (b.coord j) x]
  unfold dot coordVec
  exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, mul_comm]

theorem coord_basis (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) (i j : Fin (k + 1)) :
    b.coord j (b i) = if i = j then 1 else 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

section Frame

variable {γ : Fin m → ℝ} {v : Fin k → Fin m → ℝ}

theorem coord_coneVert (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (j : Fin (k + 1))
    (I : Finset (Fin k)) :
    b.coord j (γ + ∑ i in I, v i) =
      (if Fin.last k = j then 1 else 0) + ∑ i in I, (if Fin.castSucc i = j then 1 else 0) := by
  have hγ : γ = b (Fin.last k) := by rw [hb, Fin.snoc_last]
  have hv : ∀ i, v i = b (Fin.castSucc i) := fun i => by rw [hb, Fin.snoc_castSucc]
  rw [map_add, map_sum, hγ, coord_basis]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv, coord_basis]

theorem coord_last_coneVert (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (I : Finset (Fin k)) :
    b.coord (Fin.last k) (γ + ∑ i in I, v i) = 1 := by
  rw [coord_coneVert b hb, if_pos rfl,
    Finset.sum_eq_zero (fun i _ => if_neg (Fin.castSucc_lt_last i).ne), add_zero]

theorem coord_castSucc_coneVert (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (j : Fin k)
    (I : Finset (Fin k)) :
    b.coord (Fin.castSucc j) (γ + ∑ i in I, v i) = if j ∈ I then 1 else 0 := by
  rw [coord_coneVert b hb, if_neg (Fin.castSucc_lt_last j).ne', zero_add]
  simp only [Fin.castSucc_inj]
  rw [Finset.sum_ite_eq']

theorem coord_castSucc_v (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (i j : Fin k) :
    b.coord (Fin.castSucc j) (v i) = if i = j then 1 else 0 := by
  have hv : v i = b (Fin.castSucc i) := by rw [hb, Fin.snoc_castSucc]
  rw [hv, coord_basis]
  simp only [Fin.castSucc_inj]

/-! ## The cone and the chambers in coordinates -/

/-- The coordinate description of the paramid cone: `0 ≤ s ≤ 1` and `0 ≤ τ_i ≤ s`. -/
def coneRegion (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {x | 0 ≤ b.coord (Fin.last k) x ∧ b.coord (Fin.last k) x ≤ 1 ∧
    ∀ i : Fin k, 0 ≤ b.coord (Fin.castSucc i) x ∧
      b.coord (Fin.castSucc i) x ≤ b.coord (Fin.last k) x}

theorem convex_coneRegion (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) :
    Convex ℝ (coneRegion b) := by
  intro x hx y hy a c ha hc hac
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [coneRegion, Set.mem_setOf_eq, map_add, map_smulₛₗ, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx1) (mul_nonneg hc hy1), ?_, fun i => ⟨?_, ?_⟩⟩
  · calc a * b.coord (Fin.last k) x + c * b.coord (Fin.last k) y ≤ a * 1 + c * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hc)
      _ = 1 := by rw [mul_one, mul_one, hac]
  · exact add_nonneg (mul_nonneg ha (hx3 i).1) (mul_nonneg hc (hy3 i).1)
  · exact add_le_add (mul_le_mul_of_nonneg_left (hx3 i).2 ha)
      (mul_le_mul_of_nonneg_left (hy3 i).2 hc)

theorem convexHull_coneVertsFam_subset (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) :
    convexHull ℝ (coneVertsFam γ v : Set (Fin m → ℝ)) ⊆ coneRegion b := by
  refine convexHull_min ?_ (convex_coneRegion b)
  intro p hp
  rcases Finset.mem_insert.mp (Finset.mem_coe.mp hp) with rfl | hp
  · simp [coneRegion]
  · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨by rw [coord_last_coneVert b hb]; norm_num,
      by rw [coord_last_coneVert b hb], fun i => ?_⟩
    rw [coord_castSucc_coneVert b hb, coord_last_coneVert b hb]
    split_ifs <;> norm_num

/-- The chamber of the order `σ`: `τ_{σ 0} ≥ τ_{σ 1} ≥ … ≥ τ_{σ(k−1)}`. -/
def kuhnChamber (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) (σ : Equiv.Perm (Fin k)) :
    Set (Fin m → ℝ) :=
  {x | ∀ p q : Fin k, p < q → b.coord (Fin.castSucc (σ q)) x ≤ b.coord (Fin.castSucc (σ p)) x}

theorem mem_kuhnChamber {b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)} {σ : Equiv.Perm (Fin k)}
    {x : Fin m → ℝ} :
    x ∈ kuhnChamber b σ ↔
      ∀ p q : Fin k, p < q → b.coord (Fin.castSucc (σ q)) x ≤ b.coord (Fin.castSucc (σ p)) x :=
  Iff.rfl

theorem convex_kuhnChamber (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ)) (σ : Equiv.Perm (Fin k)) :
    Convex ℝ (kuhnChamber b σ) := by
  intro x hx y hy a c ha hc _
  rw [mem_kuhnChamber] at hx hy ⊢
  intro p q hpq
  simp only [map_add, map_smulₛₗ, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (hx p q hpq) ha)
    (mul_le_mul_of_nonneg_left (hy p q hpq) hc)

theorem chainPt_eq_coneVert (γ : Fin m → ℝ) (v : Fin k → Fin m → ℝ) (σ : Equiv.Perm (Fin k))
    (r : Fin (k + 1)) :
    chainPt γ (fun p => v (σ p)) r =
      γ + ∑ i in Finset.univ.filter (fun i : Fin k => ((σ.symm i : Fin k) : ℕ) < (r : ℕ)),
        v i := by
  unfold chainPt
  congr 1
  rw [Finset.sum_filter,
    ← Equiv.sum_comp σ.symm (fun p => if (p : ℕ) < (r : ℕ) then v (σ p) else 0)]
  simp only [Equiv.apply_symm_apply]

theorem coord_castSucc_chainPt (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (σ : Equiv.Perm (Fin k))
    (r : Fin (k + 1)) (j : Fin k) :
    b.coord (Fin.castSucc (σ j)) (chainPt γ (fun p => v (σ p)) r) =
      if (j : ℕ) < (r : ℕ) then 1 else 0 := by
  rw [chainPt_eq_coneVert, coord_castSucc_coneVert b hb]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

/-- **The chamber piece of the order `σ` is the Kuhn simplex of `σ`.** -/
theorem convexHull_kuhn_eq (b : Basis (Fin (k + 1)) ℝ (Fin m → ℝ))
    (hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j) (σ : Equiv.Perm (Fin k)) :
    convexHull ℝ (coneVertsFam γ v : Set (Fin m → ℝ)) ∩ kuhnChamber b σ =
      convexHull ℝ (Finset.univ.image (kuhnVerts γ v σ) : Set (Fin m → ℝ)) := by
  have hrange : (Finset.univ.image (kuhnVerts γ v σ) : Set (Fin m → ℝ)) =
      insert 0 (Set.range (chainPt γ (fun p => v (σ p)))) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Fin.range_cons _ _
  rw [hrange]
  have hγ : b (Fin.last k) = γ := by rw [hb, Fin.snoc_last]
  have hv : ∀ i, b (Fin.castSucc i) = v i := fun i => by rw [hb, Fin.snoc_castSucc]
  apply Set.Subset.antisymm
  · rintro x ⟨hxc, hxσ⟩
    obtain ⟨hs0, hs1, hτ⟩ := convexHull_coneVertsFam_subset b hb hxc
    have hx : x = b.coord (Fin.last k) x • γ +
        ∑ p, b.coord (Fin.castSucc (σ p)) x • v (σ p) := by
      have h1 := b.sum_repr x
      rw [Fin.sum_univ_castSucc] at h1
      rw [Equiv.sum_comp σ (fun i => b.coord (Fin.castSucc i) x • v i)]
      conv_lhs => rw [← h1]
      simp only [Basis.coord_apply, hv, hγ]
      rw [add_comm]
    rw [hx]
    refine cone_chain_mem_convexHull γ (fun p => v (σ p)) _
      (fun p => b.coord (Fin.castSucc (σ p)) x) hs0 hs1 (fun p => (hτ (σ p)).1)
      (fun p => (hτ (σ p)).2) (fun p q hpq => ?_)
    rcases hpq.lt_or_eq with h | h
    · exact hxσ p q h
    · rw [h]
  · refine convexHull_min ?_ ((convex_convexHull ℝ _).inter (convex_kuhnChamber b σ))
    rintro x (rfl | ⟨r, rfl⟩)
    · refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)), ?_⟩
      rw [mem_kuhnChamber]
      intro p q _
      simp only [map_zero, le_refl]
    · refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (chainPt_eq_coneVert γ v σ r).symm⟩))), ?_⟩
      rw [mem_kuhnChamber]
      intro p q hpq
      rw [coord_castSucc_chainPt b hb σ r q, coord_castSucc_chainPt b hb σ r p]
      have hpq' : (p : ℕ) < (q : ℕ) := Fin.lt_iff_val_lt_val.mp hpq
      split_ifs with h1 h2 h2
      · exact le_refl _
      · exact absurd (lt_trans hpq' h1) h2
      · norm_num
      · exact le_refl _

end Frame

end Kuhn

open Kuhn

/-! ## Main results -/

/-- **The Kuhn vertices are affinely independent** (for a linearly independent frame). -/
theorem kuhnVerts_affineIndependent {γ : Fin m → ℝ} {v : Fin k → Fin m → ℝ}
    (h : LinearIndependent ℝ (Fin.snoc v γ)) (σ : Equiv.Perm (Fin k)) :
    AffineIndependent ℝ (kuhnVerts γ v σ) := by
  unfold kuhnVerts
  apply affineIndependent_cons_zero
  refine linearIndependent_of_span _ (Fin.snoc v γ) h fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact Submodule.subset_span ⟨0, chainPt_zero _ _⟩
  · rw [Fin.snoc_castSucc]
    have e := chainPt_succ_sub_castSucc γ (fun p => v (σ p)) (σ.symm i)
    rw [Equiv.apply_symm_apply] at e
    rw [← e]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- **Kuhn triangulation modulo lower dimension.**  For a linearly independent frame
`(v 0, …, v (k−1), γ)` of `ℝ^m` (`k + 1 = m`), the paramid unit minus the sum of the support
functions of its `k!` Kuhn simplices lies in `LSpan m (m − 1)`. -/
theorem paramidUnit_sub_kuhn_mem_LSpan {γ : Fin m → ℝ} {v : Fin k → Fin m → ℝ}
    (h : LinearIndependent ℝ (Fin.snoc v γ)) (hm : k + 1 = m) :
    (fun y => paramidUnit γ v y -
      ∑ σ : Equiv.Perm (Fin k), hS (Finset.univ.image (kuhnVerts γ v σ)) y) ∈
      LSpan m (m - 1) := by
  let b := frameBasis γ v h hm
  have hb : ∀ j, b j = (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ) j := frameBasis_apply γ v h hm
  let α : Fin k → Fin m → ℝ := fun i => coordVec b (Fin.castSucc i)
  have hαdef : ∀ i x, dot (α i) x = b.coord (Fin.castSucc i) x := fun i x => dot_coordVec b _ x
  have hα : Function.Injective α := by
    intro i j hij
    have h1 : dot (α i) (v i) = dot (α j) (v i) := by rw [hij]
    rw [hαdef, hαdef, coord_castSucc_v b hb, coord_castSucc_v b hb] at h1
    by_contra hne
    rw [if_pos rfl, if_neg hne] at h1
    exact one_ne_zero h1
  obtain ⟨P, hP, hsum⟩ := exists_chamber_pieces α hα (coneVertsFam γ v)
  have hPσ : ∀ σ, hS (P σ) = hS (Finset.univ.image (kuhnVerts γ v σ)) := by
    intro σ
    apply hS_eq_of_convexHull_eq
    rw [hP σ, ← convexHull_kuhn_eq b hb σ]
    congr 1
    ext x
    rw [Set.mem_setOf_eq, mem_kuhnChamber]
    simp only [hαdef]
  have e : (fun y => paramidUnit γ v y -
      ∑ σ : Equiv.Perm (Fin k), hS (Finset.univ.image (kuhnVerts γ v σ)) y) =
      hS (coneVertsFam γ v) - ∑ σ : Equiv.Perm (Fin k), hS (P σ) := by
    funext y
    rw [Pi.sub_apply, Finset.sum_apply, paramidUnit_eq_hS_coneVertsFam]
    simp only [hPσ]
  rw [e]
  exact hsum

/-- **A degenerate paramid cone is lower-dimensional.**  If the frame `(v 0, …, v (k−1), γ)` is
linearly dependent (`k + 1 = m`), the cone lies in a proper subspace and its unit lies in
`LSpan m (m − 1)`. -/
theorem paramidUnit_mem_LSpan_of_not_linearIndependent {γ : Fin m → ℝ}
    {v : Fin k → Fin m → ℝ} (h : ¬ LinearIndependent ℝ (Fin.snoc v γ)) (hm : k + 1 = m) :
    paramidUnit γ v ∈ LSpan m (m - 1) := by
  rw [paramidUnit_eq_hS_coneVertsFam]
  refine hS_mem_LSpan_of_finrank_le (Finset.insert_nonempty _ _) ?_
  have hle : vectorSpan ℝ (coneVertsFam γ v : Set (Fin m → ℝ)) ≤
      Submodule.span ℝ (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)) := by
    rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    obtain ⟨p, q, hp, hq, rfl⟩ := Set.mem_vsub.mp hz
    exact Submodule.sub_mem _ (mem_span_of_mem_coneVertsFam hp)
      (mem_span_of_mem_coneVertsFam hq)
  have h1 : (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)).finrank ℝ ≤
      Fintype.card (Fin (k + 1)) := finrank_range_le_card
  have h2 : Fintype.card (Fin (k + 1)) ≠
      (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ)).finrank ℝ := fun e =>
    h (linearIndependent_iff_card_eq_finrank_span.mpr e)
  have hlt : FiniteDimensional.finrank ℝ
      (Submodule.span ℝ (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ))) < k + 1 := by
    have h3 := lt_of_le_of_ne h1 (Ne.symm h2)
    rw [Fintype.card_fin] at h3
    exact h3
  have h4 :
      FiniteDimensional.finrank ℝ (vectorSpan ℝ (coneVertsFam γ v : Set (Fin m → ℝ))) ≤
      FiniteDimensional.finrank ℝ
        (Submodule.span ℝ (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ))) :=
    Submodule.finrank_mono hle
  calc FiniteDimensional.finrank ℝ (vectorSpan ℝ (coneVertsFam γ v : Set (Fin m → ℝ)))
      ≤ FiniteDimensional.finrank ℝ
        (Submodule.span ℝ (Set.range (Fin.snoc v γ : Fin (k + 1) → Fin m → ℝ))) := h4
    _ ≤ k := Nat.lt_succ_iff.mp hlt
    _ = m - 1 := by rw [← hm, Nat.add_sub_cancel]

/-- Nonvacuity of the frame hypothesis: the standard basis `(e 0, …, e (n−1), e n)` of
`ℝ^(n+1)` is a linearly independent frame (with `n + 1` vectors in `ℝ^(n+1)`). -/
theorem exists_linearIndependent_frame (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (v : Fin n → Fin (n + 1) → ℝ),
      LinearIndependent ℝ (Fin.snoc v γ) := by
  refine ⟨Pi.single (Fin.last n) 1, fun i => Pi.single (Fin.castSucc i) 1, ?_⟩
  have e : (Fin.snoc (fun i : Fin n => (Pi.single (Fin.castSucc i) 1 : Fin (n + 1) → ℝ))
      (Pi.single (Fin.last n) 1) : Fin (n + 1) → Fin (n + 1) → ℝ) =
      ⇑(Pi.basisFun ℝ (Fin (n + 1))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Pi.basisFun_apply]
      rfl
    · rw [Fin.snoc_castSucc, Pi.basisFun_apply]
      rfl
  rw [e]
  exact (Pi.basisFun ℝ (Fin (n + 1))).linearIndependent

end

end MaxNN.ParamidGeom
