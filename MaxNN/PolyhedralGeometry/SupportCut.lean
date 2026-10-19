import MaxNN.PolyhedralGeometry.SupportCut.Transport
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Data.Finset.Pointwise

/-!
# Cutting a finite point set by a hyperplane: section, halves, and the cut identity

Fix a finite set `S ⊂ ℝ^N`, a normal vector `a ∈ ℝ^N` and a level `c ∈ ℝ`, and write
`d(p) = ⟨a, p⟩ − c` (`level a c p`, where `⟨a, p⟩ = dot a p = ∑ᵢ aᵢ pᵢ`).  The hyperplane
`H = {x | ⟨a, x⟩ = c}` splits `S` into

* `S⁺ = {p ∈ S | d(p) ≥ 0}` (`upperSide`), `S⁻ = {p ∈ S | d(p) ≤ 0}` (`lowerSide`),
  `S⁰ = {p ∈ S | d(p) = 0}` (`zeroSide`),

and each pair `p, q ∈ S` with `d(p) > 0 > d(q)` contributes the crossing point
`m(p, q) = (d(p) − d(q))⁻¹ • (d(p) • q − d(q) • p)` (`crossPoint`), the point of the segment
`[p, q]` on `H`.  `M` (`crossPoints`) is the finite set of all crossing points: the image of
`{p ∈ S | d(p) > 0} × {q ∈ S | d(q) < 0}` under `m`.  The three generating sets are
`S⁰ ∪ M` (`sectionPoints`), `S⁺ ∪ M` (`upperPoints`), `S⁻ ∪ M` (`lowerPoints`).

Support functions are finite maxima: for nonempty finite `T`,
`h_T(y) = max_{p ∈ T} ⟨p, y⟩ = T.sup' hT (fun p => dot p y)`, the convention of
`LowerDimSupport` (`Constructions/Paramid/LowerDim.lean`).

## Main results

* `convexHull_inter_hyperplane` (Theorem A (i)): `conv S ∩ H = conv (S⁰ ∪ M)`;
  `convexHull_inter_halfspace_ge`, `convexHull_inter_halfspace_le` (Theorem A (ii), (iii)):
  `conv S ∩ {d ≥ 0} = conv (S⁺ ∪ M)` and `conv S ∩ {d ≤ 0} = conv (S⁻ ∪ M)`.
  So a hyperplane section and the two halves of a polytope are again polytopes, with explicit
  finite generating sets.
* `sectionPoints_nonempty_iff`: `S⁰ ∪ M ≠ ∅ ↔ conv S ∩ H ≠ ∅`.
* `support_cut_identity` (Theorem B, the cut identity): if `S⁰ ∪ M ≠ ∅` then for every `y`,
  `h_S(y) + h_{S⁰ ∪ M}(y) = h_{S⁺ ∪ M}(y) + h_{S⁻ ∪ M}(y)`.  It follows from
  `h_S = max (h_{S⁺ ∪ M}, h_{S⁻ ∪ M})` (`sup'_eq_max_upperPoints_lowerPoints`) and
  `h_{S⁰ ∪ M} = min (h_{S⁺ ∪ M}, h_{S⁻ ∪ M})` (`sup'_sectionPoints_eq_min`); the proof does
  not use Theorem A.
* `sup'_add_eq` (Theorem C): `h_{S + T} = h_S + h_T` for the pointwise sumset `S + T`;
  `sup'_singleton_add_eq` (Theorem D): `h_{{t} + S}(y) = ⟨t, y⟩ + h_S(y)`.
* `dot_eq_of_mem_sectionPoints`: `S⁰ ∪ M ⊆ H`;
  `dot_sub_eq_zero_of_mem_sectionPoints`: differences of points of `S⁰ ∪ M` are orthogonal
  to `a`; `finrank_vectorSpan_sectionPoints_le`: for `a ≠ 0` the affine span of `S⁰ ∪ M` has
  dimension at most `N − 1` (the dimension clause of `LowerDimSupport N (N − 1)`).

Helpers, one level down: `SupportCut/Dot.lean` (bilinearity of `dot`) and
`SupportCut/Transport.lean` (the mass-transport identity behind Theorem A and the assembly of
convex combinations).
-/

namespace MaxNN

namespace SupportCut

open BigOperators

variable {N : ℕ}

/-! ## Definitions -/

/-- The signed level `d(p) = ⟨a, p⟩ − c` of `p` relative to the hyperplane
`H = {x | ⟨a, x⟩ = c}`. -/
noncomputable def level (a : Fin N → ℝ) (c : ℝ) (p : Fin N → ℝ) : ℝ := dot a p - c

/-- `S⁰ = {p ∈ S | d(p) = 0}`: the points of `S` on the hyperplane. -/
noncomputable def zeroSide (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  S.filter fun p => level a c p = 0

/-- `S⁺ = {p ∈ S | d(p) ≥ 0}`: the points of `S` in the closed positive half-space. -/
noncomputable def upperSide (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  S.filter fun p => 0 ≤ level a c p

/-- `S⁻ = {p ∈ S | d(p) ≤ 0}`: the points of `S` in the closed negative half-space. -/
noncomputable def lowerSide (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  S.filter fun p => level a c p ≤ 0

/-- The crossing point `m(p, q) = (d(p) − d(q))⁻¹ • (d(p) • q − d(q) • p)`.  For
`d(p) > 0 > d(q)` it equals `t • q + (1 − t) • p` with `t = d(p) / (d(p) − d(q)) ∈ [0, 1]`
(`crossPoint_eq_lineMap`) and lies on `H` (`level_crossPoint`): it is the point of the segment
`[p, q]` on the hyperplane. -/
noncomputable def crossPoint (a : Fin N → ℝ) (c : ℝ) (p q : Fin N → ℝ) : Fin N → ℝ :=
  (level a c p - level a c q)⁻¹ • (level a c p • q - level a c q • p)

/-- `M = {m(p, q) | p, q ∈ S, d(p) > 0, d(q) < 0}`: all crossing points, as the image of
`{p ∈ S | d(p) > 0} × {q ∈ S | d(q) < 0}` under `m`. -/
noncomputable def crossPoints (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  ((S.filter fun p => 0 < level a c p) ×ˢ (S.filter fun q => level a c q < 0)).image
    fun pq => crossPoint a c pq.1 pq.2

/-- `S⁰ ∪ M`: the finite generating set of the section `conv S ∩ H`. -/
noncomputable def sectionPoints (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  zeroSide S a c ∪ crossPoints S a c

/-- `S⁺ ∪ M`: the finite generating set of the half `conv S ∩ {d ≥ 0}`. -/
noncomputable def upperPoints (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  upperSide S a c ∪ crossPoints S a c

/-- `S⁻ ∪ M`: the finite generating set of the half `conv S ∩ {d ≤ 0}`. -/
noncomputable def lowerPoints (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    Finset (Fin N → ℝ) :=
  lowerSide S a c ∪ crossPoints S a c

/-! ## Crossing points -/

theorem crossPoint_eq_segCross (a : Fin N → ℝ) (c : ℝ) (p q : Fin N → ℝ) :
    crossPoint a c p q = segCross (level a c) p q := rfl

theorem crossPoint_eq_lineMap (a : Fin N → ℝ) (c : ℝ) {p q : Fin N → ℝ}
    (h : level a c p - level a c q ≠ 0) :
    crossPoint a c p q =
      (level a c p / (level a c p - level a c q)) • q +
        (1 - level a c p / (level a c p - level a c q)) • p :=
  segCross_eq (level a c) h

theorem crossPoint_mem_crossPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    {p q : Fin N → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hdp : 0 < level a c p)
    (hdq : level a c q < 0) : crossPoint a c p q ∈ crossPoints S a c :=
  Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨hp, hdp⟩, Finset.mem_filter.mpr ⟨hq, hdq⟩⟩, rfl⟩

theorem exists_of_mem_crossPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ crossPoints S a c) :
    ∃ p q, p ∈ S ∧ q ∈ S ∧ 0 < level a c p ∧ level a c q < 0 ∧ crossPoint a c p q = x := by
  obtain ⟨⟨p, q⟩, hpq, hx⟩ := Finset.mem_image.mp hx
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
  obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqS, hqd⟩ := Finset.mem_filter.mp hq
  exact ⟨p, q, hpS, hqS, hpd, hqd, hx⟩

/-- Crossing points lie on the hyperplane. -/
theorem level_crossPoint (a : Fin N → ℝ) (c : ℝ) {p q : Fin N → ℝ}
    (h : level a c p - level a c q ≠ 0) : level a c (crossPoint a c p q) = 0 := by
  show dot a ((level a c p - level a c q)⁻¹ • (level a c p • q - level a c q • p)) - c = 0
  rw [dot_smul_right, dot_sub_right, dot_smul_right, dot_smul_right]
  have e : level a c p * dot a q - level a c q * dot a p = (level a c p - level a c q) * c := by
    show (dot a p - c) * dot a q - (dot a q - c) * dot a p = (dot a p - c - (dot a q - c)) * c
    ring
  rw [e, ← mul_assoc, inv_mul_cancel h, one_mul, sub_self]

/-- Crossing points lie in the convex hull of `S`. -/
theorem crossPoint_mem_convexHull {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    {p q : Fin N → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hdp : 0 < level a c p)
    (hdq : level a c q < 0) : crossPoint a c p q ∈ convexHull ℝ (↑S : Set (Fin N → ℝ)) := by
  have hD : level a c p - level a c q ≠ 0 := (sub_pos.mpr (hdq.trans hdp)).ne'
  rw [crossPoint_eq_segCross, segCross_eq (level a c) hD]
  exact convex_convexHull ℝ (↑S : Set (Fin N → ℝ))
    (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq)) (subset_convexHull ℝ _ (Finset.mem_coe.mpr hp))
    (crossParam_nonneg hdp hdq) (sub_nonneg.mpr (crossParam_le_one hdp hdq)) (by ring)

theorem dot_crossPoint_le_max {a : Fin N → ℝ} {c : ℝ} {p q : Fin N → ℝ}
    (hdp : 0 < level a c p) (hdq : level a c q < 0) (y : Fin N → ℝ) :
    dot (crossPoint a c p q) y ≤ max (dot p y) (dot q y) := by
  have hD : level a c p - level a c q ≠ 0 := (sub_pos.mpr (hdq.trans hdp)).ne'
  rw [crossPoint_eq_segCross, dot_segCross_left (level a c) hD y, max_comm]
  exact convexComb_le_max (crossParam_nonneg hdp hdq) (crossParam_le_one hdp hdq)

theorem min_le_dot_crossPoint {a : Fin N → ℝ} {c : ℝ} {p q : Fin N → ℝ}
    (hdp : 0 < level a c p) (hdq : level a c q < 0) (y : Fin N → ℝ) :
    min (dot p y) (dot q y) ≤ dot (crossPoint a c p q) y := by
  have hD : level a c p - level a c q ≠ 0 := (sub_pos.mpr (hdq.trans hdp)).ne'
  rw [crossPoint_eq_segCross, dot_segCross_left (level a c) hD y, min_comm]
  exact min_le_convexComb (crossParam_nonneg hdp hdq) (crossParam_le_one hdp hdq)

/-! ## Membership bookkeeping -/

section Membership

variable {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}

theorem mem_sectionPoints_of_mem {p : Fin N → ℝ} (hp : p ∈ S) (h : level a c p = 0) :
    p ∈ sectionPoints S a c :=
  Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)

theorem mem_upperPoints_of_mem {p : Fin N → ℝ} (hp : p ∈ S) (h : 0 ≤ level a c p) :
    p ∈ upperPoints S a c :=
  Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)

theorem mem_lowerPoints_of_mem {p : Fin N → ℝ} (hp : p ∈ S) (h : level a c p ≤ 0) :
    p ∈ lowerPoints S a c :=
  Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)

theorem crossPoints_subset_sectionPoints : crossPoints S a c ⊆ sectionPoints S a c :=
  Finset.subset_union_right _ _

theorem crossPoints_subset_upperPoints : crossPoints S a c ⊆ upperPoints S a c :=
  Finset.subset_union_right _ _

theorem crossPoints_subset_lowerPoints : crossPoints S a c ⊆ lowerPoints S a c :=
  Finset.subset_union_right _ _

theorem crossPoint_mem_sectionPoints {p q : Fin N → ℝ} (hp : p ∈ S) (hq : q ∈ S)
    (hdp : 0 < level a c p) (hdq : level a c q < 0) :
    crossPoint a c p q ∈ sectionPoints S a c :=
  crossPoints_subset_sectionPoints (crossPoint_mem_crossPoints hp hq hdp hdq)

theorem crossPoint_mem_upperPoints {p q : Fin N → ℝ} (hp : p ∈ S) (hq : q ∈ S)
    (hdp : 0 < level a c p) (hdq : level a c q < 0) :
    crossPoint a c p q ∈ upperPoints S a c :=
  crossPoints_subset_upperPoints (crossPoint_mem_crossPoints hp hq hdp hdq)

theorem crossPoint_mem_lowerPoints {p q : Fin N → ℝ} (hp : p ∈ S) (hq : q ∈ S)
    (hdp : 0 < level a c p) (hdq : level a c q < 0) :
    crossPoint a c p q ∈ lowerPoints S a c :=
  crossPoints_subset_lowerPoints (crossPoint_mem_crossPoints hp hq hdp hdq)

theorem sectionPoints_subset_upperPoints : sectionPoints S a c ⊆ upperPoints S a c := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    exact mem_upperPoints_of_mem hxS hx0.ge
  · exact crossPoints_subset_upperPoints hx

theorem sectionPoints_subset_lowerPoints : sectionPoints S a c ⊆ lowerPoints S a c := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    exact mem_lowerPoints_of_mem hxS hx0.le
  · exact crossPoints_subset_lowerPoints hx

theorem nonempty_of_nonempty_sectionPoints (h : (sectionPoints S a c).Nonempty) :
    S.Nonempty := by
  obtain ⟨x, hx⟩ := h
  rcases Finset.mem_union.mp hx with hx | hx
  · exact ⟨x, (Finset.mem_filter.mp hx).1⟩
  · obtain ⟨p, q, hp, -, -, -, -⟩ := exists_of_mem_crossPoints hx
    exact ⟨p, hp⟩

theorem nonempty_upperPoints (h : (sectionPoints S a c).Nonempty) :
    (upperPoints S a c).Nonempty :=
  h.mono sectionPoints_subset_upperPoints

theorem nonempty_lowerPoints (h : (sectionPoints S a c).Nonempty) :
    (lowerPoints S a c).Nonempty :=
  h.mono sectionPoints_subset_lowerPoints

/-- A point of `S⁺ ∪ M` outside `S⁰ ∪ M` is a point of `S` strictly above `H`. -/
theorem mem_and_pos_of_mem_upperPoints {u : Fin N → ℝ} (hu : u ∈ upperPoints S a c)
    (huZ : u ∉ sectionPoints S a c) : u ∈ S ∧ 0 < level a c u := by
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨huS, hu0⟩ := Finset.mem_filter.mp hu
    exact ⟨huS, lt_of_le_of_ne hu0 fun h => huZ (mem_sectionPoints_of_mem huS h.symm)⟩
  · exact absurd (crossPoints_subset_sectionPoints hu) huZ

/-- A point of `S⁻ ∪ M` outside `S⁰ ∪ M` is a point of `S` strictly below `H`. -/
theorem mem_and_neg_of_mem_lowerPoints {l : Fin N → ℝ} (hl : l ∈ lowerPoints S a c)
    (hlZ : l ∉ sectionPoints S a c) : l ∈ S ∧ level a c l < 0 := by
  rcases Finset.mem_union.mp hl with hl | hl
  · obtain ⟨hlS, hl0⟩ := Finset.mem_filter.mp hl
    exact ⟨hlS, lt_of_le_of_ne hl0 fun h => hlZ (mem_sectionPoints_of_mem hlS h)⟩
  · exact absurd (crossPoints_subset_sectionPoints hl) hlZ

end Membership

/-! ## Theorem B: the cut identity -/

theorem dot_le_sup'_of_mem_crossPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    (hS : S.Nonempty) {z : Fin N → ℝ} (hz : z ∈ crossPoints S a c) (y : Fin N → ℝ) :
    dot z y ≤ S.sup' hS (fun p => dot p y) := by
  obtain ⟨p, q, hp, hq, hdp, hdq, rfl⟩ := exists_of_mem_crossPoints hz
  exact le_trans (dot_crossPoint_le_max hdp hdq y)
    (max_le (Finset.le_sup' (fun p => dot p y) hp) (Finset.le_sup' (fun p => dot p y) hq))

/-- `h_S = max (h_{S⁺ ∪ M}, h_{S⁻ ∪ M})`. -/
theorem sup'_eq_max_upperPoints_lowerPoints (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ)
    (hS : S.Nonempty) (hU : (upperPoints S a c).Nonempty) (hL : (lowerPoints S a c).Nonempty)
    (y : Fin N → ℝ) :
    S.sup' hS (fun p => dot p y) =
      max ((upperPoints S a c).sup' hU fun p => dot p y)
        ((lowerPoints S a c).sup' hL fun p => dot p y) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p hp => ?_
    rcases le_total 0 (level a c p) with h | h
    · exact le_trans (Finset.le_sup' (fun p => dot p y) (mem_upperPoints_of_mem hp h))
        (le_max_left _ _)
    · exact le_trans (Finset.le_sup' (fun p => dot p y) (mem_lowerPoints_of_mem hp h))
        (le_max_right _ _)
  · refine max_le (Finset.sup'_le _ _ fun z hz => ?_) (Finset.sup'_le _ _ fun z hz => ?_)
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.le_sup' (fun p => dot p y) (Finset.mem_filter.mp hz).1
      · exact dot_le_sup'_of_mem_crossPoints hS hz y
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.le_sup' (fun p => dot p y) (Finset.mem_filter.mp hz).1
      · exact dot_le_sup'_of_mem_crossPoints hS hz y

/-- `h_{S⁰ ∪ M} = min (h_{S⁺ ∪ M}, h_{S⁻ ∪ M})`.  For `≥`: take maximizers `u ∈ S⁺ ∪ M` and
`l ∈ S⁻ ∪ M`; if either lies in `S⁰ ∪ M` we are done, otherwise `d(u) > 0 > d(l)` and the
crossing point `m(u, l) ∈ M` has `⟨m(u, l), y⟩ ≥ min (⟨u, y⟩, ⟨l, y⟩)`. -/
theorem sup'_sectionPoints_eq_min (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ)
    (hZ : (sectionPoints S a c).Nonempty) (hU : (upperPoints S a c).Nonempty)
    (hL : (lowerPoints S a c).Nonempty) (y : Fin N → ℝ) :
    (sectionPoints S a c).sup' hZ (fun p => dot p y) =
      min ((upperPoints S a c).sup' hU fun p => dot p y)
        ((lowerPoints S a c).sup' hL fun p => dot p y) := by
  apply le_antisymm
  · exact le_min (Finset.sup'_mono (fun p => dot p y) sectionPoints_subset_upperPoints hZ)
      (Finset.sup'_mono (fun p => dot p y) sectionPoints_subset_lowerPoints hZ)
  · obtain ⟨u, hu, hue⟩ := Finset.exists_mem_eq_sup' hU (fun p => dot p y)
    obtain ⟨l, hl, hle⟩ := Finset.exists_mem_eq_sup' hL (fun p => dot p y)
    rw [hue, hle]
    by_cases huZ : u ∈ sectionPoints S a c
    · exact le_trans (min_le_left _ _) (Finset.le_sup' (fun p => dot p y) huZ)
    by_cases hlZ : l ∈ sectionPoints S a c
    · exact le_trans (min_le_right _ _) (Finset.le_sup' (fun p => dot p y) hlZ)
    obtain ⟨huS, hu0⟩ := mem_and_pos_of_mem_upperPoints hu huZ
    obtain ⟨hlS, hl0⟩ := mem_and_neg_of_mem_lowerPoints hl hlZ
    exact le_trans (min_le_dot_crossPoint hu0 hl0 y)
      (Finset.le_sup' (fun p => dot p y) (crossPoint_mem_sectionPoints huS hlS hu0 hl0))

/-- **Theorem B (the cut identity).**  If the section point set `S⁰ ∪ M` is nonempty
(equivalently `conv S ∩ H ≠ ∅`, `sectionPoints_nonempty_iff`), then for every `y`
`h_S(y) + h_{S⁰ ∪ M}(y) = h_{S⁺ ∪ M}(y) + h_{S⁻ ∪ M}(y)`, where
`h_T(y) = max_{p ∈ T} ⟨p, y⟩`.  (The nonemptiness proofs inside `Finset.sup'` are
proof-irrelevant; any proofs may be substituted.) -/
theorem support_cut_identity (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ)
    (h0 : (sectionPoints S a c).Nonempty) (y : Fin N → ℝ) :
    S.sup' (nonempty_of_nonempty_sectionPoints h0) (fun p => dot p y) +
        (sectionPoints S a c).sup' h0 (fun p => dot p y) =
      (upperPoints S a c).sup' (nonempty_upperPoints h0) (fun p => dot p y) +
        (lowerPoints S a c).sup' (nonempty_lowerPoints h0) (fun p => dot p y) := by
  rw [sup'_eq_max_upperPoints_lowerPoints S a c (nonempty_of_nonempty_sectionPoints h0)
      (nonempty_upperPoints h0) (nonempty_lowerPoints h0) y,
    sup'_sectionPoints_eq_min S a c h0 (nonempty_upperPoints h0) (nonempty_lowerPoints h0) y]
  exact (add_comm _ _).trans (min_add_max _ _)

/-! ## Theorems C and D: Minkowski sums and translates -/

open Pointwise in
/-- **Theorem C.** `h_{S + T}(y) = h_S(y) + h_T(y)` for the pointwise sumset
`S + T = {p + q | p ∈ S, q ∈ T}`. -/
theorem sup'_add_eq (S T : Finset (Fin N → ℝ)) (hS : S.Nonempty) (hT : T.Nonempty)
    (y : Fin N → ℝ) :
    (S + T).sup' (hS.add hT) (fun p => dot p y) =
      S.sup' hS (fun p => dot p y) + T.sup' hT (fun p => dot p y) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun z hz => ?_
    obtain ⟨p, q, hp, hq, rfl⟩ := Finset.mem_add.mp hz
    rw [dot_add_left]
    exact add_le_add (Finset.le_sup' (fun p => dot p y) hp) (Finset.le_sup' (fun p => dot p y) hq)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' hS (fun p => dot p y)
    obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_sup' hT (fun p => dot p y)
    rw [hpe, hqe, ← dot_add_left]
    exact Finset.le_sup' (fun p => dot p y) (Finset.add_mem_add hp hq)

open Pointwise in
/-- **Theorem D (translation).** `h_{{t} + S}(y) = ⟨t, y⟩ + h_S(y)`. -/
theorem sup'_singleton_add_eq (t : Fin N → ℝ) (S : Finset (Fin N → ℝ)) (hS : S.Nonempty)
    (y : Fin N → ℝ) :
    ({t} + S).sup' ((Finset.singleton_nonempty t).add hS) (fun p => dot p y) =
      dot t y + S.sup' hS (fun p => dot p y) := by
  rw [sup'_add_eq {t} S (Finset.singleton_nonempty t) hS y, Finset.sup'_singleton]

/-! ## The section lies in the hyperplane, hence is lower-dimensional -/

/-- Every point of `S⁰ ∪ M` lies on `H = {x | ⟨a, x⟩ = c}`. -/
theorem dot_eq_of_mem_sectionPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ sectionPoints S a c) : dot a x = c := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact sub_eq_zero.mp (Finset.mem_filter.mp hx).2
  · obtain ⟨p, q, -, -, hdp, hdq, rfl⟩ := exists_of_mem_crossPoints hx
    exact sub_eq_zero.mp (level_crossPoint a c (sub_pos.mpr (hdq.trans hdp)).ne')

/-- Differences of points of `S⁰ ∪ M` are orthogonal to `a`. -/
theorem dot_sub_eq_zero_of_mem_sectionPoints {S : Finset (Fin N → ℝ)} {a : Fin N → ℝ} {c : ℝ}
    {x x' : Fin N → ℝ} (hx : x ∈ sectionPoints S a c) (hx' : x' ∈ sectionPoints S a c) :
    dot a (x - x') = 0 := by
  rw [dot_sub_right, dot_eq_of_mem_sectionPoints hx, dot_eq_of_mem_sectionPoints hx', sub_self]

/-- A set contained in an affine hyperplane `{x | ⟨a, x⟩ = c}` with `a ≠ 0` has affine span of
dimension at most `N − 1`: its direction `vectorSpan` lies in `ker ⟨a, ·⟩ ⊊ ℝ^N`. -/
theorem finrank_vectorSpan_le_of_forall_dot_eq {a : Fin N → ℝ} (ha : a ≠ 0) {c : ℝ}
    {T : Set (Fin N → ℝ)} (hT : ∀ x ∈ T, dot a x = c) :
    FiniteDimensional.finrank ℝ (vectorSpan ℝ T) ≤ N - 1 := by
  have hle : vectorSpan ℝ T ≤ LinearMap.ker (dotL a) := by
    rw [vectorSpan_def, Submodule.span_le]
    intro v hv
    obtain ⟨x, x', hx, hx', rfl⟩ := Set.mem_vsub.mp hv
    rw [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, dotL_apply, dot_sub_right, hT x hx,
      hT x' hx', sub_self]
  have hlt : LinearMap.ker (dotL a) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hmem : a ∈ LinearMap.ker (dotL a) := by
      rw [htop]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, dotL_apply] at hmem
    exact ha (eq_zero_of_dot_self_eq_zero hmem)
  have h1 : FiniteDimensional.finrank ℝ (vectorSpan ℝ T) ≤
      FiniteDimensional.finrank ℝ (LinearMap.ker (dotL a)) :=
    Submodule.finrank_mono hle
  have h2 := Submodule.finrank_lt hlt
  rw [FiniteDimensional.finrank_fin_fun] at h2
  exact Nat.le_sub_one_of_lt (lt_of_le_of_lt h1 h2)

/-- **The section is lower-dimensional.**  For `a ≠ 0` the affine span of `S⁰ ∪ M` has dimension
at most `N − 1`, which is the dimension clause of `LowerDimSupport N (N − 1)`. -/
theorem finrank_vectorSpan_sectionPoints_le (S : Finset (Fin N → ℝ)) {a : Fin N → ℝ}
    (ha : a ≠ 0) (c : ℝ) :
    FiniteDimensional.finrank ℝ
        (vectorSpan ℝ (↑(sectionPoints S a c) : Set (Fin N → ℝ))) ≤ N - 1 :=
  finrank_vectorSpan_le_of_forall_dot_eq ha fun _ hx =>
    dot_eq_of_mem_sectionPoints (Finset.mem_coe.mp hx)

/-! ## Theorem A: the section and the two halves are polytopes -/

/-- `d(∑ w_y y) = ∑ w_y d(y)` for weights summing to `1`. -/
theorem level_sum_smul (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ)
    (w : (Fin N → ℝ) → ℝ) (hw1 : ∑ y in S, w y = 1) :
    level a c (∑ y in S, w y • y) = ∑ y in S, w y * level a c y := by
  show dot a (∑ y in S, w y • y) - c = ∑ y in S, w y * (dot a y - c)
  rw [dot_sum_smul_right]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]

/-- The level of a convex combination of `S` is its positive mass `∑_{d > 0} w d` plus its
negative mass `∑_{d < 0} w d`. -/
theorem level_convexComb (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ)
    (w : (Fin N → ℝ) → ℝ) (hw1 : ∑ y in S, w y = 1) :
    level a c (∑ y in S, w y • y) =
      ∑ p in S.filter (fun y => 0 < level a c y), w p * level a c p +
        ∑ q in S.filter (fun y => level a c y < 0), w q * level a c q := by
  have hsplit : ∑ y in S, w y * level a c y =
      ∑ y in S.filter (fun y => level a c y = 0), w y * level a c y +
        (∑ y in S.filter (fun y => 0 < level a c y), w y * level a c y +
          ∑ y in S.filter (fun y => level a c y < 0), w y * level a c y) :=
    sum_split_sign S (level a c) (fun y => w y * level a c y)
  have h0 : ∑ y in S.filter (fun y => level a c y = 0), w y * level a c y = 0 :=
    Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.mp hy).2, mul_zero]
  rw [level_sum_smul S a c w hw1, hsplit, h0, zero_add]

/-- **Theorem A (i): a hyperplane section of a polytope is a polytope.**
`conv S ∩ {x | ⟨a, x⟩ = c} = conv (S⁰ ∪ M)`.  For `⊆`, write `x = ∑ w_p p`; on `H` the positive
mass `A = ∑_{d > 0} w d` equals the negative mass `−∑_{d < 0} w d`, and
`x = ∑_{S⁰} w_s s + ∑_{p, q} (w_p w_q (d(p) − d(q)) / A) m(p, q)` (`mix_vec`). -/
theorem convexHull_inter_hyperplane (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    convexHull ℝ (↑S : Set (Fin N → ℝ)) ∩ {x | dot a x = c} =
      convexHull ℝ (↑(sectionPoints S a c) : Set (Fin N → ℝ)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwx
    have hxw : x = ∑ y in S, w y • y := hwx.symm
    subst hxw
    have hlev : level a c (∑ y in S, w y • y) = 0 := sub_eq_zero.mpr hxc
    rw [level_convexComb S a c w hw1] at hlev
    set P := S.filter (fun y => 0 < level a c y)
    set Q := S.filter (fun y => level a c y < 0)
    have hP : ∀ p ∈ P, 0 < level a c p := fun p hp => (Finset.mem_filter.mp hp).2
    have hQ : ∀ q ∈ Q, level a c q < 0 := fun q hq => (Finset.mem_filter.mp hq).2
    have hwP : ∀ p ∈ P, 0 ≤ w p := fun p hp => hw0 p (Finset.mem_filter.mp hp).1
    have hwQ : ∀ q ∈ Q, 0 ≤ w q := fun q hq => hw0 q (Finset.mem_filter.mp hq).1
    have hBA : -(∑ q in Q, w q * level a c q) ≤ ∑ p in P, w p * level a c p := by linarith
    have hzero : ∀ p ∈ P, (1 - mixRatio P Q (level a c) w) * w p = 0 :=
      fun p hp => one_sub_mixRatio_mul_eq_zero (δ := level a c) hP hwP hlev hp
    have hPV : ∑ p in P, ((1 - mixRatio P Q (level a c) w) * w p) • p = 0 :=
      Finset.sum_eq_zero fun p hp => by rw [hzero p hp, zero_smul]
    have hPW : ∑ p in P, (1 - mixRatio P Q (level a c) w) * w p = 0 :=
      Finset.sum_eq_zero hzero
    have hV := mix_vec P Q (level a c) w hP hQ hwQ hBA
    have hW := mix_weights P Q (level a c) w hQ hwQ hBA
    rw [hPV, zero_add] at hV
    rw [hPW, zero_add] at hW
    have hsplitV : ∑ y in S, w y • y = ∑ y in S.filter (fun y => level a c y = 0), w y • y +
        (∑ y in P, w y • y + ∑ y in Q, w y • y) :=
      sum_split_sign S (level a c) (fun y => w y • y)
    have hsplitW : ∑ y in S, w y = ∑ y in S.filter (fun y => level a c y = 0), w y +
        (∑ y in P, w y + ∑ y in Q, w y) :=
      sum_split_sign S (level a c) w
    rw [hW] at hsplitW
    rw [hsplitV, hV]
    have hA0 : 0 ≤ ∑ p in P, w p * level a c p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (hwP p hp) (hP p hp).le
    refine sum_add_sum_mem (convex_convexHull ℝ _) _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      exact hw0 y (Finset.mem_filter.mp hy).1
    · rintro ⟨p, q⟩ hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      exact crossWeight_nonneg hA0 (hwP p hp) (hwQ q hq) ((hQ q hq).trans (hP p hp)).le
    · rw [← hsplitW]
      exact hw1
    · intro y hy
      obtain ⟨hyS, hy0⟩ := Finset.mem_filter.mp hy
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (mem_sectionPoints_of_mem hyS hy0))
    · rintro ⟨p, q⟩ hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      obtain ⟨hpS, hp0⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqS, hq0⟩ := Finset.mem_filter.mp hq
      exact subset_convexHull ℝ _
        (Finset.mem_coe.mpr (crossPoint_mem_sectionPoints hpS hqS hp0 hq0))
  · refine convexHull_min ?_
      ((convex_convexHull ℝ _).inter (convex_hyperplane (dotL a).isLinear c))
    intro z hz
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hz) with hz | hz
    · obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
      exact ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hzS), sub_eq_zero.mp hz0⟩
    · obtain ⟨p, q, hp, hq, hdp, hdq, rfl⟩ := exists_of_mem_crossPoints hz
      exact ⟨crossPoint_mem_convexHull hp hq hdp hdq,
        sub_eq_zero.mp (level_crossPoint a c (sub_pos.mpr (hdq.trans hdp)).ne')⟩

/-- **Theorem A (ii).** `conv S ∩ {x | ⟨a, x⟩ ≥ c} = conv (S⁺ ∪ M)`.  For `⊆`, with positive
mass `A` and negative mass `B ≤ A`, the fraction `θ = B / A` of each positive weight is
transported across `H` and the rest stays on `S⁺` (`mix_vec`). -/
theorem convexHull_inter_halfspace_ge (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    convexHull ℝ (↑S : Set (Fin N → ℝ)) ∩ {x | c ≤ dot a x} =
      convexHull ℝ (↑(upperPoints S a c) : Set (Fin N → ℝ)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwx
    have hxw : x = ∑ y in S, w y • y := hwx.symm
    subst hxw
    have hlev : 0 ≤ level a c (∑ y in S, w y • y) := sub_nonneg.mpr hxc
    rw [level_convexComb S a c w hw1] at hlev
    set P := S.filter (fun y => 0 < level a c y)
    set Q := S.filter (fun y => level a c y < 0)
    have hP : ∀ p ∈ P, 0 < level a c p := fun p hp => (Finset.mem_filter.mp hp).2
    have hQ : ∀ q ∈ Q, level a c q < 0 := fun q hq => (Finset.mem_filter.mp hq).2
    have hwP : ∀ p ∈ P, 0 ≤ w p := fun p hp => hw0 p (Finset.mem_filter.mp hp).1
    have hwQ : ∀ q ∈ Q, 0 ≤ w q := fun q hq => hw0 q (Finset.mem_filter.mp hq).1
    have hBA : -(∑ q in Q, w q * level a c q) ≤ ∑ p in P, w p * level a c p := by linarith
    have hV := mix_vec P Q (level a c) w hP hQ hwQ hBA
    have hW := mix_weights P Q (level a c) w hQ hwQ hBA
    have hsplitV : ∑ y in S, w y • y = ∑ y in S.filter (fun y => level a c y = 0), w y • y +
        (∑ y in P, w y • y + ∑ y in Q, w y • y) :=
      sum_split_sign S (level a c) (fun y => w y • y)
    have hsplitW : ∑ y in S, w y = ∑ y in S.filter (fun y => level a c y = 0), w y +
        (∑ y in P, w y + ∑ y in Q, w y) :=
      sum_split_sign S (level a c) w
    rw [hW, ← add_assoc] at hsplitW
    rw [hsplitV, hV, ← add_assoc]
    have hA0 : 0 ≤ ∑ p in P, w p * level a c p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (hwP p hp) (hP p hp).le
    refine sum_add_sum_add_sum_mem (convex_convexHull ℝ _) _ _ _ _ _ _ _ _ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      exact hw0 y (Finset.mem_filter.mp hy).1
    · intro p hp
      exact mul_nonneg (one_sub_mixRatio_nonneg hP hwP hBA) (hwP p hp)
    · rintro ⟨p, q⟩ hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      exact crossWeight_nonneg hA0 (hwP p hp) (hwQ q hq) ((hQ q hq).trans (hP p hp)).le
    · rw [← hsplitW]
      exact hw1
    · intro y hy
      obtain ⟨hyS, hy0⟩ := Finset.mem_filter.mp hy
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (mem_upperPoints_of_mem hyS hy0.ge))
    · intro p hp
      obtain ⟨hpS, hp0⟩ := Finset.mem_filter.mp hp
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (mem_upperPoints_of_mem hpS hp0.le))
    · rintro ⟨p, q⟩ hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      obtain ⟨hpS, hp0⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqS, hq0⟩ := Finset.mem_filter.mp hq
      exact subset_convexHull ℝ _
        (Finset.mem_coe.mpr (crossPoint_mem_upperPoints hpS hqS hp0 hq0))
  · refine convexHull_min ?_
      ((convex_convexHull ℝ _).inter (convex_halfspace_ge (dotL a).isLinear c))
    intro z hz
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hz) with hz | hz
    · obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
      exact ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hzS), sub_nonneg.mp hz0⟩
    · obtain ⟨p, q, hp, hq, hdp, hdq, rfl⟩ := exists_of_mem_crossPoints hz
      exact ⟨crossPoint_mem_convexHull hp hq hdp hdq,
        (sub_eq_zero.mp (level_crossPoint a c (sub_pos.mpr (hdq.trans hdp)).ne')).ge⟩

/-- **Theorem A (iii).** `conv S ∩ {x | ⟨a, x⟩ ≤ c} = conv (S⁻ ∪ M)`: Theorem A (ii) for the
level function `−d`, which exchanges the two sides and fixes every crossing point
(`segCross_neg_swap`). -/
theorem convexHull_inter_halfspace_le (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    convexHull ℝ (↑S : Set (Fin N → ℝ)) ∩ {x | dot a x ≤ c} =
      convexHull ℝ (↑(lowerPoints S a c) : Set (Fin N → ℝ)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwx
    have hxw : x = ∑ y in S, w y • y := hwx.symm
    subst hxw
    have hlev : level a c (∑ y in S, w y • y) ≤ 0 := sub_nonpos.mpr hxc
    rw [level_convexComb S a c w hw1] at hlev
    set P := S.filter (fun y => 0 < level a c y)
    set Q := S.filter (fun y => level a c y < 0)
    have hP' : ∀ p ∈ Q, 0 < -level a c p := fun p hp => neg_pos.mpr (Finset.mem_filter.mp hp).2
    have hQ' : ∀ q ∈ P, -level a c q < 0 :=
      fun q hq => neg_lt_zero.mpr (Finset.mem_filter.mp hq).2
    have hwP : ∀ p ∈ P, 0 ≤ w p := fun p hp => hw0 p (Finset.mem_filter.mp hp).1
    have hwQ : ∀ q ∈ Q, 0 ≤ w q := fun q hq => hw0 q (Finset.mem_filter.mp hq).1
    have e1 : ∑ q in P, w q * -level a c q = -(∑ q in P, w q * level a c q) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun q _ => mul_neg (w q) (level a c q)
    have e2 : ∑ p in Q, w p * -level a c p = -(∑ p in Q, w p * level a c p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => mul_neg (w p) (level a c p)
    have hBA : -(∑ q in P, w q * -level a c q) ≤ ∑ p in Q, w p * -level a c p := by
      rw [e1, e2]
      linarith
    have hV := mix_vec Q P (fun y => -level a c y) w hP' hQ' hwP hBA
    have hW := mix_weights Q P (fun y => -level a c y) w hQ' hwP hBA
    have hsplitV : ∑ y in S, w y • y = ∑ y in S.filter (fun y => level a c y = 0), w y • y +
        (∑ y in Q, w y • y + ∑ y in P, w y • y) :=
      sum_split_sign' S (level a c) (fun y => w y • y)
    have hsplitW : ∑ y in S, w y = ∑ y in S.filter (fun y => level a c y = 0), w y +
        (∑ y in Q, w y + ∑ y in P, w y) :=
      sum_split_sign' S (level a c) w
    rw [hW, ← add_assoc] at hsplitW
    rw [hsplitV, hV, ← add_assoc]
    have hA0 : 0 ≤ ∑ p in Q, w p * -level a c p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (hwQ p hp) (hP' p hp).le
    refine sum_add_sum_add_sum_mem (convex_convexHull ℝ _) _ _ _ _ _ _ _ _ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      exact hw0 y (Finset.mem_filter.mp hy).1
    · intro p hp
      exact mul_nonneg (one_sub_mixRatio_nonneg hP' hwQ hBA) (hwQ p hp)
    · rintro ⟨q, p⟩ hqp
      obtain ⟨hq, hp⟩ := Finset.mem_product.mp hqp
      exact crossWeight_nonneg hA0 (hwQ q hq) (hwP p hp) ((hQ' p hp).trans (hP' q hq)).le
    · rw [← hsplitW]
      exact hw1
    · intro y hy
      obtain ⟨hyS, hy0⟩ := Finset.mem_filter.mp hy
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (mem_lowerPoints_of_mem hyS hy0.le))
    · intro q hq
      obtain ⟨hqS, hq0⟩ := Finset.mem_filter.mp hq
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (mem_lowerPoints_of_mem hqS hq0.le))
    · rintro ⟨q, p⟩ hqp
      obtain ⟨hq, hp⟩ := Finset.mem_product.mp hqp
      obtain ⟨hqS, hq0⟩ := Finset.mem_filter.mp hq
      obtain ⟨hpS, hp0⟩ := Finset.mem_filter.mp hp
      show segCross (fun y => -level a c y) q p ∈
        convexHull ℝ (↑(lowerPoints S a c) : Set (Fin N → ℝ))
      rw [segCross_neg_swap]
      exact subset_convexHull ℝ _
        (Finset.mem_coe.mpr (crossPoint_mem_lowerPoints hpS hqS hp0 hq0))
  · refine convexHull_min ?_
      ((convex_convexHull ℝ _).inter (convex_halfspace_le (dotL a).isLinear c))
    intro z hz
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hz) with hz | hz
    · obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
      exact ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr hzS), sub_nonpos.mp hz0⟩
    · obtain ⟨p, q, hp, hq, hdp, hdq, rfl⟩ := exists_of_mem_crossPoints hz
      exact ⟨crossPoint_mem_convexHull hp hq hdp hdq,
        (sub_eq_zero.mp (level_crossPoint a c (sub_pos.mpr (hdq.trans hdp)).ne')).le⟩

/-- `S⁰ ∪ M` is nonempty iff the section `conv S ∩ H` is nonempty. -/
theorem sectionPoints_nonempty_iff (S : Finset (Fin N → ℝ)) (a : Fin N → ℝ) (c : ℝ) :
    (sectionPoints S a c).Nonempty ↔
      (convexHull ℝ (↑S : Set (Fin N → ℝ)) ∩ {x | dot a x = c}).Nonempty := by
  rw [convexHull_inter_hyperplane, convexHull_nonempty_iff, Finset.coe_nonempty]

end SupportCut

end MaxNN
