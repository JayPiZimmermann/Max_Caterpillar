import MaxNN.PolyhedralGeometry.SupportCut.Dot
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Sum

/-!
# Mass transport across a hyperplane (helper for `PolyhedralGeometry/SupportCut.lean`)

Let `δ` be a level function (in applications `δ p = ⟨a, p⟩ − c`), `P` a finite set on which
`δ > 0`, `Q` a finite set on which `δ < 0`, and `w ≥ 0` weights.  Write
`A = ∑_{p ∈ P} w_p δ(p)` (positive mass) and `B = −∑_{q ∈ Q} w_q δ(q)` (negative mass) and
suppose `B ≤ A`.  With `θ = B / A` (`mixRatio`, `θ = 0` if `A = 0`), the crossing points
`m(p, q) = (δ p − δ q)⁻¹ • (δ p • q − δ q • p)` (`segCross`) and the weights
`W(p, q) = w_p w_q (δ p − δ q) / A` (`crossWeight`),

  `∑_P w_p p + ∑_Q w_q q = ∑_P ((1 − θ) w_p) p + ∑_{P × Q} W(p, q) m(p, q)`   (`mix_vec`),
  `∑_P w_p   + ∑_Q w_q   = ∑_P (1 − θ) w_p   + ∑_{P × Q} W(p, q)`           (`mix_weights`),

all coefficients on the right are nonnegative, and in the balanced case `A = B` every
coefficient `(1 − θ) w_p` vanishes (`one_sub_mixRatio_mul_eq_zero`).  Both identities come from
one scalar identity, `mix_scalar`, applied to the coordinates and to the constant `1`.
`sum_add_sum_mem` / `sum_add_sum_add_sum_mem` assemble two or three nonnegative families with
total weight `1` into a point of a convex set.
-/

namespace MaxNN

namespace SupportCut

open BigOperators

variable {N : ℕ}

/-! ## The crossing point of a segment with the zero set of a level function -/

/-- For a level function `δ` and points `p, q`, the point
`(δ p − δ q)⁻¹ • (δ p • q − δ q • p)` of the line `pq`; when `δ` is affine and `δ p ≠ δ q`
it is the point of that line on which `δ` vanishes. -/
noncomputable def segCross (δ : (Fin N → ℝ) → ℝ) (p q : Fin N → ℝ) : Fin N → ℝ :=
  (δ p - δ q)⁻¹ • (δ p • q - δ q • p)

/-- The parameter `t = δ p / (δ p − δ q)`, so that `segCross δ p q = t • q + (1 − t) • p`
(`segCross_eq`). -/
noncomputable def crossParam (δ : (Fin N → ℝ) → ℝ) (p q : Fin N → ℝ) : ℝ :=
  δ p / (δ p - δ q)

theorem segCross_apply (δ : (Fin N → ℝ) → ℝ) (p q : Fin N → ℝ) (i : Fin N) :
    segCross δ p q i = (δ p - δ q)⁻¹ * (δ p * q i - δ q * p i) := rfl

theorem segCross_eq (δ : (Fin N → ℝ) → ℝ) {p q : Fin N → ℝ} (h : δ p - δ q ≠ 0) :
    segCross δ p q = crossParam δ p q • q + (1 - crossParam δ p q) • p := by
  funext i
  show (δ p - δ q)⁻¹ * (δ p * q i - δ q * p i) =
    δ p / (δ p - δ q) * q i + (1 - δ p / (δ p - δ q)) * p i
  rw [one_sub_div h]
  ring

/-- Exchanging the endpoints and negating the level function gives the same point. -/
theorem segCross_neg_swap (δ : (Fin N → ℝ) → ℝ) (p q : Fin N → ℝ) :
    segCross (fun y => -δ y) q p = segCross δ p q := by
  funext i
  show (-δ q - -δ p)⁻¹ * (-δ q * p i - -δ p * q i) = (δ p - δ q)⁻¹ * (δ p * q i - δ q * p i)
  rw [show -δ q - -δ p = δ p - δ q by ring]
  ring

theorem crossParam_nonneg {δ : (Fin N → ℝ) → ℝ} {p q : Fin N → ℝ} (hp : 0 < δ p)
    (hq : δ q < 0) : 0 ≤ crossParam δ p q :=
  div_nonneg hp.le (by linarith)

theorem crossParam_le_one {δ : (Fin N → ℝ) → ℝ} {p q : Fin N → ℝ} (hp : 0 < δ p)
    (hq : δ q < 0) : crossParam δ p q ≤ 1 :=
  (div_le_one (by linarith)).mpr (by linarith)

theorem dot_segCross_left (δ : (Fin N → ℝ) → ℝ) {p q : Fin N → ℝ} (h : δ p - δ q ≠ 0)
    (y : Fin N → ℝ) :
    dot (segCross δ p q) y = crossParam δ p q * dot q y + (1 - crossParam δ p q) * dot p y := by
  rw [segCross_eq δ h, dot_add_left, dot_smul_left, dot_smul_left]

theorem convexComb_le_max {t u v : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * u + (1 - t) * v ≤ max u v := by
  have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
  calc t * u + (1 - t) * v ≤ t * max u v + (1 - t) * max u v :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left u v) h0)
          (mul_le_mul_of_nonneg_left (le_max_right u v) h1')
    _ = max u v := by ring

theorem min_le_convexComb {t u v : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    min u v ≤ t * u + (1 - t) * v := by
  have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
  calc min u v = t * min u v + (1 - t) * min u v := by ring
    _ ≤ t * u + (1 - t) * v :=
        add_le_add (mul_le_mul_of_nonneg_left (min_le_left u v) h0)
          (mul_le_mul_of_nonneg_left (min_le_right u v) h1')

/-! ## Splitting sums by the sign of a level function -/

/-- `∑_S f = ∑_{δ = 0} f + (∑_{δ > 0} f + ∑_{δ < 0} f)`. -/
theorem sum_split_sign {ι M : Type*} [AddCommMonoid M] (S : Finset ι) (δ : ι → ℝ)
    (f : ι → M) :
    ∑ y in S, f y = ∑ y in S.filter (fun y => δ y = 0), f y +
      (∑ y in S.filter (fun y => 0 < δ y), f y + ∑ y in S.filter (fun y => δ y < 0), f y) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases lt_trichotomy (δ y) 0 with h | h | h
  · rw [if_neg h.ne, if_neg (not_lt.mpr h.le), if_pos h, zero_add, zero_add]
  · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h.ge), add_zero, add_zero]
  · rw [if_neg h.ne', if_pos h, if_neg (not_lt.mpr h.le), add_zero, zero_add]

/-- `∑_S f = ∑_{δ = 0} f + (∑_{δ < 0} f + ∑_{δ > 0} f)`. -/
theorem sum_split_sign' {ι M : Type*} [AddCommMonoid M] (S : Finset ι) (δ : ι → ℝ)
    (f : ι → M) :
    ∑ y in S, f y = ∑ y in S.filter (fun y => δ y = 0), f y +
      (∑ y in S.filter (fun y => δ y < 0), f y + ∑ y in S.filter (fun y => 0 < δ y), f y) := by
  rw [sum_split_sign S δ f, add_comm (∑ y in S.filter (fun y => 0 < δ y), f y)]

/-! ## The transport identity -/

/-- Expansion of the double sum of crossing contributions (pure algebra, any `A`). -/
theorem sum_sum_cross {ι : Type*} (P Q : Finset ι) (u δ g : ι → ℝ) (A : ℝ) :
    ∑ p in P, ∑ q in Q, u p * u q / A * (δ p * g q - δ q * g p) =
      (∑ p in P, u p * δ p) / A * ∑ q in Q, u q * g q -
        (∑ q in Q, u q * δ q) / A * ∑ p in P, u p * g p := by
  have h1 : ∀ p ∈ P, ∑ q in Q, u p * u q / A * (δ p * g q - δ q * g p) =
      u p * δ p / A * ∑ q in Q, u q * g q - u p * g p / A * ∑ q in Q, u q * δ q := by
    intro p _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_div, ← Finset.sum_div]
  ring

/-- The fraction `θ = (−∑_{q ∈ Q} w_q δ_q) / (∑_{p ∈ P} w_p δ_p)` of the positive mass that is
transported across (`θ = 0` when the positive mass vanishes, by `x / 0 = 0`). -/
noncomputable def mixRatio {ι : Type*} (P Q : Finset ι) (δ w : ι → ℝ) : ℝ :=
  -(∑ q in Q, w q * δ q) / ∑ p in P, w p * δ p

/-- The weight `w_p w_q (δ p − δ q) / A` given to the crossing point of `p` and `q`. -/
noncomputable def crossWeight (δ w : (Fin N → ℝ) → ℝ) (A : ℝ)
    (pq : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  w pq.1 * w pq.2 * (δ pq.1 - δ pq.2) / A

/-- **The scalar transport identity.**  For arbitrary values `g`,
`∑_P w g + ∑_Q w g = ∑_P (1 − θ) w g + ∑_{p ∈ P} ∑_{q ∈ Q} (w_p w_q / A)(δ_p g_q − δ_q g_p)`,
provided `δ < 0` and `w ≥ 0` on `Q` and `−∑_Q w δ ≤ A = ∑_P w δ`. -/
theorem mix_scalar {ι : Type*} (P Q : Finset ι) (δ w g : ι → ℝ)
    (hQ : ∀ q ∈ Q, δ q < 0) (hwQ : ∀ q ∈ Q, 0 ≤ w q)
    (hBA : -(∑ q in Q, w q * δ q) ≤ ∑ p in P, w p * δ p) :
    ∑ p in P, w p * g p + ∑ q in Q, w q * g q =
      ∑ p in P, (1 - mixRatio P Q δ w) * w p * g p +
        ∑ p in P, ∑ q in Q, w p * w q / (∑ p in P, w p * δ p) * (δ p * g q - δ q * g p) := by
  have hfac : ∑ p in P, (1 - mixRatio P Q δ w) * w p * g p =
      (1 - mixRatio P Q δ w) * ∑ p in P, w p * g p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_assoc _ _ _
  rw [hfac, sum_sum_cross P Q w δ g, mixRatio]
  by_cases hA : ∑ p in P, w p * δ p = 0
  · -- no positive mass: then there is no negative mass either, and nothing crosses
    have hle : ∑ q in Q, w q * δ q ≤ 0 :=
      Finset.sum_nonpos fun q hq => mul_nonpos_iff.mpr (Or.inl ⟨hwQ q hq, (hQ q hq).le⟩)
    have hA' : ∑ q in Q, w q * δ q = 0 := by linarith
    have hneg : ∑ q in Q, w q * -δ q = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← hA']
      exact Finset.sum_congr rfl fun q _ => by rw [mul_neg, neg_neg]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      fun q hq => mul_nonneg (hwQ q hq) (neg_nonneg.mpr (hQ q hq).le)).mp hneg
    have hQg : ∑ q in Q, w q * g q = 0 := Finset.sum_eq_zero fun q hq => by
      rw [(mul_eq_zero.mp (hterm q hq)).resolve_right (neg_ne_zero.mpr (hQ q hq).ne), zero_mul]
    rw [hA, hA', hQg]
    simp only [neg_zero, div_zero, zero_div, sub_zero, one_mul, zero_mul, mul_zero, add_zero,
      sub_self]
  · rw [div_self hA]
    ring

/-- **The vector transport identity** (coordinatewise `mix_scalar`). -/
theorem mix_vec (P Q : Finset (Fin N → ℝ)) (δ w : (Fin N → ℝ) → ℝ)
    (hP : ∀ p ∈ P, 0 < δ p) (hQ : ∀ q ∈ Q, δ q < 0) (hwQ : ∀ q ∈ Q, 0 ≤ w q)
    (hBA : -(∑ q in Q, w q * δ q) ≤ ∑ p in P, w p * δ p) :
    ∑ p in P, w p • p + ∑ q in Q, w q • q =
      ∑ p in P, ((1 - mixRatio P Q δ w) * w p) • p +
        ∑ pq in P ×ˢ Q, crossWeight δ w (∑ p in P, w p * δ p) pq • segCross δ pq.1 pq.2 := by
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_product]
  have hcross : ∀ p ∈ P, ∀ q ∈ Q,
      w p * w q / (∑ p in P, w p * δ p) * (δ p * q i - δ q * p i) =
        crossWeight δ w (∑ p in P, w p * δ p) (p, q) * segCross δ (p, q).1 (p, q).2 i := by
    intro p hp q hq
    have hD : δ p - δ q ≠ 0 := (sub_pos.mpr ((hQ q hq).trans (hP p hp))).ne'
    show w p * w q / (∑ p in P, w p * δ p) * (δ p * q i - δ q * p i) =
      w p * w q * (δ p - δ q) / (∑ p in P, w p * δ p) *
        ((δ p - δ q)⁻¹ * (δ p * q i - δ q * p i))
    rw [show w p * w q * (δ p - δ q) / (∑ p in P, w p * δ p) *
          ((δ p - δ q)⁻¹ * (δ p * q i - δ q * p i)) =
        w p * w q / (∑ p in P, w p * δ p) * (δ p * q i - δ q * p i) *
          ((δ p - δ q)⁻¹ * (δ p - δ q)) by ring,
      inv_mul_cancel hD, mul_one]
  have key : ∑ p in P, w p * p i + ∑ q in Q, w q * q i =
      ∑ p in P, (1 - mixRatio P Q δ w) * w p * p i +
        ∑ p in P, ∑ q in Q, w p * w q / (∑ p in P, w p * δ p) * (δ p * q i - δ q * p i) :=
    mix_scalar P Q δ w (fun y => y i) hQ hwQ hBA
  rw [key, add_right_inj]
  exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hcross p hp q hq

/-- **The weight transport identity** (`mix_scalar` at the constant `1`). -/
theorem mix_weights (P Q : Finset (Fin N → ℝ)) (δ w : (Fin N → ℝ) → ℝ)
    (hQ : ∀ q ∈ Q, δ q < 0) (hwQ : ∀ q ∈ Q, 0 ≤ w q)
    (hBA : -(∑ q in Q, w q * δ q) ≤ ∑ p in P, w p * δ p) :
    ∑ p in P, w p + ∑ q in Q, w q =
      ∑ p in P, (1 - mixRatio P Q δ w) * w p +
        ∑ pq in P ×ˢ Q, crossWeight δ w (∑ p in P, w p * δ p) pq := by
  have key : ∑ p in P, w p * 1 + ∑ q in Q, w q * 1 =
      ∑ p in P, (1 - mixRatio P Q δ w) * w p * 1 +
        ∑ p in P, ∑ q in Q, w p * w q / (∑ p in P, w p * δ p) * (δ p * 1 - δ q * 1) :=
    mix_scalar P Q δ w (fun _ => 1) hQ hwQ hBA
  simp only [mul_one] at key
  rw [key, Finset.sum_product, add_right_inj]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    show w p * w q / (∑ p in P, w p * δ p) * (δ p - δ q) =
      w p * w q * (δ p - δ q) / (∑ p in P, w p * δ p)
    ring

theorem one_sub_mixRatio_nonneg {ι : Type*} {P Q : Finset ι} {δ w : ι → ℝ}
    (hP : ∀ p ∈ P, 0 < δ p) (hwP : ∀ p ∈ P, 0 ≤ w p)
    (hBA : -(∑ q in Q, w q * δ q) ≤ ∑ p in P, w p * δ p) : 0 ≤ 1 - mixRatio P Q δ w := by
  show 0 ≤ 1 - -(∑ q in Q, w q * δ q) / ∑ p in P, w p * δ p
  rcases (Finset.sum_nonneg fun p hp => mul_nonneg (hwP p hp) (hP p hp).le :
      0 ≤ ∑ p in P, w p * δ p).eq_or_lt with hA | hA
  · rw [← hA, div_zero, sub_zero]
    exact zero_le_one
  · exact sub_nonneg.mpr ((div_le_one hA).mpr hBA)

/-- In the balanced case `∑_P w δ + ∑_Q w δ = 0` no positive mass stays behind. -/
theorem one_sub_mixRatio_mul_eq_zero {ι : Type*} {P Q : Finset ι} {δ w : ι → ℝ}
    (hP : ∀ p ∈ P, 0 < δ p) (hwP : ∀ p ∈ P, 0 ≤ w p)
    (hbal : ∑ p in P, w p * δ p + ∑ q in Q, w q * δ q = 0) {p : ι} (hp : p ∈ P) :
    (1 - mixRatio P Q δ w) * w p = 0 := by
  by_cases hA : ∑ x in P, w x * δ x = 0
  · have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      fun x hx => mul_nonneg (hwP x hx) (hP x hx).le).mp hA p hp
    rw [(mul_eq_zero.mp hterm).resolve_right (hP p hp).ne', mul_zero]
  · have h1 : mixRatio P Q δ w = 1 := by
      show -(∑ q in Q, w q * δ q) / ∑ x in P, w x * δ x = 1
      rw [show -(∑ q in Q, w q * δ q) = ∑ x in P, w x * δ x by linarith]
      exact div_self hA
    rw [h1, sub_self, zero_mul]

theorem crossWeight_nonneg {δ w : (Fin N → ℝ) → ℝ} {A : ℝ} (hA : 0 ≤ A) {p q : Fin N → ℝ}
    (hwp : 0 ≤ w p) (hwq : 0 ≤ w q) (hpq : δ q ≤ δ p) : 0 ≤ crossWeight δ w A (p, q) :=
  div_nonneg (mul_nonneg (mul_nonneg hwp hwq) (sub_nonneg.mpr hpq)) hA

/-! ## Assembling convex combinations from two or three families -/

/-- Two nonnegative families with total weight `1` and points in a convex set `C` combine to a
point of `C`. -/
theorem sum_add_sum_mem {C : Set (Fin N → ℝ)} (hC : Convex ℝ C) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (v : ι → ℝ) (u : κ → ℝ) (z : ι → Fin N → ℝ)
    (z' : κ → Fin N → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (hu : ∀ j ∈ t, 0 ≤ u j)
    (h1 : ∑ i in s, v i + ∑ j in t, u j = 1) (hz : ∀ i ∈ s, z i ∈ C)
    (hz' : ∀ j ∈ t, z' j ∈ C) :
    ∑ i in s, v i • z i + ∑ j in t, u j • z' j ∈ C := by
  have h0 : ∀ i ∈ s.disjSum t, 0 ≤ Sum.elim v u i := by
    rintro (i | j) hi
    · exact hv i (Finset.inl_mem_disjSum.mp hi)
    · exact hu j (Finset.inr_mem_disjSum.mp hi)
  have hsum : ∑ i in s.disjSum t, Sum.elim v u i = 1 := by
    rw [Finset.sum_disj_sum]
    exact h1
  have hmem : ∀ i ∈ s.disjSum t, Sum.elim z z' i ∈ C := by
    rintro (i | j) hi
    · exact hz i (Finset.inl_mem_disjSum.mp hi)
    · exact hz' j (Finset.inr_mem_disjSum.mp hi)
  have key := hC.sum_mem h0 hsum hmem
  rw [Finset.sum_disj_sum] at key
  exact key

/-- Three nonnegative families with total weight `1` and points in a convex set `C` combine to
a point of `C`. -/
theorem sum_add_sum_add_sum_mem {C : Set (Fin N → ℝ)} (hC : Convex ℝ C) {ι₁ ι₂ ι₃ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂) (s₃ : Finset ι₃) (v₁ : ι₁ → ℝ) (v₂ : ι₂ → ℝ)
    (v₃ : ι₃ → ℝ) (z₁ : ι₁ → Fin N → ℝ) (z₂ : ι₂ → Fin N → ℝ) (z₃ : ι₃ → Fin N → ℝ)
    (hv₁ : ∀ i ∈ s₁, 0 ≤ v₁ i) (hv₂ : ∀ i ∈ s₂, 0 ≤ v₂ i) (hv₃ : ∀ i ∈ s₃, 0 ≤ v₃ i)
    (h1 : ∑ i in s₁, v₁ i + ∑ i in s₂, v₂ i + ∑ i in s₃, v₃ i = 1)
    (hz₁ : ∀ i ∈ s₁, z₁ i ∈ C) (hz₂ : ∀ i ∈ s₂, z₂ i ∈ C) (hz₃ : ∀ i ∈ s₃, z₃ i ∈ C) :
    ∑ i in s₁, v₁ i • z₁ i + ∑ i in s₂, v₂ i • z₂ i + ∑ i in s₃, v₃ i • z₃ i ∈ C := by
  have h12 : ∀ i ∈ s₁.disjSum s₂, 0 ≤ Sum.elim v₁ v₂ i := by
    rintro (i | i) hi
    · exact hv₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact hv₂ i (Finset.inr_mem_disjSum.mp hi)
  have hz12 : ∀ i ∈ s₁.disjSum s₂, Sum.elim z₁ z₂ i ∈ C := by
    rintro (i | i) hi
    · exact hz₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact hz₂ i (Finset.inr_mem_disjSum.mp hi)
  have hsum : ∑ i in s₁.disjSum s₂, Sum.elim v₁ v₂ i + ∑ i in s₃, v₃ i = 1 := by
    rw [Finset.sum_disj_sum]
    exact h1
  have key := sum_add_sum_mem hC (s₁.disjSum s₂) s₃ (Sum.elim v₁ v₂) v₃ (Sum.elim z₁ z₂) z₃
    h12 hv₃ hsum hz12 hz₃
  rw [Finset.sum_disj_sum] at key
  exact key

end SupportCut

end MaxNN
