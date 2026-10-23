import MaxCaterpillar.Frontier.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

/-! # Behaviour along the diagonal (Lemma T) and the spanning lemma (Lemma S)

Along `x + t·1` with `t → +∞`, a first-layer row `a` with coordinate sum `s > 0` becomes
the affine function `a·x + s t`, a row with `s < 0` becomes `0`, and a translation-invariant
row (`s = 0`) does not change. The same holds one layer up. Comparing with
`max(x + t·1) = max x + t` gives the slope identity `ZNet.slope = 1` and the identity
`max = ZNet.rest` (`ZNet.max_plus`). The side `t → -∞` is the side `+∞` of `ZNet.negIn`.

Lemma S: the rows with `s ≥ 0` have no common nonzero kernel vector, hence there are at
least `N` of them; likewise for `s ≤ 0`. There is at least one row with `s > 0` and at
least one with `s < 0`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators Filter Topology

variable {N h₁ h₂ : ℕ}

/-- The case selector: `u` if `s > 0`, `0` if `s < 0`, `v` if `s = 0`. -/
noncomputable def pick (s u v : ℝ) : ℝ := if 0 < s then u else if s < 0 then 0 else v

lemma eventually_relu (a s : ℝ) :
    ∀ᶠ t in atTop, relu (a + t * s) = pick s (a + t * s) (relu a) := by
  unfold pick
  rcases lt_trichotomy s 0 with hs | hs | hs
  · filter_upwards [eventually_ge_atTop (a / -s)] with t ht
    rw [if_neg (by linarith), if_pos hs]
    apply relu_of_nonpos
    have := (div_le_iff (neg_pos.2 hs)).1 ht
    linarith
  · subst hs; simp
  · filter_upwards [eventually_ge_atTop (-a / s)] with t ht
    rw [if_pos hs]
    apply relu_of_nonneg
    have := (div_le_iff hs).1 ht
    linarith

lemma affine_eq_of_eventually {α β γ δ : ℝ} (h : ∀ᶠ t in atTop, t * α + β = t * γ + δ) :
    α = γ ∧ β = δ := by
  obtain ⟨t0, ht⟩ := Filter.eventually_atTop.1 h
  have e1 := ht t0 le_rfl
  have e2 := ht (t0 + 1) (by linarith)
  have hα : α = γ := by linear_combination e2 - e1
  exact ⟨hα, by linear_combination e1 - t0 * hα⟩

/-- Coordinate sum `sⱼ = Aⱼ·1` of a first-layer row. -/
def ZNet.s (net : ZNet N h₁ h₂) (j : Fin h₁) : ℝ := ∑ i, net.A j i

lemma ZNet.lin_add_diag (net : ZNet N h₁ h₂) (j : Fin h₁) (x : Point N) (t : ℝ) :
    lin (net.A j) (x + diag t) = lin (net.A j) x + t * net.s j := by
  rw [lin_add_right, lin_diag]; rfl

/-- `T⁺ₖ`: the slope of the `k`-th second-layer input along `x + t·1`, `t → +∞`. -/
noncomputable def ZNet.Tp (net : ZNet N h₁ h₂) (k : Fin h₂) : ℝ :=
  ∑ j, net.W k j * pick (net.s j) (net.s j) 0

/-- `G⁺ₖ(x)`: the intercept, `Σ_{J+} Wₖⱼ Aⱼ·x + Σ_{J0} Wₖⱼ σ(Aⱼ·x)`. -/
noncomputable def ZNet.Gp (net : ZNet N h₁ h₂) (k : Fin h₂) (x : Point N) : ℝ :=
  ∑ j, net.W k j * pick (net.s j) (lin (net.A j) x) (relu (lin (net.A j) x))

/-- `Σ_{P+} dₖ T⁺ₖ`. -/
noncomputable def ZNet.slope (net : ZNet N h₁ h₂) : ℝ :=
  ∑ k, net.d k * pick (net.Tp k) (net.Tp k) 0

/-- `Σ_{P+} dₖ G⁺ₖ + Σ_{Z+} dₖ σ(G⁺ₖ)`. -/
noncomputable def ZNet.rest (net : ZNet N h₁ h₂) (x : Point N) : ℝ :=
  ∑ k, net.d k * pick (net.Tp k) (net.Gp k x) (relu (net.Gp k x))

lemma ZNet.eventually_eval (net : ZNet N h₁ h₂) (x : Point N) :
    ∀ᶠ t in atTop, net.eval (x + diag t) = t * net.slope + net.rest x := by
  have h1 : ∀ᶠ t in atTop, ∀ j, relu (lin (net.A j) (x + diag t)) =
      pick (net.s j) (lin (net.A j) x + t * net.s j) (relu (lin (net.A j) x)) :=
    Filter.eventually_all.2 fun j => (eventually_relu _ _).mono fun t ht => by
      rw [net.lin_add_diag]; exact ht
  have h2 : ∀ᶠ t in atTop, ∀ k, relu (net.Gp k x + t * net.Tp k) =
      pick (net.Tp k) (net.Gp k x + t * net.Tp k) (relu (net.Gp k x)) :=
    Filter.eventually_all.2 fun k => eventually_relu _ _
  filter_upwards [h1, h2] with t ht1 ht2
  have hk : ∀ k, ∑ j, net.W k j * relu (lin (net.A j) (x + diag t)) =
      net.Gp k x + t * net.Tp k := by
    intro k
    simp only [ht1, ZNet.Gp, ZNet.Tp, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold pick; split_ifs <;> ring
  unfold ZNet.eval
  simp only [hk, ht2, ZNet.slope, ZNet.rest, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold pick; split_ifs <;> ring

/-- **Lemma T** for a target `f` with `f (x + t·1) = f x + κ t`. -/
theorem ZNet.asymp (net : ZNet N h₁ h₂) (f : Point N → ℝ) (κ : ℝ)
    (hf : ∀ x, net.eval x = f x) (hκ : ∀ x t, f (x + diag t) = f x + κ * t) :
    net.slope = κ ∧ ∀ x, f x = net.rest x := by
  have key : ∀ x, net.slope = κ ∧ net.rest x = f x := fun x =>
    affine_eq_of_eventually ((net.eventually_eval x).mono fun t ht => by
      rw [← ht, hf, hκ]; ring)
  exact ⟨(key 0).1, fun x => (key x).2.symm⟩

lemma neg_add_diag (y : Point N) (t : ℝ) : -(y + diag t) = -y + diag (-t) := by
  funext i; simp [diag]; ring

/-- `(+∞)`: `Σ_{P+} dₖ T⁺ₖ = 1` and `max = Σ_{P+} dₖ G⁺ₖ + Σ_{Z+} dₖ σ(G⁺ₖ)`. -/
theorem ZNet.max_plus [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    net.slope = 1 ∧ ∀ x, Maximum N x = net.rest x :=
  net.asymp _ 1 h (fun x t => by rw [Maximum_add_diag]; ring)

/-- `(-∞)`, as the `(+∞)` statement for the network with negated first-layer rows. -/
theorem ZNet.max_minus [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    net.negIn.slope = -1 ∧ ∀ x, Maximum N x = net.negIn.rest (-x) := by
  obtain ⟨h1, h2⟩ := net.negIn.asymp (fun y => Maximum N (-y)) (-1)
    (fun y => by rw [net.negIn_eval, h]) (fun y t => by
      show Maximum N (-(y + diag t)) = Maximum N (-y) + -1 * t
      rw [neg_add_diag, Maximum_add_diag]; ring)
  exact ⟨h1, fun x => by rw [← h2, neg_neg]⟩

lemma ZNet.negIn_s (net : ZNet N h₁ h₂) (j : Fin h₁) : net.negIn.s j = -net.s j := by
  simp [ZNet.s, ZNet.negIn, Finset.sum_neg_distrib]

/-! ## Lemma S -/

lemma ZNet.eq_of_ker (net : ZNet N h₁ h₂) (f : Point N → ℝ) (κ : ℝ)
    (hf : ∀ x, net.eval x = f x) (hκ : ∀ x t, f (x + diag t) = f x + κ * t) (w : Point N)
    (hw : ∀ j, 0 ≤ net.s j → lin (net.A j) w = 0) : f w = f 0 := by
  have ev : ∀ᶠ t in atTop, ∀ j, relu (lin (net.A j) (w + diag t)) =
      relu (lin (net.A j) (0 + diag t)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hs : 0 ≤ net.s j
    · exact Filter.eventually_of_forall fun t => by
        rw [net.lin_add_diag, net.lin_add_diag, hw j hs, lin_zero_right]
    · filter_upwards [eventually_relu (lin (net.A j) w) (net.s j),
        eventually_relu 0 (net.s j)] with t h1 h2
      rw [net.lin_add_diag, net.lin_add_diag, lin_zero_right, h1, h2]
      unfold pick
      have hs' : ¬ 0 < net.s j := fun h => hs h.le
      rw [if_neg hs', if_pos (lt_of_not_le hs), if_neg hs', if_pos (lt_of_not_le hs)]
  obtain ⟨t, ht⟩ := ev.exists
  have : net.eval (w + diag t) = net.eval (0 + diag t) := by
    unfold ZNet.eval; simp only [ht]
  rw [hf, hf, hκ, hκ] at this
  linarith

lemma eq_zero_of_Maximum [NeZero N] (w : Point N) (h1 : Maximum N w ≤ 0)
    (h2 : Maximum N (-w) ≤ 0) : w = 0 := by
  funext i
  have a := (Maximum_le_iff _ _).1 h1 i
  have b := (Maximum_le_iff _ _).1 h2 i
  simp only [Pi.neg_apply] at b
  simp only [Pi.zero_apply]; linarith

/-- **Lemma S (+)**: the rows with `s ≥ 0` have trivial common kernel. -/
theorem ZNet.ker_plus [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (w : Point N) (hw : ∀ j, 0 ≤ net.s j → lin (net.A j) w = 0) : w = 0 := by
  have hκ : ∀ x t, Maximum N (x + diag t) = Maximum N x + 1 * t := fun x t => by
    rw [Maximum_add_diag]; ring
  have e1 := net.eq_of_ker _ 1 h hκ w hw
  have e2 := net.eq_of_ker _ 1 h hκ (-w) (fun j hj => by rw [lin_neg_right, hw j hj, neg_zero])
  rw [Maximum_zero] at e1 e2
  exact eq_zero_of_Maximum w e1.le e2.le

/-- **Lemma S (−)**: the rows with `s ≤ 0` have trivial common kernel. -/
theorem ZNet.ker_minus [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (w : Point N) (hw : ∀ j, net.s j ≤ 0 → lin (net.A j) w = 0) : w = 0 := by
  have hf : ∀ y, net.negIn.eval y = Maximum N (-y) := fun y => by rw [net.negIn_eval, h]
  have hκ : ∀ y t, Maximum N (-(y + diag t)) = Maximum N (-y) + (-1) * t := fun y t => by
    rw [neg_add_diag, Maximum_add_diag]; ring
  have hw' : ∀ v : Point N, (∀ j, net.s j ≤ 0 → lin (net.A j) v = 0) →
      ∀ j, 0 ≤ net.negIn.s j → lin (net.negIn.A j) v = 0 := by
    intro v hv j hj
    rw [net.negIn_s, neg_nonneg] at hj
    simp only [ZNet.negIn, lin_neg_left, hv j hj, neg_zero]
  have e1 := net.negIn.eq_of_ker _ (-1) hf hκ w (hw' w hw)
  have e2 := net.negIn.eq_of_ker _ (-1) hf hκ (-w) (hw' (-w) (fun j hj => by
    rw [lin_neg_right, hw j hj, neg_zero]))
  rw [neg_zero, Maximum_zero] at e1 e2
  rw [neg_neg] at e2
  exact eq_zero_of_Maximum w e2.le e1.le

/-- The linear map `x ↦ (Aⱼ·x)_{j ∈ S}`. -/
def ZNet.rowMap (net : ZNet N h₁ h₂) (S : Finset (Fin h₁)) : Point N →ₗ[ℝ] (S → ℝ) where
  toFun w j := lin (net.A j) w
  map_add' x y := by funext j; simp [lin_add_right]
  map_smul' a x := by funext j; simp [lin_smul_right]

lemma ZNet.rowMap_injective_iff (net : ZNet N h₁ h₂) (S : Finset (Fin h₁)) :
    Function.Injective (net.rowMap S) ↔ ∀ w, (∀ j ∈ S, lin (net.A j) w = 0) → w = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro H w hw
    exact H w (funext fun j => hw j j.2)
  · intro H w hw
    exact H w (fun j hj => congr_fun hw ⟨j, hj⟩)

lemma ZNet.card_ge_of_injective (net : ZNet N h₁ h₂) (S : Finset (Fin h₁))
    (hinj : Function.Injective (net.rowMap S)) : N ≤ S.card := by
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [FiniteDimensional.finrank_fin_fun, FiniteDimensional.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at this

/-- `J+ ∪ J0` has at least `N` rows. -/
theorem ZNet.card_nonneg [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    N ≤ (Finset.univ.filter fun j => 0 ≤ net.s j).card :=
  net.card_ge_of_injective _ ((net.rowMap_injective_iff _).2 fun w hw =>
    net.ker_plus h w fun j hj => hw j (by simp [hj]))

/-- `J- ∪ J0` has at least `N` rows. -/
theorem ZNet.card_nonpos [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    N ≤ (Finset.univ.filter fun j => net.s j ≤ 0).card :=
  net.card_ge_of_injective _ ((net.rowMap_injective_iff _).2 fun w hw =>
    net.ker_minus h w fun j hj => hw j (by simp [hj]))

/-- `J-` is nonempty. -/
theorem ZNet.exists_neg [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    ∃ j, net.s j < 0 := by
  by_contra hc
  push_neg at hc
  have : net.eval (diag (-1)) = net.eval 0 := by
    unfold ZNet.eval
    congr 1; funext k; congr 2; congr 1; funext j
    rw [lin_diag, lin_zero_right, relu_of_nonpos (by have := hc j; unfold ZNet.s at this; linarith), relu_of_nonpos le_rfl]
  rw [h, h, Maximum_diag, Maximum_zero] at this
  norm_num at this

/-- `J+` is nonempty. -/
theorem ZNet.exists_pos [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    ∃ j, 0 < net.s j := by
  by_contra hc
  push_neg at hc
  have : net.eval (diag 1) = net.eval 0 := by
    unfold ZNet.eval
    congr 1; funext k; congr 2; congr 1; funext j
    rw [lin_diag, lin_zero_right, relu_of_nonpos (by have := hc j; unfold ZNet.s at this; linarith), relu_of_nonpos le_rfl]
  rw [h, h, Maximum_diag, Maximum_zero] at this
  norm_num at this

end Frontier
end MaxCaterpillar
