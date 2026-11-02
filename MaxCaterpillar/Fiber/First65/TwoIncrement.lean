import MaxCaterpillar.Frontier.Asymptotics

/-! # Recovering the anchor difference from two independent increments

This is a finite, exact algebraic consequence of representing
`max (a+q) (b+r)` for every nonnegative pair `q,r`. It permits arbitrary
real coefficients, zero slopes and unused summands.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

open BigOperators Filter Topology Frontier

variable {m : ℕ}

/-- The eventual affine expression of a finite weighted ReLU sum. -/
lemma eventually_weighted_relu (d C s : Fin m → ℝ) :
    ∀ᶠ t in atTop,
      (∑ k, d k * relu (C k + t * s k)) =
        t * (∑ k, d k * pick (s k) (s k) 0) +
          ∑ k, d k * pick (s k) (C k) (relu (C k)) := by
  have hrows : ∀ᶠ t in atTop, ∀ k : Fin m,
      relu (C k + t * s k) = pick (s k) (C k + t * s k) (relu (C k)) :=
    Filter.eventually_all.2 fun k => eventually_relu (C k) (s k)
  filter_upwards [hrows] with t ht
  simp only [ht, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold pick
  split_ifs <;> ring

/-- The eventual affine expression of a finite sum with fixed outer gate
states and a second scalar direction. -/
lemma eventually_weighted_pick (d s C α : Fin m → ℝ) :
    ∀ᶠ t in atTop,
      (∑ k, d k * pick (s k) (C k + t * α k) (relu (C k + t * α k))) =
        t * (∑ k, d k * pick (s k) (α k) (pick (α k) (α k) 0)) +
          ∑ k, d k * pick (s k) (C k) (pick (α k) (C k) (relu (C k))) := by
  have hrows : ∀ᶠ t in atTop, ∀ k : Fin m,
      relu (C k + t * α k) = pick (α k) (C k + t * α k) (relu (C k)) :=
    Filter.eventually_all.2 fun k => eventually_relu (C k) (α k)
  filter_upwards [hrows] with t ht
  simp only [ht, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold pick
  split_ifs <;> ring

/-- After a common large increment, only the zero-common-slope gates
remain nonlinear in the difference variable. -/
theorem two_increment_recession (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a + q) (b + r) = ∑ k, d k * relu (C k + α k * q + β k * r)) :
    ∀ z : ℝ, max (a + z) b =
      ∑ k, d k * pick (α k + β k) (C k + z * α k) (relu (C k + z * α k)) := by
  intro z
  have ht := eventually_weighted_relu d (fun k => C k + z * α k) (fun k => α k + β k)
  have he : ∀ᶠ t in atTop,
      t * 1 + max (a + z) b =
        t * (∑ k, d k * pick (α k + β k) (α k + β k) 0) +
          ∑ k, d k * pick (α k + β k) (C k + z * α k) (relu (C k + z * α k)) := by
    filter_upwards [ht, eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (-z)]
      with t htail ht0 htz
    have hinput := h (t + z) t (by linarith) ht0
    have hleft : max (a + (t + z)) (b + t) = t * 1 + max (a + z) b := by
      rw [show a + (t + z) = (a + z) + t by ring, max_add_add_right]
      ring
    have hright : (∑ k, d k * relu (C k + α k * (t + z) + β k * t)) =
        ∑ k, d k * relu ((C k + z * α k) + t * (α k + β k)) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      ring
    rw [hleft, hright, htail] at hinput
    exact hinput
  exact (affine_eq_of_eventually he).2

/-- Any exact two-increment max representation linearly recovers `a-b`
from the intercepts of the gates with zero common slope. -/
theorem two_increment_intercept_difference (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a + q) (b + r) = ∑ k, d k * relu (C k + α k * q + β k * r)) :
    a - b = ∑ k, if α k + β k = 0 then
      d k * (if 0 < α k then C k else if α k < 0 then -C k else 0) else 0 := by
  have hr := two_increment_recession a b d C α β h
  have hp : a = ∑ k, d k * pick (α k + β k) (C k)
      (pick (α k) (C k) (relu (C k))) := by
    have he : ∀ᶠ t in atTop,
        t * 1 + a = t * (∑ k, d k * pick (α k + β k) (α k) (pick (α k) (α k) 0)) +
          ∑ k, d k * pick (α k + β k) (C k) (pick (α k) (C k) (relu (C k))) := by
      filter_upwards [eventually_weighted_pick d (fun k => α k + β k) C α,
        eventually_ge_atTop (b - a)] with t ht htab
      calc
        t * 1 + a = max (a + t) b := by rw [max_eq_left (by linarith)]; ring
        _ = _ := hr t
        _ = _ := ht
    exact (affine_eq_of_eventually he).2
  have hm : b = ∑ k, d k * pick (α k + β k) (C k)
      (pick (-α k) (C k) (relu (C k))) := by
    have he : ∀ᶠ t in atTop,
        t * 0 + b =
          t * (∑ k, d k * pick (α k + β k) (-α k) (pick (-α k) (-α k) 0)) +
            ∑ k, d k * pick (α k + β k) (C k) (pick (-α k) (C k) (relu (C k))) := by
      filter_upwards [eventually_weighted_pick d (fun k => α k + β k) C (fun k => -α k),
        eventually_ge_atTop (a - b)] with t ht htab
      have hr' := hr (-t)
      simp only [neg_mul, mul_neg] at hr' ht
      calc
        t * 0 + b = max (a + -t) b := by rw [max_eq_right (by linarith)]; ring
        _ = _ := hr'
        _ = _ := ht
    exact (affine_eq_of_eventually he).2
  rw [hp, hm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases lt_trichotomy (α k + β k) 0 with hs | hs | hs
  · simp [pick, hs, not_lt.2 hs.le, hs.ne]
  · rw [if_pos hs]
    simp only [pick, hs, lt_irrefl, if_false]
    rcases lt_trichotomy (α k) 0 with hα | hα | hα
    · simp [hα, not_lt.2 hα.le, neg_pos.2 hα]
    · simp [hα]
    · simp [hα, not_lt.2 hα.le, neg_neg_of_pos hα]
  · simp [pick, hs, hs.ne']

/-- When the intercepts are linear combinations of fixed features, the same
fixed feature span contains the anchor difference. The coefficients are
independent of the feature argument. -/
theorem two_increment_feature_span {p : ℕ} {X : Type*}
    (a b : X → ℝ) (features : Fin p → X → ℝ)
    (d α β : Fin m → ℝ) (W : Fin m → Fin p → ℝ)
    (h : ∀ x : X, ∀ q r : ℝ, 0 ≤ q → 0 ≤ r →
      max (a x + q) (b x + r) =
        ∑ k, d k * relu ((∑ j, W k j * features j x) + α k * q + β k * r)) :
    ∃ c : Fin p → ℝ, ∀ x, a x - b x = ∑ j, c j * features j x := by
  let η : Fin m → ℝ := fun k => if α k + β k = 0 then
    d k * (if 0 < α k then 1 else if α k < 0 then -1 else 0) else 0
  refine ⟨fun j => ∑ k, η k * W k j, fun x => ?_⟩
  have hx := two_increment_intercept_difference (a x) (b x) d
    (fun k => ∑ j, W k j * features j x) α β (h x)
  calc
    a x - b x = ∑ k, η k * (∑ j, W k j * features j x) := by
      rw [hx]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [η]
      split_ifs <;> ring
    _ = ∑ k, ∑ j, (η k * W k j) * features j x := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ j, (∑ k, η k * W k j) * features j x := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

end Fiber
end MaxCaterpillar
