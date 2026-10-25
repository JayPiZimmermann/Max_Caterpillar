import MaxCaterpillar.Frontier.SecondWidthPlus

/-!
Exact analytic restriction for the second-width-four search.
Independent shifts eliminate all outer folds on their common kernel.
This does not assert a network width bound.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.WidthTradeoff
open Filter Topology BigOperators

lemma slope_zero_of_local_nonneg (c : ℝ)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * c) : c = 0 := by
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ (-t) * c := by
    have ht : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using continuous_neg.continuousAt.tendsto (x := (0 : ℝ))
    exact ht.eventually h
  have hr : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ t*c ∧ 0 ≤ (-t)*c :=
    (h.and hn).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 ≤ t*c ∧ 0 ≤ (-t)*c) ∧ 0 < t :=
    hr.and self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, hnt⟩, hp⟩ := hall.exists
  nlinarith

lemma slope_at_positive (w : ℝ → ℝ) (hw : ContinuousAt w 0)
    (h0 : 0 < w 0) (c s : ℝ)
    (h : ∀ t, 0 ≤ t * c + s * (relu (w t + t) - relu (w t))) : c = -s := by
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w t := hw.eventually (lt_mem_nhds h0)
  have hw' : ContinuousAt (fun t => w t + t) 0 := hw.add continuousAt_id
  have hp' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w t + t :=
    hw'.eventually (lt_mem_nhds (by simpa using h0))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * (c + s) := by
    filter_upwards [hp, hp'] with t ht ht'
    have h1 := h t
    rw [relu_of_nonneg ht'.le, relu_of_nonneg ht.le] at h1
    nlinarith
  have hz := slope_zero_of_local_nonneg (c+s) he
  linarith

lemma slope_at_negative (w : ℝ → ℝ) (hw : ContinuousAt w 0)
    (h0 : w 0 < 0) (c s : ℝ)
    (h : ∀ t, 0 ≤ t * c + s * (relu (w t + t) - relu (w t))) : c = 0 := by
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), w t < 0 := hw.eventually (gt_mem_nhds h0)
  have hw' : ContinuousAt (fun t => w t + t) 0 := hw.add continuousAt_id
  have hp' : ∀ᶠ t in 𝓝 (0 : ℝ), w t + t < 0 :=
    hw'.eventually (gt_mem_nhds (by simpa using h0))
  apply slope_zero_of_local_nonneg c
  filter_upwards [hp, hp'] with t ht ht'
  have h1 := h t
  simpa only [relu_of_nonpos ht'.le, relu_of_nonpos ht.le, sub_self,
    mul_zero, add_zero] using h1


variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear remainder of a globally nonnegative ReLU difference sum
vanishes on the common kernel of its shifts. -/
theorem linear_zero_on_shift_kernel
    (w : ι → Point N → ℝ) (L : Point N) (delta : ι → Point N) (s : ι → ℝ)
    (h : ∀ x, 0 ≤ lin L x +
      ∑ i, s i * (relu (w i x + lin (delta i) x) - relu (w i x)))
    (x : Point N) (hx : ∀ i, lin (delta i) x = 0) : lin L x = 0 := by
  have hp := h x
  have hn := h (-x)
  simp only [hx, add_zero, sub_self, mul_zero, Finset.sum_const_zero] at hp
  simp only [lin_neg_right, hx, neg_zero, add_zero, sub_self,
    mul_zero, Finset.sum_const_zero] at hn
  linarith

/-- If one shift can be varied independently of every other shift, its
continuous preactivation has a single weak sign throughout their common
kernel. The coefficient may have either nonzero sign. -/
theorem transverse_sign_family
    (w : ι → Point N → ℝ) (L : Point N) (delta : ι → Point N) (s : ι → ℝ)
    (h : ∀ x, 0 ≤ lin L x +
      ∑ j, s j * (relu (w j x + lin (delta j) x) - relu (w j x)))
    (i : ι) (hwi : Continuous (w i)) (hsi : s i ≠ 0)
    (y : Point N) (hy : ∀ j, lin (delta j) y = if j = i then 1 else 0) :
    (∀ x, (∀ j, lin (delta j) x = 0) → 0 ≤ w i x) ∨
    (∀ x, (∀ j, lin (delta j) x = 0) → w i x ≤ 0) := by
  classical
  have key (z : Point N) (hz : ∀ j, lin (delta j) z = 0) :
      ∀ t, 0 ≤ t * lin L y + s i *
        (relu (w i (z + t • y) + t) - relu (w i (z + t • y))) := by
    intro t
    have hL := linear_zero_on_shift_kernel w L delta s h z hz
    have hall := h (z + t • y)
    have hd (j : ι) : lin (delta j) (z + t • y) = if j = i then t else 0 := by
      rw [lin_add_right, lin_smul_right, hz, hy]
      split_ifs <;> ring
    rw [lin_add_right, lin_smul_right, hL, zero_add] at hall
    have hs : (∑ j, s j * (relu (w j (z + t • y) +
        lin (delta j) (z + t • y)) - relu (w j (z + t • y)))) =
        s i * (relu (w i (z + t • y) + t) - relu (w i (z + t • y))) := by
      rw [Finset.sum_eq_single i]
      · rw [hd i, if_pos rfl]
      · intro j _ hji
        rw [hd j, if_neg hji, add_zero, sub_self, mul_zero]
      · simp
    rwa [hs] at hall
  have hc (z : Point N) : ContinuousAt (fun t : ℝ => w i (z + t • y)) 0 :=
    (hwi.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
  by_cases hp : ∃ z, (∀ j, lin (delta j) z = 0) ∧ 0 < w i z
  · obtain ⟨z, hz, hzp⟩ := hp
    have hplus : lin L y = -s i := slope_at_positive (fun t => w i (z + t • y))
      (hc z) (by simpa using hzp) _ _ (key z hz)
    left
    intro x hx
    by_contra hxn
    have hxneg : w i x < 0 := lt_of_not_ge hxn
    have hminus : lin L y = 0 := slope_at_negative (fun t => w i (x + t • y))
      (hc x) (by simpa using hxneg) _ _ (key x hx)
    exact hsi (by linarith)
  · right
    intro x hx
    exact le_of_not_gt fun hxpos => hp ⟨x, hx, hxpos⟩

/-- With independent shifts, every fold restricts to either its argument or
zero. Thus all folds disappear simultaneously on the common kernel. -/
theorem transverse_folds_linearize
    (w : ι → Point N → ℝ) (hw : ∀ i, Continuous (w i))
    (L : Point N) (delta : ι → Point N) (s : ι → ℝ) (hs : ∀ i, s i ≠ 0)
    (h : ∀ x, 0 ≤ lin L x +
      ∑ j, s j * (relu (w j x + lin (delta j) x) - relu (w j x)))
    (y : ι → Point N)
    (hy : ∀ i j, lin (delta j) (y i) = if j = i then 1 else 0) :
    ∃ c : ι → ℝ, (∀ i, c i = 0 ∨ c i = s i) ∧
      ∀ x, (∀ j, lin (delta j) x = 0) →
        (∑ i, s i * relu (w i x)) = ∑ i, c i * w i x := by
  classical
  have hsign (i : ι) := transverse_sign_family w L delta s h i (hw i) (hs i) (y i) (hy i)
  let c : ι → ℝ := fun i => if ∀ x, (∀ j, lin (delta j) x = 0) → 0 ≤ w i x
    then s i else 0
  refine ⟨c, ?_, ?_⟩
  · intro i
    dsimp [c]
    split_ifs <;> simp
  · intro x hx
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [c]
    split_ifs with hi
    · rw [relu_of_nonneg (hi x hx)]
    · have hi' : ∀ x, (∀ j, lin (delta j) x = 0) → w i x ≤ 0 :=
        (hsign i).resolve_left hi
      rw [relu_of_nonpos (hi' x hx), mul_zero, zero_mul]


/-- The normalized positive and negative translation identities imply that
the represented function has a linear odd part on the common shift kernel.
This is a necessary restriction, not an exclusion of a width-four network. -/
theorem normalized_tails_kernel_odd
    (f u v : Point N → ℝ) (w : ι → Point N → ℝ)
    (hu : OddLin u) (hv : OddLin v) (hw : ∀ i, OddLin (w i))
    (hwc : ∀ i, Continuous (w i)) (alpha beta : Point N)
    (delta : ι → Point N) (s : ι → ℝ) (hs : ∀ i, s i ≠ 0)
    (hplus : ∀ x, f x = u x + lin alpha x - relu (v x) +
      ∑ i, s i * relu (w i x + lin (delta i) x))
    (hminus : ∀ x, f x = -v x - lin beta x + relu (u x) +
      ∑ i, s i * relu (w i x))
    (y : ι → Point N)
    (hy : ∀ i j, lin (delta j) (y i) = if j = i then 1 else 0) :
    ∃ c : Point N, ∀ x, (∀ j, lin (delta j) x = 0) →
      f x - f (-x) = lin c x := by
  classical
  let L := alpha + beta
  have hkey (x : Point N) : relu (-u x) + relu (-v x) = lin L x +
      ∑ i, s i * (relu (w i x + lin (delta i) x) - relu (w i x)) := by
    have hp := hplus x
    have hm := hminus x
    have he1 := relu_sub_relu_neg (u x)
    have he2 := relu_sub_relu_neg (v x)
    dsimp [L]
    rw [lin_add_left]
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hpos (x : Point N) : 0 ≤ lin L x +
      ∑ i, s i * (relu (w i x + lin (delta i) x) - relu (w i x)) := by
    rw [← hkey x]
    exact add_nonneg (relu_nonneg _) (relu_nonneg _)
  obtain ⟨a, -, ha⟩ := transverse_folds_linearize w hwc L delta s hs hpos y hy
  have hvker (x : Point N) (hx : ∀ j, lin (delta j) x = 0) : 0 ≤ v x := by
    have hL := linear_zero_on_shift_kernel w L delta s hpos x hx
    have he := hkey x
    simp only [hx, add_zero, sub_self, mul_zero, Finset.sum_const_zero, hL] at he
    have hn := relu_nonneg (-u x)
    have hv' : -v x ≤ relu (-v x) := le_max_right _ _
    linarith
  let b : Point N → ℝ := fun x => u x + lin alpha x - v x + ∑ i, a i * w i x
  have hb : OddLin b :=
    (((hu.add (oddLin_lin alpha)).add (hv.const_mul (-1))).add
      (OddLin.sum _ fun i _ => (hw i).const_mul (a i))).congr fun x => by
        dsimp [b]; ring
  obtain ⟨c, hc⟩ := hb
  have hrep (x : Point N) (hx : ∀ j, lin (delta j) x = 0) : f x = b x := by
    rw [hplus x, relu_of_nonneg (hvker x hx)]
    simp only [hx, add_zero]
    rw [ha x hx]
  refine ⟨c, fun x hx => ?_⟩
  have hnx : ∀ j, lin (delta j) (-x) = 0 := by
    intro j
    rw [lin_neg_right, hx, neg_zero]
  rw [hrep x hx, hrep (-x) hnx]
  exact hc x


/-- Without independent shifts the positivity hypothesis does not force signs:
two equal ReLU differences with opposite coefficients cancel identically. -/
theorem dependent_shift_cancellation (x : Point 2) :
    0 ≤ (relu (x 1 + x 0) - relu (x 1)) -
      (relu (x 1 + x 0) - relu (x 1)) := by
  simp

/-- The common preactivation in the preceding exact counterexample has both
signs on the common shift kernel. -/
theorem dependent_shift_sign_failure :
    ¬ ((∀ x : Point 2, x 0 = 0 → 0 ≤ x 1) ∨
      (∀ x : Point 2, x 0 = 0 → x 1 ≤ 0)) := by
  rintro (hp | hn)
  · have he := hp ![0, -1] (by simp)
    norm_num at he
  · have he := hn ![0, 1] (by simp)
    norm_num at he

#print axioms dependent_shift_sign_failure

#check @normalized_tails_kernel_odd
#print axioms normalized_tails_kernel_odd

#check @transverse_sign_family
#print axioms transverse_sign_family
#check @transverse_folds_linearize
#print axioms transverse_folds_linearize

end MaxCaterpillar.Frontier.WidthTradeoff
