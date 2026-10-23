import MaxCaterpillar.Frontier.Asymptotics

/-! # The claw lemma (Lemma C4) for every `N`

Let `I` be a set of coordinates, `a ∈ I`, `|I \ {a}| ≥ 3`, and let `q` vanish on `I` and be
`≤ -1` off `I`. If a bias-free network computes the maximum, then some translation-invariant
first-layer row `Aⱼ` (`sⱼ = 0`) has `Aⱼ·q = 0` and `Aⱼ(a) ≠ 0` (`ZNet.claw`).

Proof. Suppose not. Use the identity `max = rest` of `ZNet.max_plus` and put
`H(x) = rest(x + δeₐ) - rest(x - δeₐ)` for a small `δ > 0`. Near `q`, every row with `Aⱼ·q ≠ 0`
is affine, and every translation-invariant row with `Aⱼ·q = 0` does not see the shift `±δeₐ`.
A case check on each second-layer neuron (`key_real`) shows that
`H(q + εv) - H(q - εv) = ε·C·v` for a fixed covector `C` (`ZNet.claw_net`). On the maximum side,
`H(q + εv) = δ + εvₐ - ε max_{I \ {a}} v` for small `ε`, and this has no linear odd part when
`|I \ {a}| ≥ 3` (`max_claw_false`).
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators Filter Topology

variable {N h₁ h₂ : ℕ}

/-! ## Expansion of the rows near `q` -/

/-- The gradient of the row term `pick(sⱼ, Aⱼ·x, σ(Aⱼ·x))` near `q` (rows with `Aⱼ·q ≠ 0`). -/
noncomputable def ZNet.gam (net : ZNet N h₁ h₂) (q : Point N) (j : Fin h₁) : Point N :=
  if 0 < net.s j then net.A j else if net.s j < 0 then 0 else
    if 0 < lin (net.A j) q then net.A j else 0

/-- The part of a translation-invariant row with `Aⱼ·q = 0`: `σ(Aⱼ·z)`. -/
noncomputable def ZNet.rr (net : ZNet N h₁ h₂) (q : Point N) (j : Fin h₁) (z : Point N) : ℝ :=
  if net.s j = 0 ∧ lin (net.A j) q = 0 then relu (lin (net.A j) z) else 0

/-- The odd part of `rr`. -/
noncomputable def ZNet.rv (net : ZNet N h₁ h₂) (q : Point N) (j : Fin h₁) : Point N :=
  if net.s j = 0 ∧ lin (net.A j) q = 0 then net.A j else 0

lemma ZNet.row_expand (net : ZNet N h₁ h₂) (q z : Point N) (j : Fin h₁)
    (hz : net.s j = 0 → lin (net.A j) q ≠ 0 → |lin (net.A j) z| < |lin (net.A j) q|) :
    pick (net.s j) (lin (net.A j) (q + z)) (relu (lin (net.A j) (q + z))) =
      pick (net.s j) (lin (net.A j) q) (relu (lin (net.A j) q)) + lin (net.gam q j) z +
        net.rr q j z := by
  rw [lin_add_right]
  unfold pick ZNet.gam ZNet.rr
  rcases lt_trichotomy (net.s j) 0 with hs | hs | hs
  · have h1 : ¬ (0 : ℝ) < net.s j := not_lt.2 hs.le
    have h2 : ¬ (net.s j = 0 ∧ lin (net.A j) q = 0) := fun h => hs.ne h.1
    simp only [h1, hs, h2, if_false, if_true, lin_zero_left]
    ring
  · have h1 : ¬ (0 : ℝ) < net.s j := by rw [hs]; exact lt_irrefl 0
    have h2 : ¬ net.s j < 0 := by rw [hs]; exact lt_irrefl 0
    simp only [h1, h2, if_false]
    by_cases hq : lin (net.A j) q = 0
    · have h3 : net.s j = 0 ∧ lin (net.A j) q = 0 := ⟨hs, hq⟩
      rw [if_pos h3, hq, if_neg (lt_irrefl 0), relu_of_nonpos (le_refl (0 : ℝ)), lin_zero_left,
        zero_add]
      ring
    · have h3 : ¬ (net.s j = 0 ∧ lin (net.A j) q = 0) := fun h => hq h.2
      rw [if_neg h3]
      have hzz := hz hs hq
      rcases lt_or_gt_of_ne hq with hn | hp
      · rw [abs_of_neg hn, abs_lt] at hzz
        rw [if_neg (not_lt.2 hn.le), relu_of_nonpos (by linarith), relu_of_nonpos hn.le,
          lin_zero_left]
        ring
      · rw [abs_of_pos hp, abs_lt] at hzz
        rw [if_pos hp, relu_of_nonneg (by linarith), relu_of_nonneg hp.le]
        ring
  · have h2 : ¬ (net.s j = 0 ∧ lin (net.A j) q = 0) := fun h => hs.ne' h.1
    simp only [hs, h2, if_true, if_false]
    ring

/-- The gradient of the second-layer input `Gₖ` near `q`. -/
noncomputable def ZNet.cv (net : ZNet N h₁ h₂) (q : Point N) (k : Fin h₂) : Point N :=
  ∑ j, net.W k j • net.gam q j

/-- The positively homogeneous part of `Gₖ` at `q`. -/
noncomputable def ZNet.RR (net : ZNet N h₁ h₂) (q : Point N) (k : Fin h₂) (z : Point N) : ℝ :=
  ∑ j, net.W k j * net.rr q j z

/-- The odd part of `RR`. -/
noncomputable def ZNet.RV (net : ZNet N h₁ h₂) (q : Point N) (k : Fin h₂) : Point N :=
  ∑ j, net.W k j • net.rv q j

lemma ZNet.Gp_expand (net : ZNet N h₁ h₂) (q z : Point N)
    (hz : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 → |lin (net.A j) z| < |lin (net.A j) q|)
    (k : Fin h₂) :
    net.Gp k (q + z) = net.Gp k q + lin (net.cv q k) z + net.RR q k z := by
  unfold ZNet.Gp ZNet.cv ZNet.RR
  simp only [net.row_expand q z _ (hz _), mul_add, Finset.sum_add_distrib, lin_sum_left,
    lin_smul_left]

lemma ZNet.rr_shift (net : ZNet N h₁ h₂) (q : Point N) (a : Fin N)
    (ha : ∀ j, net.s j = 0 → lin (net.A j) q = 0 → net.A j a = 0) (j : Fin h₁) (z : Point N)
    (τ : ℝ) : net.rr q j (z + τ • unitVec a) = net.rr q j z := by
  unfold ZNet.rr
  split_ifs with h
  · rw [lin_add_right, lin_smul_right, lin_unitVec, ha j h.1 h.2, mul_zero, add_zero]
  · rfl

lemma ZNet.rr_smul (net : ZNet N h₁ h₂) (q : Point N) (j : Fin h₁) (z : Point N) {ε : ℝ}
    (hε : 0 < ε) : net.rr q j (ε • z) = ε * net.rr q j z := by
  unfold ZNet.rr
  split_ifs
  · rw [lin_smul_right, relu_mul_pos hε]
  · ring

lemma ZNet.rr_odd (net : ZNet N h₁ h₂) (q : Point N) (j : Fin h₁) (z : Point N) :
    net.rr q j z - net.rr q j (-z) = lin (net.rv q j) z := by
  unfold ZNet.rr ZNet.rv
  split_ifs
  · rw [lin_neg_right, relu_sub_relu_neg]
  · rw [lin_zero_left]; ring

lemma ZNet.RR_shift (net : ZNet N h₁ h₂) (q : Point N) (a : Fin N)
    (ha : ∀ j, net.s j = 0 → lin (net.A j) q = 0 → net.A j a = 0) (k : Fin h₂) (z : Point N)
    (τ : ℝ) : net.RR q k (z + τ • unitVec a) = net.RR q k z := by
  unfold ZNet.RR
  simp only [net.rr_shift q a ha]

lemma ZNet.RR_smul (net : ZNet N h₁ h₂) (q : Point N) (k : Fin h₂) (z : Point N) {ε : ℝ}
    (hε : 0 < ε) : net.RR q k (ε • z) = ε * net.RR q k z := by
  unfold ZNet.RR
  simp only [net.rr_smul q _ z hε, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma ZNet.RR_odd (net : ZNet N h₁ h₂) (q : Point N) (k : Fin h₂) (z : Point N) :
    net.RR q k z - net.RR q k (-z) = lin (net.RV q k) z := by
  unfold ZNet.RR ZNet.RV
  rw [lin_sum_left, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [lin_smul_left, ← net.rr_odd q j z]; ring

/-- `Gₖ(q + εw + τeₐ) = Gₖ(q) + τ mₖ + ε gₖ(w)`. -/
lemma ZNet.Gp_at (net : ZNet N h₁ h₂) (q : Point N) (a : Fin N)
    (ha : ∀ j, net.s j = 0 → lin (net.A j) q = 0 → net.A j a = 0) (k : Fin h₂) (w : Point N)
    {ε τ : ℝ} (hε : 0 < ε)
    (hw : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 →
      |ε * lin (net.A j) w| < |lin (net.A j) q| / 2)
    (hτ : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 → |τ * net.A j a| < |lin (net.A j) q| / 2) :
    net.Gp k (q + (ε • w + τ • unitVec a)) =
      net.Gp k q + τ * lin (net.cv q k) (unitVec a) +
        ε * (lin (net.cv q k) w + net.RR q k w) := by
  have hz : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 →
      |lin (net.A j) (ε • w + τ • unitVec a)| < |lin (net.A j) q| := by
    intro j hs hq
    rw [lin_add_right, lin_smul_right, lin_smul_right, lin_unitVec]
    calc |ε * lin (net.A j) w + τ * net.A j a|
        ≤ |ε * lin (net.A j) w| + |τ * net.A j a| := abs_add _ _
      _ < |lin (net.A j) q| / 2 + |lin (net.A j) q| / 2 := add_lt_add (hw j hs hq) (hτ j hs hq)
      _ = |lin (net.A j) q| := by ring
  rw [net.Gp_expand q _ hz k, net.RR_shift q a ha, net.RR_smul q k w hε, lin_add_right,
    lin_smul_right, lin_smul_right]
  ring

/-! ## The one-neuron case check -/

/-- The coefficient `κ(T, u, m)`: `sgn m` if `T = 0` and `u = 0`, else `0`. -/
noncomputable def kap (T u m : ℝ) : ℝ :=
  if T = 0 ∧ u = 0 then (if 0 < m then 1 else if m < 0 then -1 else 0) else 0

lemma key_real (T u m δ α β : ℝ) (hδ : 0 < δ) (hu : u = 0 ∨ δ * |m| < |u| / 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (pick T (u + δ * m + ε * α) (relu (u + δ * m + ε * α)) -
          pick T (u + -δ * m + ε * α) (relu (u + -δ * m + ε * α))) -
        (pick T (u + δ * m + ε * β) (relu (u + δ * m + ε * β)) -
          pick T (u + -δ * m + ε * β) (relu (u + -δ * m + ε * β))) =
      ε * (kap T u m * (α - β)) := by
  rcases lt_trichotomy T 0 with hT | hT | hT
  · refine Filter.eventually_of_forall fun ε => ?_
    simp only [pick, kap, if_neg (not_lt.2 hT.le), if_pos hT, if_neg (fun h : T = 0 ∧ u = 0 =>
      hT.ne h.1)]
    ring
  · subst hT
    have hp : ∀ x y : ℝ, pick 0 x y = y := fun x y => by simp [pick]
    simp only [hp]
    have hm1 : δ * m ≤ δ * |m| := mul_le_mul_of_nonneg_left (le_abs_self m) hδ.le
    have hm2 : -(δ * |m|) ≤ δ * m := by
      have := mul_le_mul_of_nonneg_left (abs_le.1 (le_refl |m|)).1 hδ.le; linarith
    by_cases hu0 : u = 0
    · subst hu0
      rcases lt_trichotomy m 0 with hm | hm | hm
      · have hb : 0 < δ * -m := mul_pos hδ (neg_pos.2 hm)
        filter_upwards [eventually_small α hb, eventually_small β hb] with ε h1 h2
        rw [abs_lt] at h1 h2
        rw [relu_of_nonpos (by nlinarith), relu_of_nonneg (by nlinarith),
          relu_of_nonpos (by nlinarith), relu_of_nonneg (by nlinarith)]
        simp only [kap, and_self, if_true, if_neg (not_lt.2 hm.le), if_pos hm]
        ring
      · subst hm
        refine Filter.eventually_of_forall fun ε => ?_
        simp only [mul_zero, add_zero, zero_add, sub_self, kap, and_self, if_true,
          lt_irrefl, if_false]
        ring
      · have hb : 0 < δ * m := mul_pos hδ hm
        filter_upwards [eventually_small α hb, eventually_small β hb] with ε h1 h2
        rw [abs_lt] at h1 h2
        rw [relu_of_nonneg (by nlinarith), relu_of_nonpos (by nlinarith),
          relu_of_nonneg (by nlinarith), relu_of_nonpos (by nlinarith)]
        simp only [kap, and_self, if_true, if_pos hm]
        ring
    · have hu' := hu.resolve_left hu0
      have hk : kap 0 u m = 0 := by simp [kap, hu0]
      rw [hk]
      have hb : 0 < |u| / 2 := by have := abs_pos.2 hu0; linarith
      filter_upwards [eventually_small α hb, eventually_small β hb] with ε h1 h2
      rw [abs_lt] at h1 h2
      rcases lt_or_gt_of_ne hu0 with hn | hp
      · rw [abs_of_neg hn] at h1 h2 hu'
        rw [relu_of_nonpos (by linarith), relu_of_nonpos (by linarith),
          relu_of_nonpos (by linarith), relu_of_nonpos (by linarith)]
        ring
      · rw [abs_of_pos hp] at h1 h2 hu'
        rw [relu_of_nonneg (by linarith), relu_of_nonneg (by linarith),
          relu_of_nonneg (by linarith), relu_of_nonneg (by linarith)]
        ring
  · refine Filter.eventually_of_forall fun ε => ?_
    simp only [pick, kap, if_pos hT, if_neg (fun h : T = 0 ∧ u = 0 => hT.ne' h.1)]
    ring

/-! ## The network side -/

/-- If no translation-invariant row with `Aⱼ·q = 0` sees the coordinate `a`, then the double
difference of `rest` along `±δeₐ` and `±εv` is linear in `v`. -/
theorem ZNet.claw_net (net : ZNet N h₁ h₂) (q : Point N) (a : Fin N)
    (ha : ∀ j, net.s j = 0 → lin (net.A j) q = 0 → net.A j a = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ C : Point N, ∀ v : Point N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (net.rest (q + (ε • v + δ • unitVec a)) - net.rest (q + (ε • v + (-δ) • unitVec a))) -
        (net.rest (q + (ε • (-v) + δ • unitVec a)) -
          net.rest (q + (ε • (-v) + (-δ) • unitVec a))) = ε * lin C v := by
  have hδev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 → |δ * net.A j a| < |lin (net.A j) q| / 2) ∧
      (∀ k, net.Gp k q ≠ 0 → |δ * lin (net.cv q k) (unitVec a)| < |net.Gp k q| / 2) ∧
      δ ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    refine (Filter.eventually_all.2 fun j => ?_).and
      ((Filter.eventually_all.2 fun k => ?_).and (Ioo_mem_nhdsWithin_Ioi (by norm_num)))
    · by_cases hj : net.s j = 0 ∧ lin (net.A j) q ≠ 0
      · have : 0 < |lin (net.A j) q| / 2 := by have := abs_pos.2 hj.2; linarith
        exact (eventually_small (net.A j a) this).mono fun δ h _ _ => h
      · exact Filter.eventually_of_forall fun δ h1 h2 => absurd ⟨h1, h2⟩ hj
    · by_cases hk : net.Gp k q ≠ 0
      · have : 0 < |net.Gp k q| / 2 := by have := abs_pos.2 hk; linarith
        exact (eventually_small (lin (net.cv q k) (unitVec a)) this).mono fun δ h _ => h
      · exact Filter.eventually_of_forall fun δ h1 => absurd h1 hk
  obtain ⟨δ, hδj, hδk, hδ0, hδ1⟩ := hδev.exists
  refine ⟨δ, hδ0, hδ1, ∑ k, (net.d k * kap (net.Tp k) (net.Gp k q)
    (lin (net.cv q k) (unitVec a))) • ((2 : ℝ) • net.cv q k + net.RV q k), fun v => ?_⟩
  have hδj' : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 →
      |(-δ) * net.A j a| < |lin (net.A j) q| / 2 := fun j h1 h2 => by
    rw [neg_mul, abs_neg]; exact hδj j h1 h2
  have hku : ∀ k, net.Gp k q = 0 ∨
      δ * |lin (net.cv q k) (unitVec a)| < |net.Gp k q| / 2 := by
    intro k
    by_cases hk : net.Gp k q = 0
    · exact Or.inl hk
    · right
      have := hδk k hk
      rwa [abs_mul, abs_of_pos hδ0] at this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 →
        |ε * lin (net.A j) v| < |lin (net.A j) q| / 2) ∧
      (∀ k,
        (pick (net.Tp k)
            (net.Gp k q + δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) v + net.RR q k v))
            (relu (net.Gp k q + δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) v + net.RR q k v))) -
          pick (net.Tp k)
            (net.Gp k q + -δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) v + net.RR q k v))
            (relu (net.Gp k q + -δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) v + net.RR q k v)))) -
        (pick (net.Tp k)
            (net.Gp k q + δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) (-v) + net.RR q k (-v)))
            (relu (net.Gp k q + δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) (-v) + net.RR q k (-v)))) -
          pick (net.Tp k)
            (net.Gp k q + -δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) (-v) + net.RR q k (-v)))
            (relu (net.Gp k q + -δ * lin (net.cv q k) (unitVec a) +
              ε * (lin (net.cv q k) (-v) + net.RR q k (-v))))) =
        ε * (kap (net.Tp k) (net.Gp k q) (lin (net.cv q k) (unitVec a)) *
          ((lin (net.cv q k) v + net.RR q k v) -
            (lin (net.cv q k) (-v) + net.RR q k (-v))))) ∧
      0 < ε := by
    refine (Filter.eventually_all.2 fun j => ?_).and
      ((Filter.eventually_all.2 fun k => key_real _ _ _ _ _ _ hδ0 (hku k)).and
        self_mem_nhdsWithin)
    by_cases hj : net.s j = 0 ∧ lin (net.A j) q ≠ 0
    · have : 0 < |lin (net.A j) q| / 2 := by have := abs_pos.2 hj.2; linarith
      exact (eventually_small (lin (net.A j) v) this).mono fun ε h _ _ => h
    · exact Filter.eventually_of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hj
  filter_upwards [hev] with ε hε'
  obtain ⟨hεj, hεk, hε⟩ := hε'
  have hεj' : ∀ j, net.s j = 0 → lin (net.A j) q ≠ 0 →
      |ε * lin (net.A j) (-v)| < |lin (net.A j) q| / 2 := fun j h1 h2 => by
    rw [lin_neg_right, mul_neg, abs_neg]; exact hεj j h1 h2
  have G1 := fun k => net.Gp_at q a ha k v hε hεj hδj
  have G2 := fun k => net.Gp_at q a ha k v hε hεj hδj'
  have G3 := fun k => net.Gp_at q a ha k (-v) hε hεj' hδj
  have G4 := fun k => net.Gp_at q a ha k (-v) hε hεj' hδj'
  unfold ZNet.rest
  simp only [G1, G2, G3, G4]
  rw [lin_sum_left, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := hεk k
  have hodd : (lin (net.cv q k) v + net.RR q k v) - (lin (net.cv q k) (-v) + net.RR q k (-v)) =
      lin ((2 : ℝ) • net.cv q k + net.RV q k) v := by
    rw [lin_add_left, lin_smul_left, lin_neg_right, ← net.RR_odd q k v]; ring
  rw [hodd] at e
  rw [lin_smul_left]
  linear_combination net.d k * e

/-! ## The maximum side -/

lemma Maximum_near [NeZero N] (I : Finset (Fin N)) (q : Point N) (hq0 : ∀ i ∈ I, q i = 0)
    (hq1 : ∀ i ∉ I, q i ≤ -1) (z : Point N) (hz : ∀ k, |z k| ≤ 1 / 2) (i0 : Fin N)
    (hi0 : i0 ∈ I) (hmax : ∀ k ∈ I, z k ≤ z i0) : Maximum N (q + z) = z i0 := by
  refine Maximum_eq_of _ _ i0 (by simp [hq0 i0 hi0]) fun k => ?_
  simp only [Pi.add_apply]
  by_cases hk : k ∈ I
  · rw [hq0 k hk, zero_add]; exact hmax k hk
  · have h1 := hq1 k hk
    have h2 := (abs_le.1 (hz k)).2
    have h3 := (abs_le.1 (hz i0)).1
    linarith

lemma coord_shift (w : Point N) (a k : Fin N) (s τ : ℝ) :
    (s • w + τ • unitVec a) k = s * w k + (if k = a then τ else 0) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec_apply]
  split_ifs <;> ring

/-- The maximum has no linear double difference at `q` when `|I \ {a}| ≥ 3`. -/
theorem max_claw_false [NeZero N] (I : Finset (Fin N)) (a : Fin N) (haI : a ∈ I)
    (hY : 3 ≤ (I.erase a).card) (q : Point N) (hq0 : ∀ i ∈ I, q i = 0)
    (hq1 : ∀ i ∉ I, q i ≤ -1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (C : Point N)
    (hC : ∀ v : Point N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (Maximum N (q + (ε • v + δ • unitVec a)) - Maximum N (q + (ε • v + (-δ) • unitVec a))) -
        (Maximum N (q + (ε • (-v) + δ • unitVec a)) -
          Maximum N (q + (ε • (-v) + (-δ) • unitVec a))) = ε * lin C v) : False := by
  set Y := I.erase a with hYdef
  let oneY : Point N := fun k => if k ∈ Y then 1 else 0
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ i, i ∈ Y →
        (Maximum N (q + (ε • unitVec i + δ • unitVec a)) -
            Maximum N (q + (ε • unitVec i + (-δ) • unitVec a))) -
          (Maximum N (q + (ε • (-unitVec i) + δ • unitVec a)) -
            Maximum N (q + (ε • (-unitVec i) + (-δ) • unitVec a))) =
          ε * lin C (unitVec i)) ∧
      ((Maximum N (q + (ε • oneY + δ • unitVec a)) -
            Maximum N (q + (ε • oneY + (-δ) • unitVec a))) -
          (Maximum N (q + (ε • (-oneY) + δ • unitVec a)) -
            Maximum N (q + (ε • (-oneY) + (-δ) • unitVec a))) = ε * lin C oneY) ∧
      ε ∈ Set.Ioo (0 : ℝ) (δ / 2) := by
    refine (Filter.eventually_all.2 fun i => ?_).and ((hC oneY).and
      (Ioo_mem_nhdsWithin_Ioi (Set.left_mem_Ico.2 (by linarith))))
    exact (hC (unitVec i)).mono fun ε h _ => h
  obtain ⟨ε, hi, hone, hε0, hε1⟩ := hall.exists
  have haY : a ∉ Y := Finset.not_mem_erase a I
  have hYI : ∀ i ∈ Y, i ∈ I := fun i hi => Finset.mem_of_mem_erase hi
  have hia : ∀ i ∈ Y, i ≠ a := fun i hi => Finset.ne_of_mem_erase hi
  have hz : ∀ (w : Point N) (τ : ℝ), (∀ k, |w k| ≤ 1) → |τ| ≤ δ →
      ∀ k, |(ε • w + τ • unitVec a) k| ≤ 1 / 2 := by
    intro w τ hw hτ k
    rw [coord_shift]
    have h1 : |ε * w k| ≤ ε := by
      rw [abs_mul, abs_of_pos hε0]; exact mul_le_of_le_one_right hε0.le (hw k)
    have h2 : |(if k = a then τ else 0)| ≤ δ := by
      split_ifs
      · exact hτ
      · simp [hδ0.le]
    exact (abs_add _ _).trans (by linarith)
  have hδa : |δ| ≤ δ := le_of_eq (abs_of_pos hδ0)
  have hδa' : |-δ| ≤ δ := by rw [abs_neg]; exact hδa
  have L1 : ∀ w : Point N, (∀ k, |w k| ≤ 1) →
      Maximum N (q + (ε • w + δ • unitVec a)) = δ + ε * w a := by
    intro w hw
    have := Maximum_near I q hq0 hq1 _ (hz w δ hw hδa) a haI (fun k _ => by
      rw [coord_shift, coord_shift, if_pos (rfl : a = a)]
      rcases eq_or_ne k a with rfl | hka
      · simp
      · rw [if_neg hka]
        have e1 := mul_le_mul_of_nonneg_left (abs_le.1 (hw k)).2 hε0.le
        have e2 := mul_le_mul_of_nonneg_left (abs_le.1 (hw a)).1 hε0.le
        linarith)
    rw [this, coord_shift, if_pos (rfl : a = a)]; ring
  have L2 : ∀ (w : Point N) (i0 : Fin N), i0 ∈ Y → (∀ k ∈ Y, w k ≤ w i0) →
      (∀ k, |w k| ≤ 1) → Maximum N (q + (ε • w + (-δ) • unitVec a)) = ε * w i0 := by
    intro w i0 hi0 hmax hw
    have := Maximum_near I q hq0 hq1 _ (hz w (-δ) hw hδa') i0 (hYI i0 hi0) (fun k hk => by
      rw [coord_shift, coord_shift, if_neg (hia i0 hi0)]
      rcases eq_or_ne k a with rfl | hka
      · rw [if_pos rfl]
        have e1 := mul_le_mul_of_nonneg_left (abs_le.1 (hw k)).2 hε0.le
        have e2 := mul_le_mul_of_nonneg_left (abs_le.1 (hw i0)).1 hε0.le
        linarith
      · rw [if_neg hka]
        have e1 := mul_le_mul_of_nonneg_left (hmax k (Finset.mem_erase.2 ⟨hka, hk⟩)) hε0.le
        linarith)
    rw [this, coord_shift, if_neg (hia i0 hi0)]; ring
  have hu1 : ∀ i k : Fin N, |unitVec i k| ≤ 1 := fun i k => by
    rw [unitVec_apply]; split_ifs <;> simp
  have hun1 : ∀ i k : Fin N, |(-unitVec i) k| ≤ 1 := fun i k => by
    rw [Pi.neg_apply, abs_neg]; exact hu1 i k
  have ho1 : ∀ k : Fin N, |oneY k| ≤ 1 := fun k => by
    show |(if k ∈ Y then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp
  have hon1 : ∀ k : Fin N, |(-oneY) k| ≤ 1 := fun k => by
    rw [Pi.neg_apply, abs_neg]; exact ho1 k
  -- `C i = -1` for `i ∈ Y`
  have hCi : ∀ i ∈ Y, C i = -1 := by
    intro i hiY
    obtain ⟨i', hi'Y, hi'i⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < Y.card) i
    have hai : a ≠ i := (hia i hiY).symm
    have e := hi i hiY
    rw [L1 _ (hu1 i), L1 _ (hun1 i),
      L2 _ i hiY (fun k _ => by
        rw [unitVec_apply, unitVec_apply, if_pos rfl]; split_ifs <;> norm_num) (hu1 i),
      L2 _ i' hi'Y (fun k _ => by
        rw [Pi.neg_apply, Pi.neg_apply, unitVec_apply, unitVec_apply, if_neg hi'i]
        split_ifs <;> norm_num) (hun1 i),
      lin_unitVec, Pi.neg_apply, Pi.neg_apply, unitVec_apply, unitVec_apply, unitVec_apply,
      if_neg hai, if_pos rfl, if_neg hi'i] at e
    have : ε * (C i + 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  -- the vector `1_Y`
  obtain ⟨i0, hi0⟩ : Y.Nonempty := Finset.card_pos.1 (by omega)
  have hoa : oneY a = 0 := if_neg haY
  have hoi : oneY i0 = 1 := if_pos hi0
  rw [L1 _ ho1, L1 _ hon1,
    L2 _ i0 hi0 (fun k hk => by
      show (if k ∈ Y then (1 : ℝ) else 0) ≤ (if i0 ∈ Y then 1 else 0)
      rw [if_pos hk, if_pos hi0]) ho1,
    L2 _ i0 hi0 (fun k hk => by
      show -(if k ∈ Y then (1 : ℝ) else 0) ≤ -(if i0 ∈ Y then 1 else 0)
      rw [if_pos hk, if_pos hi0]) hon1,
    Pi.neg_apply, Pi.neg_apply, hoa, hoi] at hone
  have hsum : lin C oneY = -(Y.card : ℝ) := by
    have : ∀ k, C k * oneY k = if k ∈ Y then C k else 0 := fun k => by
      show C k * (if k ∈ Y then (1 : ℝ) else 0) = _
      split_ifs <;> ring
    simp only [lin, this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_congr rfl hCi, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [hsum] at hone
  have h3 : (3 : ℝ) ≤ Y.card := by exact_mod_cast hY
  have : ε * (Y.card - 2) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h <;> linarith

/-- **Lemma C4 (claw).** If a bias-free network computes `max_N`, `a ∈ I`, `|I \ {a}| ≥ 3`, and
`q` vanishes on `I` and is `≤ -1` off `I`, then some translation-invariant row `Aⱼ` has
`Aⱼ·q = 0` and `Aⱼ(a) ≠ 0`. -/
theorem ZNet.claw [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x)
    (I : Finset (Fin N)) (a : Fin N) (haI : a ∈ I) (hY : 3 ≤ (I.erase a).card) (q : Point N)
    (hq0 : ∀ i ∈ I, q i = 0) (hq1 : ∀ i ∉ I, q i ≤ -1) :
    ∃ j, net.s j = 0 ∧ lin (net.A j) q = 0 ∧ net.A j a ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨δ, hδ0, hδ1, C, hC⟩ := net.claw_net q a hc
  have hrest := (net.max_plus h).2
  exact max_claw_false I a haI hY q hq0 hq1 δ hδ0 hδ1 C fun v =>
    (hC v).mono fun ε e => by simp only [hrest]; exact e

end Frontier
end MaxCaterpillar
