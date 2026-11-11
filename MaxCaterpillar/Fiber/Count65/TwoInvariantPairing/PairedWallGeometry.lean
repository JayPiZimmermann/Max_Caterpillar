import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.CarrierPlane

/-! # Carrier geometry at the paired four-root wall

The same active-kernel argument works at a root wall: invariant rows which
are exactly zero need only annihilate the chosen perturbation direction.
No bound on the second hidden width is used.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators Filter Topology Frontier
variable {N h₁ h₂ : ℕ}

private lemma negative_tail (a s : ℝ) (hs : s < 0) :
    ∀ᶠ t in atTop, a + t * s < 0 := by
  filter_upwards [eventually_ge_atTop (a / -s + 1)] with t ht
  have hm := (div_le_iff (neg_pos.mpr hs)).mp
    (show a / -s ≤ t - 1 by linarith)
  nlinarith only [hm, hs]

/-- At either diagonal end, every active invariant row and every carrier
at that end must jointly retain a maximizing coordinate. -/
theorem diagonal_active_invariant_kernel_top_coordinate [NeZero N]
    (net : ZNet N h₁ h₂) (hexact : ∀ x, net.eval x = Maximum N x)
    (q w : Point N) (δ : ℝ) (hδ : δ ≠ 0)
    (hzero : ∀ j, net.s j = 0 → 0 ≤ lin (net.A j) q → lin (net.A j) w = 0)
    (hw : ∀ j, 0 < δ * net.s j → lin (net.A j) w = 0)
    (i : Fin N) (hi : q i = Maximum N q) : w i = 0 := by
  have htail : ∀ᶠ t in atTop, ∀ j, δ * net.s j < 0 →
      lin (net.A j) (q + diag (δ * t)) < 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hs : δ * net.s j < 0
    · filter_upwards [negative_tail (lin (net.A j) q) (δ * net.s j) hs] with t ht
      intro _
      rw [net.lin_add_diag]
      nlinarith only [ht]
    · exact Filter.eventually_of_forall fun _ h => (hs h).elim
  obtain ⟨t, ht⟩ := htail.exists
  have hactive : ∀ j, 0 ≤ lin (net.A j) (q + diag (δ * t)) →
      lin (net.A j) w = 0 := by
    intro j hj
    rcases lt_trichotomy (δ * net.s j) 0 with hs | hs | hs
    · exact (not_lt.mpr hj (ht j hs)).elim
    · have hz : net.s j = 0 := (mul_eq_zero.mp hs).resolve_left hδ
      apply hzero j hz
      simpa only [net.lin_add_diag, hz, mul_zero, add_zero] using hj
    · exact hw j hs
  let Phi : (Fin h₁ → ℝ) → ℝ := fun y => ∑ k, net.d k * relu (∑ j, net.W k j * y j)
  have hmodel : ∀ x : Point N, Maximum N x =
      lin (0 : Point N) x + Phi (fun j => relu (lin (net.A j) x)) := by
    intro x
    rw [lin_zero_left, zero_add]
    exact (hexact x).symm
  have htop : (q + diag (δ * t) : Point N) i = Maximum N (q + diag (δ * t)) := by
    simp only [Pi.add_apply, diag, hi, Maximum_add_diag]
  have he := active_kernel_top_coordinate net.A (0 : Point N) Phi hmodel
    (q + diag (δ * t)) w hactive i htop
  simpa only [lin_zero_left] using he

/-- If a single observation plus equality of two anchors retains their value,
that observation has no coefficients outside the anchor plane. -/
theorem one_observation_wall_plane (a : Point N) (q s : Fin N) (hqs : q ≠ s)
    (hker : ∀ w : Point N, lin a w = 0 → w q = w s → w q = 0) :
    ∀ i, i ≠ q → i ≠ s → a i = 0 := by
  intro i hiq his
  let w : Point N := (a q + a s) • unitVec i - a i • (unitVec q + unitVec s)
  have hw : lin a w = 0 := by
    dsimp [w]
    rw [lin_sub_right, lin_smul_right, lin_smul_right, lin_add_right,
      lin_unitVec, lin_unitVec, lin_unitVec]
    ring
  have hwq : w q = -a i := by simp [w, unitVec, hiq.symm, hqs]
  have hws : w s = -a i := by simp [w, unitVec, his.symm, hqs.symm]
  have h := hker w hw (hwq.trans hws.symm)
  linarith only [h, hwq]

/-- Four invariant root directions at a paired-code wall force each unique
carrier to be supported on the two wall anchors. -/
theorem paired_wall_carrier_plane [NeZero N]
    (net : ZNet N h₁ h₂) (hexact : ∀ x, net.eval x = Maximum N x)
    (p q r s : Fin N) (hpq : p ≠ q) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hroots : ∀ j, net.s j = 0 →
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec p - unitVec q)) ∨
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec r - unitVec s)) ∨
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec q - unitVec s)) ∨
      (∃ c : ℝ, 0 < c ∧ net.A j = c • (unitVec s - unitVec q)))
    (δ : ℝ) (hδ : δ ≠ 0) (a : Fin h₁)
    (hcarrier : ∀ j, 0 < δ * net.s j → j = a) :
    ∀ i, i ≠ q → i ≠ s → net.A a i = 0 := by
  let z : Point N := unitVec q + unitVec s
  have hzq : z q = 1 := by simp [z, unitVec, hqs]
  have hz : z q = Maximum N z := by
    rw [hzq]
    symm
    apply Maximum_eq_of z 1 q hzq
    intro i
    simp only [z, Pi.add_apply, unitVec]
    split_ifs with hi hj
    · exact (hqs (hi.symm.trans hj)).elim
    all_goals norm_num
  apply one_observation_wall_plane (net.A a) q s hqs
  intro w hwa hws
  apply diagonal_active_invariant_kernel_top_coordinate net hexact z w δ hδ _ _ q hz
  · intro j hj hactive
    rcases hroots j hj with ⟨c,hc,he⟩ | ⟨c,hc,he⟩ | ⟨c,hc,he⟩ | ⟨c,hc,he⟩
    · rw [he, lin_smul_left, lin_coordinate_difference] at hactive
      have : c * (-1) < 0 := by nlinarith only [hc]
      have hval : z p - z q = -1 := by simp [z, unitVec, hpq, hps, hqs]
      rw [hval] at hactive
      linarith
    · rw [he, lin_smul_left, lin_coordinate_difference] at hactive
      have : c * (-1) < 0 := by nlinarith only [hc]
      have hval : z r - z s = -1 := by simp [z, unitVec, hqr.symm, hrs, hqs.symm]
      rw [hval] at hactive
      linarith
    · rw [he, lin_smul_left, lin_coordinate_difference, hws, sub_self, mul_zero]
    · rw [he, lin_smul_left, lin_coordinate_difference, hws, sub_self, mul_zero]
  · intro j hj
    rw [hcarrier j hj]
    exact hwa

#check @paired_wall_carrier_plane
#print axioms paired_wall_carrier_plane
end MaxCaterpillar.Fiber.Count65
