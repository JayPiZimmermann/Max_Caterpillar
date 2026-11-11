import MaxCaterpillar.Fiber.First65
import MaxCaterpillar.Fiber.First65.ActiveSpan
import MaxCaterpillar.Fiber.First65.TwoIncrement

/-!
# Two-invariant-row anchor geometry

The information-loss argument is independent of the second hidden width.
This leaf develops the actual-network bridge used by the paired-sector
classification. It does not assume that an arbitrary completion is paired.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators Filter Topology Frontier

variable {N h₁ h₂ : ℕ}

private lemma eventually_negative_affine (a s : ℝ) (hs : s < 0) :
    ∀ᶠ t in atTop, a + t * s < 0 := by
  filter_upwards [eventually_ge_atTop (a / -s + 1)] with t ht
  have hm := (div_le_iff (neg_pos.mpr hs)).mp
    (show a / -s ≤ t - 1 by linarith)
  nlinarith only [hm, hs]

/-- If all invariant rows are inactive at q, the active carriers at either
end of its diagonal ray must retain every maximizing coordinate of q.
The hypothesis is a kernel condition on the actual first rows. -/
theorem diagonal_carrier_kernel_top_coordinate [NeZero N]
    (net : ZNet N h₁ h₂) (hexact : ∀ x, net.eval x = Maximum N x)
    (q w : Point N) (δ : ℝ) (hδ : δ ≠ 0)
    (hzero : ∀ j, net.s j = 0 → lin (net.A j) q < 0)
    (hw : ∀ j, 0 < δ * net.s j → lin (net.A j) w = 0)
    (i : Fin N) (hi : q i = Maximum N q) : w i = 0 := by
  have htail : ∀ᶠ t in atTop, ∀ j, δ * net.s j < 0 →
      lin (net.A j) (q + diag (δ * t)) < 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hs : δ * net.s j < 0
    · filter_upwards [eventually_negative_affine (lin (net.A j) q)
        (δ * net.s j) hs] with t ht
      intro _
      rw [net.lin_add_diag]
      nlinarith only [ht]
    · exact Filter.eventually_of_forall fun _ h => (hs h).elim
  obtain ⟨t, ht⟩ := htail.exists
  have hactive : ∀ j, 0 ≤ lin (net.A j) (q + diag (δ * t)) →
      lin (net.A j) w = 0 := by
    intro j hj
    apply hw j
    rcases lt_trichotomy (δ * net.s j) 0 with hs | hs | hs
    · exact (not_lt.mpr hj (ht j hs)).elim
    · have hz : net.s j = 0 := (mul_eq_zero.mp hs).resolve_left hδ
      have hb := hzero j hz
      rw [net.lin_add_diag, hz, mul_zero, add_zero] at hj
      linarith
    · exact hs
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

/-- Two observations retaining two distinct coordinates span precisely that
coordinate plane. The proof uses three explicit kernel vectors. -/
theorem two_observation_anchor_plane (a b : Point N) (p q : Fin N)
    (hpq : p ≠ q)
    (hker : ∀ w : Point N, lin a w = 0 → lin b w = 0 → w p = 0 ∧ w q = 0) :
    a p * b q - a q * b p ≠ 0 ∧
      ∀ r, r ≠ p → r ≠ q → a r = 0 ∧ b r = 0 := by
  have hpq' : q ≠ p := hpq.symm
  have hdet : a p * b q - a q * b p ≠ 0 := by
    intro hz
    have h₁ := hker (b q • unitVec p - b p • unitVec q)
      (by rw [lin_sub_right, lin_smul_right, lin_smul_right, lin_unitVec, lin_unitVec];
          nlinarith only [hz])
      (by rw [lin_sub_right, lin_smul_right, lin_smul_right, lin_unitVec, lin_unitVec]; ring)
    have h₂ := hker (a q • unitVec p - a p • unitVec q)
      (by rw [lin_sub_right, lin_smul_right, lin_smul_right, lin_unitVec, lin_unitVec]; ring)
      (by rw [lin_sub_right, lin_smul_right, lin_smul_right, lin_unitVec, lin_unitVec];
          nlinarith only [hz])
    simp [unitVec, hpq, hpq'] at h₁ h₂
    have hbad := hker (unitVec p) (by rw [lin_unitVec, h₂.2])
      (by rw [lin_unitVec, h₁.2])
    simpa [unitVec, hpq'] using hbad
  refine ⟨hdet, ?_⟩
  intro r hrp hrq
  let d : ℝ := a p * b q - a q * b p
  let u : ℝ := a r * b q - a q * b r
  let v : ℝ := a p * b r - a r * b p
  let w : Point N := d • unitVec r - u • unitVec p - v • unitVec q
  have ha : lin a w = 0 := by
    dsimp only [w]
    rw [lin_sub_right, lin_sub_right, lin_smul_right, lin_smul_right,
      lin_smul_right, lin_unitVec, lin_unitVec, lin_unitVec]
    ring
  have hb : lin b w = 0 := by
    dsimp only [w]
    rw [lin_sub_right, lin_sub_right, lin_smul_right, lin_smul_right,
      lin_smul_right, lin_unitVec, lin_unitVec, lin_unitVec]
    ring
  have hh := hker w ha hb
  have hu : u = 0 := by
    have hwval : w p = -u := by simp [w, unitVec, hrp.symm, hpq]
    linarith only [hh.1, hwval]
  have hv : v = 0 := by
    have hwval : w q = -v := by simp [w, unitVec, hrq.symm, hpq']
    linarith only [hh.2, hwval]
  have ha_mul : a r * (a p * b q - a q * b p) = 0 := by
    calc
      _ = a p * u + a q * v := by dsimp [u,v]; ring
      _ = 0 := by rw [hu,hv]; ring
  have hb_mul : b r * (a p * b q - a q * b p) = 0 := by
    calc
      _ = b p * u + b q * v := by dsimp [u,v]; ring
      _ = 0 := by rw [hu,hv]; ring
  exact ⟨(mul_eq_zero.mp ha_mul).resolve_right hdet,
    (mul_eq_zero.mp hb_mul).resolve_right hdet⟩

/-- The four-coordinate form used for the two inactive pair anchors. -/
theorem anchor_plane_of_kernel (a b : Point 4)
    (hker : ∀ w : Point 4, lin a w = 0 → lin b w = 0 → w 1 = 0 ∧ w 3 = 0) :
    a 1 * b 3 - a 3 * b 1 ≠ 0 ∧
      a 0 = 0 ∧ a 2 = 0 ∧ b 0 = 0 ∧ b 2 = 0 := by
  obtain ⟨hd, hout⟩ := two_observation_anchor_plane a b 1 3 (by decide) hker
  exact ⟨hd, (hout 0 (by decide) (by decide)).1,
    (hout 2 (by decide) (by decide)).1, (hout 0 (by decide) (by decide)).2,
    (hout 2 (by decide) (by decide)).2⟩

#check @diagonal_carrier_kernel_top_coordinate
#check @two_observation_anchor_plane
#print axioms diagonal_carrier_kernel_top_coordinate
#print axioms two_observation_anchor_plane
end MaxCaterpillar.Fiber.Count65
