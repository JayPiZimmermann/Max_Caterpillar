import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic.Linarith

/-!
# Local-to-global convexity on `ℝ`

`convexOn_univ_of_locally`: a continuous function on `ℝ` that is convex on a ball
around every point is convex on all of `ℝ`.

Proof (chord-maximum argument): fix `x < y` and let `D` be the deficit of `G` against
the chord through `(x, G x)` and `(y, G y)` on `[x, y]`.  `D` attains its maximum `M`;
if `M > 0`, the *first* maximizer `τ = sInf S` lies strictly inside `(x, y)`, and local
convexity at `τ` forces the deficit at `τ - η` to equal `M` as well — contradicting
minimality of `τ`.  So `M ≤ 0`, i.e. `G` lies below every chord.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- The chord through `(x, Gx)` and `(y, Gy)`, as a function of `t`. -/
noncomputable def chord (Gx Gy x y t : ℝ) : ℝ :=
  ((y - t) * Gx + (t - x) * Gy) / (y - x)

theorem chord_left {Gx Gy x y : ℝ} (hyx : y - x ≠ 0) : chord Gx Gy x y x = Gx := by
  unfold chord
  rw [sub_self, zero_mul, add_zero, mul_comm, mul_div_assoc, div_self hyx, mul_one]

theorem chord_right {Gx Gy x y : ℝ} (hyx : y - x ≠ 0) : chord Gx Gy x y y = Gy := by
  unfold chord
  rw [sub_self, zero_mul, zero_add, mul_comm, mul_div_assoc, div_self hyx, mul_one]

/-- The chord evaluates affinely on convex combinations of its endpoints. -/
theorem chord_combo {Gx Gy x y a b : ℝ} (hyx : y - x ≠ 0) (hab : a + b = 1) :
    chord Gx Gy x y (a * x + b * y) = a * Gx + b * Gy := by
  unfold chord
  have hnum : (y - (a * x + b * y)) * Gx + ((a * x + b * y) - x) * Gy
      = (y - x) * (a * Gx + b * Gy) := by
    have ha : a = 1 - b := by linarith
    rw [ha]
    ring
  rw [hnum, mul_comm, mul_div_assoc, div_self hyx, mul_one]

theorem continuous_chord (Gx Gy x y : ℝ) : Continuous (chord Gx Gy x y) := by
  show Continuous fun t => ((y - t) * Gx + (t - x) * Gy) / (y - x)
  have e : (fun t => ((y - t) * Gx + (t - x) * Gy) / (y - x))
      = fun t => ((y - t) * Gx + (t - x) * Gy) * (y - x)⁻¹ := by
    funext t
    rw [div_eq_mul_inv]
  rw [e]
  exact (((continuous_const.sub continuous_id).mul continuous_const).add
    ((continuous_id.sub continuous_const).mul continuous_const)).mul continuous_const

/-- On `[x, y]`, a continuous locally convex function lies below its chord. -/
theorem le_chord_of_locally {G : ℝ → ℝ} (hG : Continuous G)
    (hloc : ∀ t₀ : ℝ, ∃ δ > 0, ConvexOn ℝ (Metric.ball t₀ δ) G)
    {x y : ℝ} (hxy : x < y) :
    ∀ t ∈ Set.Icc x y, G t ≤ chord (G x) (G y) x y t := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxy)
  intro t ht
  have hDcont : Continuous fun s => G s - chord (G x) (G y) x y s :=
    hG.sub (continuous_chord _ _ _ _)
  obtain ⟨T, hTmem, hTmax⟩ := isCompact_Icc.exists_forall_ge
    (Set.nonempty_Icc.mpr (le_of_lt hxy)) hDcont.continuousOn
  have hTmax' : ∀ z ∈ Set.Icc x y,
      G z - chord (G x) (G y) x y z ≤ G T - chord (G x) (G y) x y T := hTmax
  rcases le_or_lt (G T - chord (G x) (G y) x y T) 0 with hM | hM
  · have h := hTmax' t ht
    linarith
  · exfalso
    have hDx : G x - chord (G x) (G y) x y x = 0 := by
      rw [chord_left hyx]
      ring
    have hDy : G y - chord (G x) (G y) x y y = 0 := by
      rw [chord_right hyx]
      ring
    -- the set of maximizers and its infimum
    have hSclosed : IsClosed (Set.Icc x y ∩
        {s | G s - chord (G x) (G y) x y s = G T - chord (G x) (G y) x y T}) :=
      isClosed_Icc.inter (isClosed_eq hDcont continuous_const)
    have hSne : (Set.Icc x y ∩
        {s | G s - chord (G x) (G y) x y s = G T - chord (G x) (G y) x y T}).Nonempty :=
      ⟨T, hTmem, rfl⟩
    have hSbdd : BddBelow (Set.Icc x y ∩
        {s | G s - chord (G x) (G y) x y s = G T - chord (G x) (G y) x y T}) :=
      BddBelow.mono (Set.inter_subset_left _ _) bddBelow_Icc
    obtain ⟨hτmem, hτeq⟩ := hSclosed.csInf_mem hSne hSbdd
    obtain ⟨hxτ, hτy⟩ := hτmem
    set τ := sInf (Set.Icc x y ∩
      {s | G s - chord (G x) (G y) x y s = G T - chord (G x) (G y) x y T})
    have hτeq' : G τ - chord (G x) (G y) x y τ = G T - chord (G x) (G y) x y T := hτeq
    have hxτ' : x < τ := by
      rcases eq_or_lt_of_le hxτ with h | h
      · exfalso
        rw [← h] at hτeq'
        rw [hDx] at hτeq'
        linarith
      · exact h
    have hτy' : τ < y := by
      rcases eq_or_lt_of_le hτy with h | h
      · exfalso
        rw [h] at hτeq'
        rw [hDy] at hτeq'
        linarith
      · exact h
    obtain ⟨δ, hδ, hconv⟩ := hloc τ
    set η := min (δ / 2) (min ((τ - x) / 2) ((y - τ) / 2))
    have hη : 0 < η :=
      lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηx : η ≤ (τ - x) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hηy : η ≤ (y - τ) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have humem : (τ - η) ∈ Metric.ball τ δ := by
      rw [Metric.mem_ball, Real.dist_eq, show τ - η - τ = -η from by ring, abs_neg,
        abs_of_pos hη]
      exact hηδ
    have hwmem : (τ + η) ∈ Metric.ball τ δ := by
      rw [Metric.mem_ball, Real.dist_eq, show τ + η - τ = η from by ring, abs_of_pos hη]
      exact hηδ
    have huIcc : (τ - η) ∈ Set.Icc x y := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hwIcc : (τ + η) ∈ Set.Icc x y := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hmid := hconv.2 humem hwmem (le_of_lt one_half_pos) (le_of_lt one_half_pos)
      (by ring : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      show (1 / 2 : ℝ) * (τ - η) + (1 / 2) * (τ + η) = τ from by ring] at hmid
    have hCmid : chord (G x) (G y) x y τ
        = (1 / 2) * chord (G x) (G y) x y (τ - η)
          + (1 / 2) * chord (G x) (G y) x y (τ + η) := by
      unfold chord
      ring
    have hDu := hTmax' _ huIcc
    have hDw := hTmax' _ hwIcc
    have huS : (τ - η) ∈ Set.Icc x y ∩
        {s | G s - chord (G x) (G y) x y s = G T - chord (G x) (G y) x y T} := by
      refine ⟨huIcc, ?_⟩
      show G (τ - η) - chord (G x) (G y) x y (τ - η)
          = G T - chord (G x) (G y) x y T
      linarith
    have hle : τ ≤ τ - η := csInf_le hSbdd huS
    linarith

/-- **Local-to-global convexity.**  A continuous function on `ℝ` that is convex on a
ball around every point is convex on `ℝ`. -/
theorem convexOn_univ_of_locally {G : ℝ → ℝ} (hG : Continuous G)
    (hloc : ∀ t₀ : ℝ, ∃ δ > 0, ConvexOn ℝ (Metric.ball t₀ δ) G) :
    ConvexOn ℝ Set.univ G := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hax : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
    have hay : a * y + b * y = y := by rw [← add_mul, hab, one_mul]
    have hb' : 0 ≤ b * (y - x) := mul_nonneg hb (by linarith)
    have ha' : 0 ≤ a * (y - x) := mul_nonneg ha (by linarith)
    have hp : (a * x + b * y) ∈ Set.Icc x y :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h := le_chord_of_locally hG hloc hxy _ hp
    rw [chord_combo (sub_ne_zero.mpr (ne_of_gt hxy)) hab] at h
    show G (a * x + b * y) ≤ a * G x + b * G y
    exact h
  · show G (a * x + b * y) ≤ a * G x + b * G y
    rw [← hxy, show a * x + b * x = x from by rw [← add_mul, hab, one_mul]]
    have he : a * G x + b * G x = G x := by rw [← add_mul, hab, one_mul]
    linarith
  · have hax : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
    have hay : a * y + b * y = y := by rw [← add_mul, hab, one_mul]
    have hb' : 0 ≤ b * (x - y) := mul_nonneg hb (by linarith)
    have ha' : 0 ≤ a * (x - y) := mul_nonneg ha (by linarith)
    have hp : (b * y + a * x) ∈ Set.Icc y x :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h := le_chord_of_locally hG hloc hxy _ hp
    rw [chord_combo (sub_ne_zero.mpr (ne_of_gt hxy)) (show b + a = 1 from by linarith)] at h
    show G (a * x + b * y) ≤ a * G x + b * G y
    rw [show a * x + b * y = b * y + a * x from by ring]
    linarith

end MaxNN
