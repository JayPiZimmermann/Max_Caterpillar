import MaxCaterpillar.Fiber.Mixed65.CarrierForcing
import MaxCaterpillar.Fiber.JumpBalance

/-! # Effective amplitudes of the two forced mixed-dictionary carriers

An arbitrary three-gate residual identity with the forced left and right carrier
directions has effective carrier amplitudes at least one. This is derived from
local exact crease balance after choosing a facet point where the other carrier
does not vanish. No residual normal-form chart is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

private lemma max_self_add_relu (a s : ℝ) : max a (a + s) = a + relu s := by
  rcases le_total 0 s with hs | hs
  · rw [relu_of_nonneg hs, max_eq_right (by linarith)]
  · rw [relu_of_nonpos hs, max_eq_left (by linarith), add_zero]

/-- The exact local scalar identity on an open top facet, with all actual gate
intercepts retained. -/
theorem ResidualSystem.facet_local_identity {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (h : d.Represents t)
    (q b : ℝ) (hq : 0 < q) (ha : 0 < q + b) :
    ∀ s : ℝ, |s| < q + b →
      relu s = d.lW * s + (d.base t q b (q + b) - (q + b)) +
        ∑ i, d.out i * relu (d.W i * s + d.gate t i q b (q + b)) := by
  intro s hs
  have hcs : 0 ≤ (q + b) + s := by linarith [(abs_lt.mp hs).1]
  have hh := h q b ((q + b) + s)
  rw [max_eq_left (by linarith : b ≤ q + b), relu_of_nonneg hcs, max_self_add_relu] at hh
  have hbase := form_shift_last t d.lU d.lV d.lW d.lT q b (q + b) s ha.le hcs
  change d.base t q b ((q + b) + s) = d.lW * s + d.base t q b (q + b) at hbase
  have hgate : ∀ i, d.gate t i q b ((q + b) + s) =
      d.W i * s + d.gate t i q b (q + b) := fun i =>
    form_shift_last t (d.U i) (d.V i) (d.W i) (d.T i) q b (q + b) s ha.le hcs
  simp_rw [hbase, hgate] at hh
  linarith only [hh]

/-- A gate that is the only potentially positive vanishing gate on an open facet
has effective amplitude at least one. -/
theorem ResidualSystem.unique_facet_amplitude_ge_one {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (h : d.Represents t)
    (q b : ℝ) (hq : 0 < q) (ha : 0 < q + b) (j : ι)
    (hj : d.gate t j q b (q + b) = 0)
    (hother : ∀ i, d.gate t i q b (q + b) = 0 → i ≠ j → d.out i ≤ 0) :
    1 ≤ d.out j * |d.W j| := by
  exact unique_positive_unit_jump_amplitude_ge_one d.W
    (fun i => d.gate t i q b (q + b)) d.out d.lW
    (d.base t q b (q + b) - (q + b)) (q + b) ha
    (d.facet_local_identity t h q b hq ha) j hj hother

private lemma exists_affine_nonzero_on_Ioo (A B l u : ℝ) (hlu : l < u)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ x ∈ Set.Ioo l u, A + B * x ≠ 0 := by
  classical
  by_cases hB : B = 0
  · refine ⟨(l + u) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    have hA : A ≠ 0 := hAB.resolve_right (not_not.mpr hB)
    simpa only [hB, zero_mul, add_zero] using hA
  · obtain ⟨x, hx, hnot⟩ := (Set.Ioo_infinite hlu).exists_not_mem_finset ({-A / B} : Finset ℝ)
    refine ⟨x, hx, ?_⟩
    intro hz
    have he : x = -A / B := (eq_div_iff hB).mpr (by nlinarith only [hz])
    apply hnot
    simpa only [Finset.mem_singleton] using he

/-- A left carrier vanishes on its entire open left facet. -/
theorem ResidualSystem.left_carrier_facet_zero {ι : Type*}
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (i : ι)
    (hU : d.U i = -(1 + t) * d.W i) (hT : d.T i = d.W i)
    (b : ℝ) (hb : b ∈ Set.Ioo (-1 : ℝ) 0) :
    d.gate t i 1 b (1 + b) = 0 := by
  simp only [ResidualSystem.gate, form, hU, hT,
    relu_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), relu_of_nonpos hb.2.le,
    relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ 1 + b),
    relu_of_nonneg (by linarith [hb.2] : (0 : ℝ) ≤ t * 1 - b), mul_zero]
  ring

/-- A right carrier vanishes on its entire open right facet. -/
theorem ResidualSystem.right_carrier_facet_zero {ι : Type*}
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (i : ι)
    (hU : d.U i = -d.W i) (hV : d.V i = -d.W i)
    (b : ℝ) (hb : b ∈ Set.Ioo (t + 1) (t + 2)) :
    d.gate t i 1 b (1 + b) = 0 := by
  simp only [ResidualSystem.gate, form, hU, hV,
    relu_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
    relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ b),
    relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ 1 + b),
    relu_of_nonpos (by linarith [hb.1] : t * 1 - b ≤ 0), mul_zero]
  ring

/-- The right carrier is nonzero somewhere on the open left facet. -/
theorem ResidualSystem.right_carrier_nonzero_left_facet {ι : Type*}
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (i : ι)
    (hW : d.W i ≠ 0) (hU : d.U i = -d.W i) :
    ∃ b ∈ Set.Ioo (-1 : ℝ) 0, d.gate t i 1 b (1 + b) ≠ 0 := by
  have hAB : t * d.T i ≠ 0 ∨ d.W i - d.T i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hT : d.T i = 0 := (mul_eq_zero.mp hn.1).resolve_left (ne_of_gt ht)
    exact hW (by linarith [hn.2])
  obtain ⟨b, hb, hne⟩ := exists_affine_nonzero_on_Ioo
    (t * d.T i) (d.W i - d.T i) (-1) 0 (by norm_num) hAB
  refine ⟨b, hb, ?_⟩
  have he : d.gate t i 1 b (1 + b) = t * d.T i + (d.W i - d.T i) * b := by
    simp only [ResidualSystem.gate, form, hU,
      relu_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), relu_of_nonpos hb.2.le,
      relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ 1 + b),
      relu_of_nonneg (by linarith [hb.2] : (0 : ℝ) ≤ t * 1 - b), mul_zero]
    ring
  rwa [he]

/-- The left carrier is nonzero somewhere on the open right facet. -/
theorem ResidualSystem.left_carrier_nonzero_right_facet {ι : Type*}
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (i : ι)
    (hW : d.W i ≠ 0) (hU : d.U i = -(1 + t) * d.W i) :
    ∃ b ∈ Set.Ioo (t + 1) (t + 2), d.gate t i 1 b (1 + b) ≠ 0 := by
  have hA : -t * d.W i ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (ne_of_gt ht)) hW
  obtain ⟨b, hb, hne⟩ := exists_affine_nonzero_on_Ioo
    (-t * d.W i) (d.V i + d.W i) (t + 1) (t + 2) (by linarith) (Or.inl hA)
  refine ⟨b, hb, ?_⟩
  have he : d.gate t i 1 b (1 + b) = -t * d.W i + (d.V i + d.W i) * b := by
    simp only [ResidualSystem.gate, form, hU,
      relu_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
      relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ b),
      relu_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ 1 + b),
      relu_of_nonpos (by linarith [hb.1] : t * 1 - b ≤ 0), mul_zero]
    ring
  rwa [he]

/-- Both effective positive carrier amplitudes in a three-gate system are at
least one. Only the sign of the remaining output is assumed. -/
theorem ResidualSystem.carrier_amplitudes_ge_one
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hneg : d.out 2 ≤ 0)
    (hW0 : d.W 0 ≠ 0) (hU0 : d.U 0 = -(1 + t) * d.W 0) (hT0 : d.T 0 = d.W 0)
    (hW1 : d.W 1 ≠ 0) (hU1 : d.U 1 = -d.W 1) (hV1 : d.V 1 = -d.W 1) :
    1 ≤ d.out 0 * |d.W 0| ∧ 1 ≤ d.out 1 * |d.W 1| := by
  constructor
  · obtain ⟨b, hb, hother⟩ := d.right_carrier_nonzero_left_facet t ht 1 hW1 hU1
    apply d.unique_facet_amplitude_ge_one t h 1 b (by norm_num) (by linarith [hb.1]) 0
      (d.left_carrier_facet_zero t ht 0 hU0 hT0 b hb)
    intro i hi hne
    fin_cases i
    · exact (hne rfl).elim
    · exact (hother hi).elim
    · exact hneg
  · obtain ⟨b, hb, hother⟩ := d.left_carrier_nonzero_right_facet t ht 0 hW0 hU0
    apply d.unique_facet_amplitude_ge_one t h 1 b (by norm_num) (by linarith [hb.1]) 1
      (d.right_carrier_facet_zero t ht 1 hU1 hV1 b hb)
    intro i hi hne
    fin_cases i
    · exact (hother hi).elim
    · exact (hne rfl).elim
    · exact hneg

end MaxCaterpillar.Fiber.Mixed65
