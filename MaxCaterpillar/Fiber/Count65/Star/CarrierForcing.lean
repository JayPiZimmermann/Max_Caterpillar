import MaxCaterpillar.Fiber.Star65.Clipping
import MaxCaterpillar.Fiber.Mixed65.CarrierForcing

/-! # Positive-path residuals need three genuine gates

The coefficient record is shared with the mixed-dictionary development, while
all functions below use the actual positive-path features. No carrier roles,
output signs, or residual normal forms are assumed in `RepresentsStar`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65

abbrev CoefficientSystem := Mixed65.ResidualSystem

noncomputable def starBase {ι : Type*} (d : CoefficientSystem ι) (r q b c : ℝ) : ℝ :=
  starLinearForm r d.lU d.lV d.lW d.lT q b c

noncomputable def starGate {ι : Type*} (d : CoefficientSystem ι)
    (r : ℝ) (i : ι) (q b c : ℝ) : ℝ :=
  starLinearForm r (d.U i) (d.V i) (d.W i) (d.T i) q b c

def RepresentsStar {ι : Type*} [Fintype ι] (d : CoefficientSystem ι) (r : ℝ) : Prop :=
  ∀ q b c : ℝ, max (max 0 (q + b)) (max b (relu c)) =
    starBase d r q b c + ∑ i, d.out i * relu (starGate d r i q b c)

lemma star_shift_last (r A B C D q b c s : ℝ) (hc : 0 ≤ c) (hcs : 0 ≤ c + s) :
    starLinearForm r A B C D q b (c + s) =
      C * s + starLinearForm r A B C D q b c := by
  unfold starLinearForm
  rw [max_eq_right hc, max_eq_right hcs]
  ring

private lemma max_shift_relu (a s : ℝ) : max a (a + s) = a + relu s := by
  rcases le_total 0 s with hs | hs
  · rw [relu_of_nonneg hs, max_eq_right (by linarith)]
  · rw [relu_of_nonpos hs, max_eq_left (by linarith), add_zero]

lemma target_star_eq_mixed {q b c : ℝ} (hb : 0 ≤ b) :
    max (max 0 (q + b)) (max b (relu c)) = max (max (q + b) b) (relu c) := by
  calc
    _ = max (max 0 (max (q + b) b)) (relu c) := by ac_rfl
    _ = _ := by rw [max_eq_right (hb.trans (le_max_right _ _))]

/-- Each open top facet has a positive output gate vanishing with nonzero
independent-coordinate slope. -/
theorem positive_gate_on_facet {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (H : RepresentsStar d r)
    (q b : ℝ) (hq : 0 < q) (ha : 0 < q + b) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧ starGate d r i q b (q + b) = 0 := by
  apply exists_positive_active_zero_gate d.W (fun i => starGate d r i q b (q + b)) d.out
    d.lW (starBase d r q b (q + b) - (q + b)) (q + b) ha
  intro s hs
  have hcs : 0 ≤ (q + b) + s := by linarith [(abs_lt.mp hs).1]
  have hh := H q b ((q + b) + s)
  rw [max_eq_right ha.le, ← max_assoc, max_eq_left (by linarith : b ≤ q + b),
    relu_of_nonneg hcs, max_shift_relu] at hh
  have hb0 := star_shift_last r d.lU d.lV d.lW d.lT q b (q + b) s ha.le hcs
  have hgi : ∀ i, starGate d r i q b ((q + b) + s) =
      d.W i * s + starGate d r i q b (q + b) := fun i =>
    star_shift_last r (d.U i) (d.V i) (d.W i) (d.T i) q b (q + b) s ha.le hcs
  change starBase d r q b ((q + b) + s) = d.lW * s + starBase d r q b (q + b) at hb0
  simp_rw [hb0, hgi] at hh
  linarith only [hh]

/-- The left carrier is forced on `q=1,-1<b<0`; all coefficients are real. -/
theorem exists_left_carrier {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧
      d.U i + d.W i + d.T i = 0 ∧ d.W i + r * d.T i = 0 := by
  have hcover : ∀ b ∈ Set.Ioo (-1 : ℝ) 0,
      ∃ i, (0 < d.out i ∧ d.W i ≠ 0) ∧
        (d.U i + d.W i + d.T i) + (d.W i + r * d.T i) * b = 0 := by
    intro b hb
    obtain ⟨i, hi, hW, hz⟩ := positive_gate_on_facet d r H 1 b
      (by norm_num) (by linarith [hb.1])
    refine ⟨i, ⟨hi, hW⟩, ?_⟩
    have ht : 0 ≤ 1 + r * b := by nlinarith only [hr1, hb.1, hb.2, hr]
    simp only [starGate, starLinearForm,
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_eq_left hb.2.le,
      max_eq_right (by linarith [hb.1] : (0 : ℝ) ≤ 1 + b),
      max_eq_right ht] at hz
    nlinarith only [hz]
  obtain ⟨i, ⟨hi, hW⟩, hU, hT⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => d.U i + d.W i + d.T i) (fun i => d.W i + r * d.T i)
    (fun i => 0 < d.out i ∧ d.W i ≠ 0) (by norm_num : (-1 : ℝ) < 0) hcover
  exact ⟨i, hi, hW, hU, hT⟩

/-- The independent right facet forces zero fourth-feature coefficient. -/
theorem exists_right_carrier {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r)
    (H : RepresentsStar d r) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧ d.T i = 0 ∧ d.V i + d.W i = 0 := by
  have hcover : ∀ A ∈ Set.Ioo (0 : ℝ) 1,
      ∃ i, (0 < d.out i ∧ d.W i ≠ 0) ∧
        (d.V i + d.W i) + (r * d.T i) * A = 0 := by
    intro A hA
    have hq : r * (A - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith [hA.2])
    have ht : 0 ≤ r * (A - 1) + r * 1 := by nlinarith only [mul_pos hr hA.1]
    have haffine : ∀ s : ℝ, |s| < 1 →
        relu s = d.lW * s + (starBase d r (r * (A - 1)) 1 1 - 1) +
          ∑ i, d.out i * relu (d.W i * s + starGate d r i (r * (A - 1)) 1 1) := by
      intro s hs
      have hcs : 0 ≤ 1 + s := by linarith [(abs_lt.mp hs).1]
      have he := H (r * (A - 1)) 1 (1 + s)
      rw [target_star_eq_mixed (by norm_num),
        max_eq_right (by linarith only [hq] : r * (A - 1) + 1 ≤ 1),
        relu_of_nonneg hcs, max_shift_relu] at he
      have hbase := star_shift_last r d.lU d.lV d.lW d.lT
        (r * (A - 1)) 1 1 s (by norm_num) hcs
      change starBase d r (r * (A - 1)) 1 (1 + s) =
        d.lW * s + starBase d r (r * (A - 1)) 1 1 at hbase
      have hgate : ∀ i, starGate d r i (r * (A - 1)) 1 (1 + s) =
        d.W i * s + starGate d r i (r * (A - 1)) 1 1 := fun i =>
          star_shift_last r (d.U i) (d.V i) (d.W i) (d.T i)
            (r * (A - 1)) 1 1 s (by norm_num) hcs
      simp_rw [hbase, hgate] at he
      linarith only [he]
    obtain ⟨i, hi, hW, hz⟩ := exists_positive_active_zero_gate d.W
      (fun i => starGate d r i (r * (A - 1)) 1 1) d.out d.lW
      (starBase d r (r * (A - 1)) 1 1 - 1) 1 (by norm_num) haffine
    refine ⟨i, ⟨hi, hW⟩, ?_⟩
    simp only [starGate, starLinearForm, max_eq_left hq,
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_eq_right ht] at hz
    nlinarith only [hz]
  obtain ⟨i, ⟨hi, hW⟩, hv, ht⟩ := Mixed65.exists_zero_affine_of_interval_cover_fintype
    (fun i => d.V i + d.W i) (fun i => r * d.T i)
    (fun i => 0 < d.out i ∧ d.W i ≠ 0) (by norm_num : (0 : ℝ) < 1) hcover
  exact ⟨i, hi, hW, (mul_eq_zero.mp ht).resolve_left (ne_of_gt hr), hv⟩

/-- Every representation needs two distinct positive-output terms. -/
theorem two_positive_carriers {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) :
    ∃ i j, i ≠ j ∧ 0 < d.out i ∧ 0 < d.out j ∧ d.W i ≠ 0 ∧ d.W j ≠ 0 := by
  obtain ⟨i, hi, hiW, hiU, hiT⟩ := exists_left_carrier d r hr hr1 H
  obtain ⟨j, hj, hjW, hjT, hjV⟩ := exists_right_carrier d r hr H
  refine ⟨i, j, ?_, hi, hj, hiW, hjW⟩
  intro hij
  subst j
  rw [hjT, mul_zero, add_zero] at hiT
  exact hiW hiT

/-- The left carrier always has a spurious crease where the target is affine. -/
theorem left_carrier_spurious {ι : Type*} (d : CoefficientSystem ι)
    (r : ℝ) (hr : 0 < r) (i : ι) (hW : d.W i ≠ 0)
    (hU : d.U i + d.W i + d.T i = 0) (hT : d.W i + r * d.T i = 0) :
    ∃ q b c : ℝ, 0 < b ∧ 0 < c ∧ c ≠ max (q + b) b ∧ starGate d r i q b c = 0 := by
  by_cases hV : d.V i = 0
  · refine ⟨-r / 2, 1, 1 / 2, by norm_num, by norm_num, ?_, ?_⟩
    · rw [max_eq_right (by linarith only [hr] : -r / 2 + 1 ≤ 1)]
      norm_num
    · have hq : -r / 2 ≤ 0 := by linarith only [hr]
      have ht : 0 ≤ -r / 2 + r * 1 := by linarith only [hr]
      simp only [starGate, starLinearForm, hV, max_eq_left hq,
        max_eq_right ht, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      nlinarith only [hT]
  · let v : ℝ := -d.V i / d.W i
    have hv : v * d.W i = -d.V i := div_mul_cancel _ hW
    have hv0 : v ≠ 0 := div_ne_zero (neg_ne_zero.mpr hV) hW
    let q : ℝ := 2 + |1 + v|
    let c : ℝ := q + 1 + v
    have hq : 0 < q := by dsimp [q]; linarith only [abs_nonneg (1 + v)]
    have hc : 0 < c := by dsimp [c, q]; linarith only [neg_le_abs_self (1 + v)]
    refine ⟨q, 1, c, by norm_num, hc, ?_, ?_⟩
    · rw [max_eq_left (by linarith only [hq] : (1 : ℝ) ≤ q + 1)]
      intro he
      exact hv0 (by dsimp [c] at he; linarith only [he])
    · have ht : 0 ≤ q + r * 1 := by linarith only [hq, hr]
      simp only [starGate, starLinearForm, max_eq_right hq.le,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_eq_right hc.le,
        max_eq_right ht]
      calc
        _ = (d.U i + d.W i + d.T i) * q +
            (d.W i + r * d.T i) + (d.V i + v * d.W i) := by
              dsimp only [c]
              ring
        _ = 0 := by rw [hU, hT, hv]; ring

/-- A third, negative-output term is forced by an actual spurious crease. -/
theorem exists_negative_active_gate {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) : ∃ i, d.out i < 0 ∧ d.W i ≠ 0 := by
  obtain ⟨i, hi, hW, hU, hT⟩ := exists_left_carrier d r hr hr1 H
  obtain ⟨q, b, c, hb, hc, hneq, hz⟩ := left_carrier_spurious d r hr i hW hU hT
  obtain ⟨δ, u, v, hδ, hloc⟩ := Mixed65.target_affine_near q b c hc hneq
  have hid : ∀ s : ℝ, |s| < δ →
      (∑ j, d.out j * relu (d.W j * s + starGate d r j q b c)) =
        (u - d.lW) * s + (v - starBase d r q b c) := by
    intro s hs
    obtain ⟨hcs, htarget⟩ := hloc s hs
    have he := H q b (c + s)
    rw [target_star_eq_mixed hb.le, htarget] at he
    have hbase := star_shift_last r d.lU d.lV d.lW d.lT q b c s hc.le hcs
    change starBase d r q b (c + s) = d.lW * s + starBase d r q b c at hbase
    have hgate : ∀ j, starGate d r j q b (c + s) =
        d.W j * s + starGate d r j q b c := fun j =>
      star_shift_last r (d.U j) (d.V j) (d.W j) (d.T j) q b c s hc.le hcs
    simp_rw [hbase, hgate] at he
    linarith only [he]
  obtain ⟨j, hj, _, hjW⟩ := exists_negative_active_zero_gate d.W
    (fun j => starGate d r j q b c) d.out (u - d.lW) (v - starBase d r q b c)
    δ hδ hid i hi hz hW
  exact ⟨j, hj, hjW⟩

/-- The sign consequence of the stronger active-gate statement. -/
theorem exists_negative_gate {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) : ∃ i, d.out i < 0 := by
  obtain ⟨j, hj, _⟩ := exists_negative_active_gate d r hr hr1 H
  exact ⟨j, hj⟩

/-- No two-gate residual over this dictionary computes Max4. This is a
floor on every arbitrary real residual system, not only normalized charts. -/
theorem residual_card_ge_three {ι : Type*} [Fintype ι]
    (d : CoefficientSystem ι) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (H : RepresentsStar d r) : 3 ≤ Fintype.card ι := by
  classical
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := two_positive_carriers d r hr hr1 H
  obtain ⟨k, hk⟩ := exists_negative_gate d r hr hr1 H
  have hik : i ≠ k := by intro he; subst k; linarith only [hi, hk]
  have hjk : j ≠ k := by intro he; subst k; linarith only [hj, hk]
  have hcard : ({i,j,k} : Finset ι).card = 3 := by simp [hij,hik,hjk]
  have hle := Finset.card_le_of_subset (Finset.subset_univ ({i,j,k} : Finset ι))
  simpa only [hcard, Finset.card_univ] using hle

end MaxCaterpillar.Fiber.Count65.Star
