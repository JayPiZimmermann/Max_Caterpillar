import MaxCaterpillar.Fiber.Count65.Mixed.ResidualDirections
import MaxCaterpillar.Fiber.Mixed65.CarrierAmplitude

/-! # Exact effective amplitudes in the exhaustive mixed residual directions

Every actual three-gate identity has two positive unit crease amplitudes and
one negative unit crease amplitude. No amplitude normalization is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier

lemma ResidualSystem.facet_jump3 (d : ResidualSystem (Fin 3)) (t : ℝ)
    (h : d.Represents t) (q b : ℝ) (hq : 0 < q) (ha : 0 < q+b) :
    (∑ i, if d.gate t i q b (q+b) = 0 then d.out i * |d.W i| else 0) = 1 := by
  have hj := local_relu_jump_balance d.W
    (fun i => d.gate t i q b (q+b)) d.out 1 d.lW
    (d.base t q b (q+b)-(q+b)) (q+b) ha
    (by simpa only [one_mul] using d.facet_local_identity t h q b hq ha)
  simpa only [Finset.sum_filter] using hj

lemma ResidualSystem.spurious_jump3 (d : ResidualSystem (Fin 3)) (t : ℝ)
    (h : d.Represents t) (q b c : ℝ) (hc : 0 < c)
    (hneq : c ≠ max (q+b) b) :
    (∑ i, if d.gate t i q b c = 0 then d.out i * |d.W i| else 0) = 0 := by
  obtain ⟨δ,u,v,hδ,hloc⟩ := target_affine_near q b c hc hneq
  have hident : ∀ s : ℝ, |s| < δ →
      (0:ℝ) * relu s = (d.lW-u)*s + (d.base t q b c-v) +
        ∑ i, d.out i * relu (d.W i*s+d.gate t i q b c) := by
    intro s hs
    obtain ⟨hcs,htarget⟩ := hloc s hs
    have hh := h q b (c+s)
    rw [htarget] at hh
    have hbase := form_shift_last t d.lU d.lV d.lW d.lT q b c s hc.le hcs
    change d.base t q b (c+s) = d.lW*s+d.base t q b c at hbase
    have hgate : ∀ i, d.gate t i q b (c+s) = d.W i*s+d.gate t i q b c :=
      fun i => form_shift_last t (d.U i) (d.V i) (d.W i) (d.T i) q b c s hc.le hcs
    simp_rw [hbase,hgate] at hh
    linear_combination hh
  have hj := local_relu_jump_balance d.W
    (fun i => d.gate t i q b c) d.out 0 (d.lW-u)
    (d.base t q b c-v) δ hδ hident
  simpa only [Finset.sum_filter] using hj

private lemma nonzero_mul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  mul_ne_zero ha hb

/-- Unit amplitudes in branch A follow from two unique target creases and
one shared spurious crease. -/
theorem ResidualSystem.amplitudes_A (d : ResidualSystem (Fin 3)) (t k : ℝ)
    (ht : 0 < t) (hk : 1 ≤ t*k) (h : d.Represents t)
    (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0) (hW2 : d.W 2 ≠ 0)
    (hd : d.HasADirections t k) :
    d.out 0 * |d.W 0| = 1 ∧ d.out 1 * |d.W 1| = 1 ∧
      d.out 2 * |d.W 2| = -1 := by
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  have hk0 : 0 < k := by
    by_contra hn
    have hm : t*k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hn)
    linarith
  have evals_left :
      d.gate t 0 1 (-(1/2)) (1/2) = 0 ∧
      d.gate t 1 1 (-(1/2)) (1/2) = d.W 1 * (t*k+(k-1)/2) ∧
      d.gate t 2 1 (-(1/2)) (1/2) = d.W 2 * (k*(t+1/2)) := by
    simp only [ResidualSystem.gate, form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos (by norm_num : (-(1/2):ℝ) ≤ 0),
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t*1-(-(1/2)))]
    constructor <;> [ring; constructor <;> ring]
  have hleft1 : d.gate t 1 1 (-(1/2)) (1/2) ≠ 0 := by
    rw [evals_left.2.1]
    exact mul_ne_zero hW1 (ne_of_gt (by linarith : 0 < t*k+(k-1)/2))
  have hleft2 : d.gate t 2 1 (-(1/2)) (1/2) ≠ 0 := by
    rw [evals_left.2.2]
    exact mul_ne_zero hW2 (mul_ne_zero hk0.ne' (ne_of_gt (by linarith : 0 < t+1/2)))
  have h0 := d.facet_jump3 t h 1 (-(1/2)) (by norm_num) (by norm_num)
  norm_num [Fin.sum_univ_succ,evals_left.1,hleft1,hleft2] at h0
  have evals_right :
      d.gate t 0 1 (t+1) (t+2) = d.W 0 ∧
      d.gate t 1 1 (t+1) (t+2) = 0 ∧
      d.gate t 2 1 (t+1) (t+2) = d.W 2 := by
    simp only [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t+1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t+2),
      relu_of_nonpos (by linarith : t*1-(t+1) ≤ (0:ℝ))]
    constructor <;> [ring; constructor <;> ring]
  have h1 := d.facet_jump3 t h 1 (t+1) (by norm_num) (by linarith)
  rw [show 1+(t+1) = t+2 by ring] at h1
  norm_num [Fin.sum_univ_succ,evals_right.1,evals_right.2.1,evals_right.2.2,hW0,hW2] at h1
  have evals_spurious :
      d.gate t 0 1 (t+1) (1+t) = 0 ∧
      d.gate t 1 1 (t+1) (1+t) = -d.W 1 ∧
      d.gate t 2 1 (t+1) (1+t) = 0 := by
    simp only [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t+1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ 1+t),
      relu_of_nonpos (by linarith : t*1-(t+1) ≤ (0:ℝ))]
    constructor <;> [ring; constructor <;> ring]
  have h2 := d.spurious_jump3 t h 1 (t+1) (1+t) (by linarith)
    (by rw [max_eq_left (by linarith : t+1 ≤ 1+(t+1))]; linarith)
  norm_num [Fin.sum_univ_succ,evals_spurious.1,evals_spurious.2.1,
    evals_spurious.2.2,hW1] at h2
  exact ⟨h0,h1,by linarith only [h0,h2]⟩

/-- The same three crease balances determine all amplitudes in branch B. -/
theorem ResidualSystem.amplitudes_B (d : ResidualSystem (Fin 3)) (t r : ℝ)
    (ht : 0 < t) (hr : 1+t ≤ t*r) (h : d.Represents t)
    (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0) (hW2 : d.W 2 ≠ 0)
    (hd : d.HasBDirections t r) :
    d.out 0 * |d.W 0| = 1 ∧ d.out 1 * |d.W 1| = 1 ∧
      d.out 2 * |d.W 2| = -1 := by
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  have hr0 : 1 < r := by nlinarith only [ht,hr]
  have evals_left :
      d.gate t 0 1 (-(1/2)) (1/2) = 0 ∧
      d.gate t 1 1 (-(1/2)) (1/2) = -d.W 1 / 2 ∧
      d.gate t 2 1 (-(1/2)) (1/2) = -d.W 2 / 2 := by
    simp only [ResidualSystem.gate, form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos (by norm_num : (-(1/2):ℝ) ≤ 0),
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t*1-(-(1/2)))]
    constructor <;> [ring; constructor <;> ring]
  have hleft1 : d.gate t 1 1 (-(1/2)) (1/2) ≠ 0 := by
    rw [evals_left.2.1]
    exact div_ne_zero (neg_ne_zero.mpr hW1) (by norm_num)
  have hleft2 : d.gate t 2 1 (-(1/2)) (1/2) ≠ 0 := by
    rw [evals_left.2.2]
    exact div_ne_zero (neg_ne_zero.mpr hW2) (by norm_num)
  have h0 := d.facet_jump3 t h 1 (-(1/2)) (by norm_num) (by norm_num)
  norm_num [Fin.sum_univ_succ,evals_left.1,hleft1,hleft2] at h0
  have evals_right :
      d.gate t 0 1 (t+1) (t+2) = d.W 0 * (1+r*(t+1)) ∧
      d.gate t 1 1 (t+1) (t+2) = 0 ∧
      d.gate t 2 1 (t+1) (t+2) = d.W 2 * (r*(t+1)) := by
    simp only [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t+1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t+2),
      relu_of_nonpos (by linarith : t*1-(t+1) ≤ (0:ℝ))]
    constructor <;> [ring; constructor <;> ring]
  have hright0 : d.gate t 0 1 (t+1) (t+2) ≠ 0 := by
    rw [evals_right.1]
    exact mul_ne_zero hW0 (ne_of_gt (by nlinarith only [hr0,ht] : 0 < 1+r*(t+1)))
  have hright2 : d.gate t 2 1 (t+1) (t+2) ≠ 0 := by
    rw [evals_right.2.2]
    exact mul_ne_zero hW2 (mul_ne_zero (ne_of_gt (by linarith : 0 < r))
      (ne_of_gt (by linarith : 0 < t+1)))
  have h1 := d.facet_jump3 t h 1 (t+1) (by norm_num) (by linarith)
  rw [show 1+(t+1) = t+2 by ring] at h1
  norm_num [Fin.sum_univ_succ,evals_right.2.1,hright0,hright2] at h1
  have evals_spurious :
      d.gate t 0 1 (-1) 1 = d.W 0 ∧
      d.gate t 1 1 (-1) 1 = 0 ∧
      d.gate t 2 1 (-1) 1 = 0 := by
    simp only [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos (by norm_num : (-1:ℝ) ≤ 0),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ t*1-(-1))]
    constructor <;> [ring; constructor <;> ring]
  have h2 := d.spurious_jump3 t h 1 (-1) 1 (by norm_num)
    (by norm_num)
  norm_num [Fin.sum_univ_succ,evals_spurious.1,evals_spurious.2.1,
    evals_spurious.2.2,hW0] at h2
  exact ⟨h0,h1,by linarith only [h1,h2]⟩

/-- Unit amplitudes are derived for every projectively classified residual. -/
theorem ResidualSystem.amplitudes_of_projective_normal_form
    (d : ResidualSystem (Fin 3)) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0) (hW2 : d.W 2 ≠ 0)
    (hn : (∃ k : ℝ, 1 ≤ t*k ∧ d.HasADirections t k) ∨
      (∃ r : ℝ, 1+t ≤ t*r ∧ d.HasBDirections t r)) :
    d.out 0 * |d.W 0| = 1 ∧ d.out 1 * |d.W 1| = 1 ∧
      d.out 2 * |d.W 2| = -1 := by
  rcases hn with ⟨k,hk,hd⟩ | ⟨r,hr,hd⟩
  · exact d.amplitudes_A t k ht hk h hW0 hW1 hW2 hd
  · exact d.amplitudes_B t r ht hr h hW0 hW1 hW2 hd

end MaxCaterpillar.Fiber.Mixed65
