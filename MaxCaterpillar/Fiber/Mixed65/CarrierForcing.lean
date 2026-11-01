import MaxCaterpillar.Fiber.PositiveKink
import MaxCaterpillar.Fiber.KinkCancellation
import MaxCaterpillar.Fiber.Mixed65.Clipping
import MaxCaterpillar.Fiber.Mixed65.LinearCover
import Mathlib.Data.Finset.Card

/-! # Positive carrier directions forced by an arbitrary mixed residual identity

The hypotheses quantify over every real input. The preactivations and output
weights are arbitrary; no residual chart or gate signs are assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators MaxCaterpillar.Frontier

structure ResidualSystem (ι : Type*) where
  lU : ℝ
  lV : ℝ
  lW : ℝ
  lT : ℝ
  out : ι → ℝ
  U : ι → ℝ
  V : ι → ℝ
  W : ι → ℝ
  T : ι → ℝ

noncomputable def ResidualSystem.base {ι : Type*} (d : ResidualSystem ι)
    (t q b c : ℝ) : ℝ := form t d.lU d.lV d.lW d.lT q b c

noncomputable def ResidualSystem.gate {ι : Type*} (d : ResidualSystem ι)
    (t : ℝ) (i : ι) (q b c : ℝ) : ℝ := form t (d.U i) (d.V i) (d.W i) (d.T i) q b c

def ResidualSystem.Represents {ι : Type*} [Fintype ι] (d : ResidualSystem ι)
    (t : ℝ) : Prop := ∀ q b c : ℝ,
  max (max (q + b) b) (relu c) = d.base t q b c + ∑ i, d.out i * relu (d.gate t i q b c)

theorem form_shift_last (t A B C D q b c s : ℝ) (hc : 0 ≤ c) (hcs : 0 ≤ c + s) :
    form t A B C D q b (c + s) = C * s + form t A B C D q b c := by
  unfold form
  rw [relu_of_nonneg hc, relu_of_nonneg hcs]
  ring

private lemma max_shift_relu (a s : ℝ) : max a (a + s) = a + relu s := by
  rcases le_total 0 s with hs | hs
  · rw [relu_of_nonneg hs, max_eq_right (by linarith)]
  · rw [relu_of_nonpos hs, max_eq_left (by linarith), add_zero]

/-- Every open top facet carries a nontrivial positive gate. -/
theorem ResidualSystem.positive_gate_on_facet {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (h : d.Represents t)
    (q b : ℝ) (hq : 0 < q) (ha : 0 < q + b) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧ d.gate t i q b (q + b) = 0 := by
  apply exists_positive_active_zero_gate d.W (fun i => d.gate t i q b (q + b)) d.out
    d.lW (d.base t q b (q + b) - (q + b)) (q + b) ha
  intro s hs
  have hcs : 0 ≤ (q + b) + s := by linarith [(abs_lt.mp hs).1]
  have hh := h q b ((q + b) + s)
  rw [max_eq_left (by linarith : b ≤ q + b), relu_of_nonneg hcs, max_shift_relu] at hh
  have hb0 := form_shift_last t d.lU d.lV d.lW d.lT q b (q + b) s ha.le hcs
  have hgi : ∀ i, d.gate t i q b ((q + b) + s) =
      d.W i * s + d.gate t i q b (q + b) := fun i =>
    form_shift_last t (d.U i) (d.V i) (d.W i) (d.T i) q b (q + b) s ha.le hcs
  change d.base t q b ((q + b) + s) = d.lW * s + d.base t q b (q + b) at hb0
  simp_rw [hb0, hgi] at hh
  linarith only [hh]

/-- A positive core carrying the region `q>0,b<0` has the first forced direction. -/
theorem ResidualSystem.exists_left_carrier {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧
      d.U i = -(1 + t) * d.W i ∧ d.T i = d.W i := by
  have hcover : ∀ b ∈ Set.Ioo (-1 : ℝ) 0,
      ∃ i, (0 < d.out i ∧ d.W i ≠ 0) ∧
        (d.U i + d.W i + t * d.T i) + (d.W i - d.T i) * b = 0 := by
    intro b hb
    obtain ⟨i, hi, hW, hz⟩ := d.positive_gate_on_facet t h 1 b (by norm_num) (by linarith [hb.1])
    refine ⟨i, ⟨hi, hW⟩, ?_⟩
    have hTb : 0 ≤ t * 1 - b := by linarith [hb.2]
    simp only [ResidualSystem.gate, form, relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonpos hb.2.le, relu_of_nonneg (by linarith [hb.1] : (0:ℝ) ≤ 1 + b),
      relu_of_nonneg hTb] at hz
    nlinarith only [hz]
  obtain ⟨i, ⟨hi, hW⟩, hA, hB⟩ := exists_zero_affine_of_interval_cover_fintype
    (fun i => d.U i + d.W i + t * d.T i) (fun i => d.W i - d.T i)
    (fun i => 0 < d.out i ∧ d.W i ≠ 0) (by norm_num : (-1:ℝ) < 0) hcover
  refine ⟨i, hi, hW, ?_, ?_⟩
  · have hT : d.T i = d.W i := by linarith only [hB]
    rw [hT] at hA
    nlinarith only [hA]
  · linarith only [hB]

/-- A positive core carrying the region `q>0,b>t*q` has the second forced direction. -/
theorem ResidualSystem.exists_right_carrier {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t) :
    ∃ i, 0 < d.out i ∧ d.W i ≠ 0 ∧
      d.U i = -d.W i ∧ d.V i = -d.W i := by
  have hcover : ∀ b ∈ Set.Ioo (t + 1) (t + 2),
      ∃ i, (0 < d.out i ∧ d.W i ≠ 0) ∧
        (d.U i + d.W i) + (d.V i + d.W i) * b = 0 := by
    intro b hb
    obtain ⟨i, hi, hW, hz⟩ := d.positive_gate_on_facet t h 1 b (by norm_num) (by linarith [hb.1])
    refine ⟨i, ⟨hi, hW⟩, ?_⟩
    have hTb : t * 1 - b ≤ 0 := by linarith [hb.1]
    simp only [ResidualSystem.gate, form, relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith [hb.1] : (0:ℝ) ≤ b),
      relu_of_nonneg (by linarith [hb.1] : (0:ℝ) ≤ 1 + b),
      relu_of_nonpos hTb] at hz
    nlinarith only [hz]
  obtain ⟨i, ⟨hi, hW⟩, hA, hB⟩ := exists_zero_affine_of_interval_cover_fintype
    (fun i => d.U i + d.W i) (fun i => d.V i + d.W i)
    (fun i => 0 < d.out i ∧ d.W i ≠ 0) (by linarith : t + 1 < t + 2) hcover
  exact ⟨i, hi, hW, by linarith only [hA], by linarith only [hB]⟩

/-- Every finite exact mixed residual needs two different positive-output gates. -/
theorem ResidualSystem.two_positive_carriers {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t) :
    ∃ i j, i ≠ j ∧ 0 < d.out i ∧ 0 < d.out j ∧ d.W i ≠ 0 ∧ d.W j ≠ 0 := by
  obtain ⟨i, hi, hiW, hiU, _⟩ := d.exists_left_carrier t ht h
  obtain ⟨j, hj, hjW, hjU, _⟩ := d.exists_right_carrier t ht h
  refine ⟨i, j, ?_, hi, hj, hiW, hjW⟩
  intro hij
  subst j
  have hz : t * d.W i = 0 := by nlinarith only [hiU, hjU]
  exact hiW ((mul_eq_zero.mp hz).resolve_left (ne_of_gt ht))

/-- Every left-facet carrier also has a non-target zero inside a strict
positive `W` cell. This is independent of the number of other gates. -/
theorem ResidualSystem.left_carrier_spurious {ι : Type*}
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (i : ι)
    (hW : d.W i ≠ 0) (hU : d.U i = -(1 + t) * d.W i)
    (hT : d.T i = d.W i) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ c ≠ 1 + b ∧ d.gate t i 1 b c = 0 := by
  by_cases hV : d.V i = 0
  · refine ⟨t + 1, 1 + t, by linarith, by linarith, by linarith, ?_⟩
    simp only [ResidualSystem.gate, form, hU, hV, hT, zero_mul,
      relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
      relu_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t),
      relu_of_nonpos (by linarith : t * 1 - (t + 1) ≤ 0)]
    ring
  · let r : ℝ := d.V i / d.W i
    have hr : r * d.W i = d.V i := div_mul_cancel _ hW
    have hr0 : r ≠ 0 := div_ne_zero hV hW
    have hall := (eventually_small (1 - r) (by norm_num : (0:ℝ) < 1 / 2)).and
      (Ioo_mem_nhdsWithin_Ioi (show (0:ℝ) ∈ Set.Ico 0 t from ⟨le_rfl, ht⟩))
    obtain ⟨b, hbsmall, hb0, hbt⟩ := hall.exists
    let c : ℝ := 1 + (1 - r) * b
    have hc : 0 < c := by
      dsimp [c]
      nlinarith only [(abs_lt.mp hbsmall).1]
    refine ⟨b, c, hb0, hc, ?_, ?_⟩
    · intro he
      have hz : r * b = 0 := by dsimp [c] at he; nlinarith only [he]
      exact (mul_ne_zero hr0 (ne_of_gt hb0)) hz
    · simp only [ResidualSystem.gate, form, hU, hT,
        relu_of_nonneg (by norm_num : (0:ℝ) ≤ 1), relu_of_nonneg hb0.le,
        relu_of_nonneg hc.le, relu_of_nonneg (by linarith : 0 ≤ t * 1 - b)]
      dsimp [c]
      nlinarith only [congrArg (fun z : ℝ => z * b) hr]

/-- Away from a target facet, varying the positive `W` coordinate keeps the
target affine on a genuine interval. -/
theorem target_affine_near (q b c : ℝ) (hc : 0 < c)
    (hneq : c ≠ max (q + b) b) :
    ∃ δ u v : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      0 ≤ c + s ∧ max (max (q + b) b) (relu (c + s)) = u * s + v := by
  let m := max (q + b) b
  let δ := min c |c - m| / 2
  have hdiff : 0 < |c - m| := abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hd : 0 < δ := div_pos (lt_min hc hdiff) (by norm_num)
  have hdC : δ ≤ c / 2 := by dsimp [δ]; linarith only [min_le_left c |c - m|]
  have hdM : δ ≤ |c - m| / 2 := by dsimp [δ]; linarith only [min_le_right c |c - m|]
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · refine ⟨δ, 0, m, hd, ?_⟩
    intro s hs
    obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
    have hcs : 0 ≤ c + s := by linarith only [hs1, hdC, hc]
    refine ⟨hcs, ?_⟩
    have hmc : c + s ≤ m := by
      rw [abs_of_neg (sub_neg.mpr hlt)] at hdM
      linarith only [hs2, hdM, hlt]
    rw [relu_of_nonneg hcs, max_eq_left hmc, zero_mul, zero_add]
  · refine ⟨δ, 1, c, hd, ?_⟩
    intro s hs
    obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
    have hcs : 0 ≤ c + s := by linarith only [hs1, hdC, hc]
    refine ⟨hcs, ?_⟩
    have hmc : m ≤ c + s := by
      rw [abs_of_pos (sub_pos.mpr hgt)] at hdM
      linarith only [hs1, hdM, hgt]
    rw [relu_of_nonneg hcs, max_eq_right hmc, one_mul]
    ring

/-- The unavoidable extra crease of a left carrier forces a negative-output
gate in every finite residual identity. -/
theorem ResidualSystem.exists_negative_gate {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t) :
    ∃ i, d.out i < 0 := by
  obtain ⟨i, hi, hW, hU, hT⟩ := d.exists_left_carrier t ht h
  obtain ⟨b, c, hb, hc, hneq, hz⟩ := d.left_carrier_spurious t ht i hW hU hT
  have hmax : max (1 + b) b = 1 + b := max_eq_left (by linarith)
  obtain ⟨δ, u, v, hδ, hloc⟩ := target_affine_near 1 b c hc (by rwa [hmax])
  have hidentity : ∀ s : ℝ, |s| < δ →
      (∑ j, d.out j * relu (d.W j * s + d.gate t j 1 b c)) =
        (u - d.lW) * s + (v - d.base t 1 b c) := by
    intro s hs
    obtain ⟨hcs, htarget⟩ := hloc s hs
    have hh := h 1 b (c + s)
    rw [htarget] at hh
    have hbase := form_shift_last t d.lU d.lV d.lW d.lT 1 b c s hc.le hcs
    change d.base t 1 b (c + s) = d.lW * s + d.base t 1 b c at hbase
    have hgate : ∀ j, d.gate t j 1 b (c + s) = d.W j * s + d.gate t j 1 b c :=
      fun j => form_shift_last t (d.U j) (d.V j) (d.W j) (d.T j) 1 b c s hc.le hcs
    simp_rw [hbase, hgate] at hh
    nlinarith only [hh]
  obtain ⟨j, hj, _, _⟩ := exists_negative_active_zero_gate d.W
    (fun j => d.gate t j 1 b c) d.out (u - d.lW) (v - d.base t 1 b c)
    δ hδ hidentity i hi hz hW
  exact ⟨j, hj⟩

/-- Arbitrary real residuals over the mixed four-feature dictionary require
at least three ReLU terms. The output signs were not assumed. -/
theorem ResidualSystem.card_ge_three {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t) :
    3 ≤ Fintype.card ι := by
  classical
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := d.two_positive_carriers t ht h
  obtain ⟨k, hk⟩ := d.exists_negative_gate t ht h
  have hik : i ≠ k := by intro he; subst k; linarith only [hi, hk]
  have hjk : j ≠ k := by intro he; subst k; linarith only [hj, hk]
  have hcard : ({i, j, k} : Finset ι).card = 3 := by simp [hij, hik, hjk]
  have hle := Finset.card_le_of_subset (Finset.subset_univ ({i, j, k} : Finset ι))
  simpa only [hcard, Finset.card_univ] using hle

end MaxCaterpillar.Fiber.Mixed65
