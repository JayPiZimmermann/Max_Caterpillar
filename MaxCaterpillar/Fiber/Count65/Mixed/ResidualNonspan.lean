import MaxCaterpillar.Fiber.Count65.Mixed.ResidualAmplitudes
import MaxCaterpillar.Fiber.Count65.Mixed.SignDomains

/-! # Two opposite feature rays exclude a remainder in the core span

This replaces a determinant calculation by the scalar identity
`relu u + relu (-u) = abs u`. The argument concerns actual all-input
residual systems, including arbitrary original gate orientations.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open BigOperators MaxCaterpillar.Frontier

@[simp] private lemma fin3_mk_zero (h : 0 < 3) : (⟨0,h⟩ : Fin 3) = 0 := by rfl
@[simp] private lemma fin3_mk_one (h : 1 < 3) : (⟨1,h⟩ : Fin 3) = 1 := by rfl
@[simp] private lemma fin3_mk_two (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := by rfl

/-- A unit target on opposite rays is incompatible with unit total crease
amplitude when the linear remainder obeys the same opposite-ray relation. -/
lemma opposite_ray_remainder_contradiction {ι : Type*} [Fintype ι]
    (a B₀ B₁ : ℝ) (w d s : ι → ℝ) (ha : 0 < a)
    (hB₀ : B₀ = ∑ i, s i*w i) (hB₁ : B₁ = ∑ i, s i*(-a*w i))
    (hx : 1 = B₀ + ∑ i, d i*relu (w i))
    (hy : a = B₁ + ∑ i, d i*relu (-a*w i))
    (hamp : (∑ i, d i*|w i|) = 1) : False := by
  have hbase : B₁ = -a*B₀ := by
    rw [hB₀,hB₁,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hneg : (∑ i, d i*relu (-a*w i)) = a * ∑ i, d i*relu (-w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show -a*w i = a*(-w i) by ring,relu_mul_pos ha]
    ring
  have habs : (∑ i, d i*relu (w i)) + (∑ i, d i*relu (-w i)) = 1 := by
    rw [← Finset.sum_add_distrib]
    simp only [← mul_add,relu_add_relu_neg_eq_abs]
    exact hamp
  rw [hbase,hneg] at hy
  have hz : a = 0 := by
    linear_combination hy + a*hx + a*habs
  exact ha.ne' hz

private lemma gate_w_ray (d : ResidualSystem (Fin 3)) (t : ℝ) (i : Fin 3) :
    d.gate t i 0 0 1 = d.W i := by
  norm_num [ResidualSystem.gate,form,relu]

/-- No linear combination of the three actual branch-A cores equals the
feature-linear remainder. All orientations and endpoint parameters are allowed. -/
theorem ResidualSystem.remainder_not_span_A
    (d : ResidualSystem (Fin 3)) (t k : ℝ) (ht : 0 < t) (hk : 1 ≤ t*k)
    (h : d.Represents t) (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0)
    (hW2 : d.W 2 ≠ 0) (hd : d.HasADirections t k) :
    ¬ ∃ s : Fin 3 → ℝ, ∀ q b c : ℝ,
      d.base t q b c = ∑ i, s i * d.gate t i q b c := by
  rintro ⟨s,hs⟩
  obtain ⟨ha0,ha1,ha2⟩ := d.amplitudes_A t k ht hk h hW0 hW1 hW2 hd
  have hamp : (∑ i, d.out i*|d.W i|) = 1 := by
    norm_num [Fin.sum_univ_succ,ha0,ha1,ha2]
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  have hm : ∀ i : Fin 3, d.gate t i 1 t 0 = -(1+t)*d.W i := by
    intro i
    fin_cases i <;> simp only [fin3_mk_zero,fin3_mk_one,fin3_mk_two] <;>
      norm_num [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
        MaxCaterpillar.relu,max_eq_right ht.le] <;> ring
  have hB₀ := hs 0 0 1
  simp only [gate_w_ray] at hB₀
  have hB₁ := hs 1 t 0
  simp_rw [hm] at hB₁
  have hx := h 0 0 1
  simp_rw [gate_w_ray] at hx
  norm_num only [zero_add,max_self,relu, max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
  have hy := h 1 t 0
  simp_rw [hm] at hy
  have htarget : max (max (1+t) t) (relu 0) = 1+t := by
    rw [max_eq_left (by linarith : t ≤ 1+t),
      relu_of_nonpos (le_refl (0:ℝ)),max_eq_left (by linarith : (0:ℝ) ≤ 1+t)]
  rw [htarget] at hy
  exact opposite_ray_remainder_contradiction (1+t) (d.base t 0 0 1)
    (d.base t 1 t 0) d.W d.out s (by linarith) hB₀ hB₁ hx hy hamp

/-- The other branch uses the other middle ray and has the same proof. -/
theorem ResidualSystem.remainder_not_span_B
    (d : ResidualSystem (Fin 3)) (t r : ℝ) (ht : 0 < t) (hr : 1+t ≤ t*r)
    (h : d.Represents t) (hW0 : d.W 0 ≠ 0) (hW1 : d.W 1 ≠ 0)
    (hW2 : d.W 2 ≠ 0) (hd : d.HasBDirections t r) :
    ¬ ∃ s : Fin 3 → ℝ, ∀ q b c : ℝ,
      d.base t q b c = ∑ i, s i * d.gate t i q b c := by
  rintro ⟨s,hs⟩
  obtain ⟨ha0,ha1,ha2⟩ := d.amplitudes_B t r ht hr h hW0 hW1 hW2 hd
  have hamp : (∑ i, d.out i*|d.W i|) = 1 := by
    norm_num [Fin.sum_univ_succ,ha0,ha1,ha2]
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  have hm : ∀ i : Fin 3, d.gate t i 1 0 0 = -(1:ℝ)*d.W i := by
    intro i
    fin_cases i <;> simp only [fin3_mk_zero,fin3_mk_one,fin3_mk_two] <;>
      norm_num [ResidualSystem.gate,form,hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2,
        MaxCaterpillar.relu,max_eq_right ht.le] <;> ring
  have hB₀ := hs 0 0 1
  simp only [gate_w_ray] at hB₀
  have hB₁ := hs 1 0 0
  simp_rw [hm] at hB₁
  have hx := h 0 0 1
  simp_rw [gate_w_ray] at hx
  norm_num only [zero_add,max_self,relu, max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
  have hy := h 1 0 0
  simp_rw [hm] at hy
  norm_num only [add_zero,relu,max_self,max_eq_left (by norm_num : (0:ℝ) ≤ 1)] at hy
  exact opposite_ray_remainder_contradiction 1 (d.base t 0 0 1)
    (d.base t 1 0 0) d.W d.out s (by norm_num) hB₀ hB₁ hx hy hamp

/-- Every actual core of branch A has full coefficient span on both signs. -/
theorem ResidualSystem.sign_spans_A (d : ResidualSystem (Fin 3)) (t k : ℝ)
    (ht : 0 < t) (hW : ∀ i, d.W i ≠ 0) (hd : d.HasADirections t k) :
    ∀ i, FormBothSignSpans t (d.U i) (d.V i) (d.W i) (d.T i) := by
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  intro i
  apply form_both_sign_spans_of_middle_a_multiple _ _ _ _ _ ht (hW i)
  fin_cases i <;> simp only [fin3_mk_zero,fin3_mk_one,fin3_mk_two]
  · erw [hU0,hV0]; ring
  · erw [hU1,hV1]; ring
  · erw [hU2,hV2]; ring

/-- Branch B uses one of the two middle rays according to the core role. -/
theorem ResidualSystem.sign_spans_B (d : ResidualSystem (Fin 3)) (t r : ℝ)
    (ht : 0 < t) (hW : ∀ i, d.W i ≠ 0) (hd : d.HasBDirections t r) :
    ∀ i, FormBothSignSpans t (d.U i) (d.V i) (d.W i) (d.T i) := by
  rcases hd with ⟨hU0,hV0,hT0,hU1,hV1,hT1,hU2,hV2,hT2⟩
  intro i
  fin_cases i
  · apply form_both_sign_spans_of_middle_b_multiple _ _ _ _ _ ht (hW 0)
    erw [hU0,hT0]
    ring
  · apply form_both_sign_spans_of_middle_a_multiple _ _ _ _ _ ht (hW 1)
    erw [hU1,hV1]
    ring
  · apply form_both_sign_spans_of_middle_b_multiple _ _ _ _ _ ht (hW 2)
    erw [hU2,hT2]
    ring

/-- The actual residual identities supply all span inputs needed by the
physical lifting argument. No coefficient chart is assumed. -/
theorem ResidualSystem.exists_full_span_normal_form {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (t : ℝ) (ht : 0 < t) (h : d.Represents t)
    (hcard : Fintype.card ι = 3) :
    ∃ e : Fin 3 ≃ ι, (d.reindex e).Represents t ∧
      0 < (d.reindex e).out 0 ∧ 0 < (d.reindex e).out 1 ∧ (d.reindex e).out 2 < 0 ∧
      (∀ i, FormBothSignSpans t ((d.reindex e).U i) ((d.reindex e).V i)
        ((d.reindex e).W i) ((d.reindex e).T i)) ∧
      ¬ (∃ s : Fin 3 → ℝ, ∀ q b c : ℝ, (d.reindex e).base t q b c =
        ∑ i, s i * (d.reindex e).gate t i q b c) := by
  obtain ⟨e,he,h0,h1,h2,hW0,hW1,hW2,hbranches⟩ :=
    d.exists_projective_normal_form t ht h hcard
  have hW : ∀ i, (d.reindex e).W i ≠ 0 := by
    intro i
    fin_cases i <;> assumption
  refine ⟨e,he,h0,h1,h2,?_⟩
  rcases hbranches with ⟨k,hk,hd⟩ | ⟨r,hr,hd⟩
  · exact ⟨(d.reindex e).sign_spans_A t k ht hW hd,
      (d.reindex e).remainder_not_span_A t k ht hk he hW0 hW1 hW2 hd⟩
  · exact ⟨(d.reindex e).sign_spans_B t r ht hW hd,
      (d.reindex e).remainder_not_span_B t r ht hr he hW0 hW1 hW2 hd⟩

end MaxCaterpillar.Fiber.Mixed65
