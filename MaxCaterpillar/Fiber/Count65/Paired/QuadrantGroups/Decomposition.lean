import MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

/-! # An explicit finite decomposition by positive crossing rays

The finite set of rays is computed from the original coefficients. Each ray
contributes one linear form, and every remaining gate is either nonnegative
linear or dormant on the quadrant. No connectivity conclusion is assumed.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups

open BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def crossingSlots (a b : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => a i*b i < 0)

noncomputable def knotLocations (a b : ι → ℝ) : Finset ℝ :=
  (crossingSlots a b).image (fun i => -b i/a i)

noncomputable def crossingGroup (a b : ι → ℝ) (τ : ℝ) : Finset ι :=
  (crossingSlots a b).filter (fun i => -b i/a i = τ)

theorem rayKey_eq_of_vanish (a b τ : ℝ) (ha : a ≠ 0)
    (hz : a*τ+b = 0) : -b/a = τ := by
  apply (div_eq_iff ha).mpr
  linarith only [hz]

theorem knotLocations_positive (a b : ι → ℝ) (τ : ℝ)
    (hτ : τ ∈ knotLocations a b) : 0 < τ := by
  classical
  rcases Finset.mem_image.mp hτ with ⟨i,hi,rfl⟩
  rcases (Connected64.crossing_iff_positive_knot (a i) (b i)).mp
    (Finset.mem_filter.mp hi).2 with ⟨σ,hσ,ha,hz⟩
  rw [rayKey_eq_of_vanish _ _ _ ha hz]
  exact hσ

/-- Removing only zero rows from the original knot group gives its fiber in
the finite partition by crossing rays. -/
theorem crossingGroup_eq (a b : ι → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    crossingGroup a b τ = (knotGroup a b τ).filter (fun i => a i ≠ 0) := by
  classical
  apply Finset.ext
  intro i
  simp only [crossingGroup,crossingSlots,knotGroup,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hab,hkey⟩
    have ha : a i ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at hab
      exact (lt_irrefl 0) hab
    have hmul := (div_eq_iff ha).mp hkey
    exact ⟨by linarith only [hmul],ha⟩
  · rintro ⟨hz,ha⟩
    exact ⟨(Connected64.crossing_iff_positive_knot _ _).mpr ⟨τ,hτ,ha,hz⟩,
      rayKey_eq_of_vanish _ _ _ ha hz⟩

theorem crossingGroup_linear (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i*max 0 (a i*Q+b i*N)) = Q-N) (Q N : ℝ) :
    (∑ i in crossingGroup a b τ, d i*max 0 (a i*Q+b i*N)) =
      (∑ i in crossingGroup a b τ, d i*max 0 (a i))*(Q-τ*N) := by
  classical
  apply finite_aligned_group_linear
  · intro i hi
    rw [crossingGroup_eq a b τ hτ] at hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  · rw [crossingGroup_eq a b τ hτ,Finset.sum_filter]
    have hjump := knotGroup_jump_zero a b d τ hτ hfit
    convert hjump using 1
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases ha : a i = 0 <;> simp [ha]

theorem crossingGroup_coefficient_eq (a b d : ι → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (∑ i in crossingGroup a b τ, d i*max 0 (a i)) = groupCoefficient a b d τ := by
  classical
  rw [crossingGroup_eq a b τ hτ,Finset.sum_filter]
  unfold groupCoefficient
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases ha : a i = 0 <;> simp [ha]

/-- All crossing gates, grouped over the actual finite set of distinct rays,
are a sum of linear forms. This includes any number of coincident knots. -/
theorem finite_crossing_decomposition (a b d : ι → ℝ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i*max 0 (a i*Q+b i*N)) = Q-N) (Q N : ℝ) :
    (∑ i in crossingSlots a b, d i*max 0 (a i*Q+b i*N)) =
      ∑ τ in knotLocations a b,
        (∑ i in crossingGroup a b τ, d i*max 0 (a i))*(Q-τ*N) := by
  classical
  have hmap : ∀ i ∈ crossingSlots a b, -b i/a i ∈ knotLocations a b := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro τ hτ
  exact crossingGroup_linear a b d τ (knotLocations_positive a b τ hτ) hfit Q N

/-- When no ray carries a surviving linear form, all crossing outputs may be
erased together. No induction over knot groups is required. -/
theorem all_zero_crossing_groups_cancel (a b d : ι → ℝ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i*max 0 (a i*Q+b i*N)) = Q-N)
    (hzero : ∀ τ ∈ knotLocations a b, groupCoefficient a b d τ = 0) (Q N : ℝ) :
    (∑ i in crossingSlots a b, d i*max 0 (a i*Q+b i*N)) = 0 := by
  rw [finite_crossing_decomposition a b d hfit Q N]
  apply Finset.sum_eq_zero
  intro τ hτ
  rw [crossingGroup_coefficient_eq a b d τ (knotLocations_positive a b τ hτ),
    hzero τ hτ,zero_mul]

theorem noncrossing_gate_eval (a b Q N : ℝ) (hab : ¬ a*b < 0)
    (hQ : 0 ≤ Q) (hN : 0 ≤ N) :
    max 0 (a*Q+b*N) = max 0 a*Q+max 0 b*N := by
  rcases gate_classification a b with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨τ,hτ,ha,hz⟩
  · rw [max_eq_right ha,max_eq_right hb,
      max_eq_right (add_nonneg (mul_nonneg ha hQ) (mul_nonneg hb hN))]
  · rw [max_eq_left ha,max_eq_left hb,
      max_eq_left (add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha hQ)
        (mul_nonpos_of_nonpos_of_nonneg hb hN))]
    ring
  · exact False.elim (hab
      ((Connected64.crossing_iff_positive_knot a b).mpr ⟨τ,hτ,ha,hz⟩))

/-- Exhaustive finite algebraic classification of the original homogeneous
representation: noncrossing linear/dead slots plus one linear contribution
for each distinct crossing ray. -/
theorem finite_quadrant_decomposition (a b d : ι → ℝ)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i*max 0 (a i*Q+b i*N)) = Q-N)
    (Q N : ℝ) (hQ : 0 ≤ Q) (hN : 0 ≤ N) :
    (∑ i, d i*max 0 (a i*Q+b i*N)) =
      (∑ i in Finset.univ.filter (fun i => ¬ a i*b i < 0),
        d i*(max 0 (a i)*Q+max 0 (b i)*N))+
      ∑ τ in knotLocations a b,
        (∑ i in crossingGroup a b τ, d i*max 0 (a i))*(Q-τ*N) := by
  classical
  rw [← finite_crossing_decomposition a b d hfit Q N]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (fun i => a i*b i < 0)
    (fun i => d i*max 0 (a i*Q+b i*N))
  rw [← hpartition,add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [noncrossing_gate_eval (a i) (b i) Q N (Finset.mem_filter.mp hi).2 hQ hN]

/-- In the no-effective-crossing branch, the two existing nonnegative slots
needed by the direct split chord have opposite nonzero output signs. -/
theorem no_crossing_active_signs (a b d : ι → ℝ)
    (hno : ∀ i, d i ≠ 0 → ¬ a i*b i < 0)
    (hfit : ∀ Q N : ℝ, 0 ≤ Q → 0 ≤ N →
      (∑ i, d i*max 0 (a i*Q+b i*N)) = Q-N) :
    (∃ p, 0 < d p ∧ 0 < a p ∧ 0 ≤ b p) ∧
      (∃ n, d n < 0 ∧ 0 ≤ a n ∧ 0 < b n) := by
  classical
  rcases quadrant_axis_weights a b d hfit with ⟨hA,hB⟩
  have hforms := no_crossing_normal_form a b d hno
  have hexpos : ∃ i, 0 < d i*max 0 (a i) := by
    by_contra hn
    have hall : ∀ i, d i*max 0 (a i) ≤ 0 :=
      fun i => le_of_not_gt (fun hi => hn ⟨i,hi⟩)
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun i _hi => hall i)
    linarith only [hA,hs]
  have hexneg : ∃ i, d i*max 0 (b i) < 0 := by
    by_contra hn
    have hall : ∀ i, 0 ≤ d i*max 0 (b i) :=
      fun i => le_of_not_gt (fun hi => hn ⟨i,hi⟩)
    have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _hi => hall i)
    linarith only [hB,hs]
  constructor
  · rcases hexpos with ⟨i,hi⟩
    have hdi : 0 < d i := by
      by_contra hd
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) (le_max_left 0 (a i))
      linarith only [hp,hi]
    have hai : 0 < a i := by
      by_contra ha
      rw [max_eq_left (le_of_not_gt ha),mul_zero] at hi
      exact (lt_irrefl 0) hi
    refine ⟨i,hdi,hai,?_⟩
    rcases hforms i with hd | ⟨_ha,hb⟩ | ⟨ha,_hb⟩
    · exact False.elim ((ne_of_gt hdi) hd)
    · exact hb
    · linarith only [ha,hai]
  · rcases hexneg with ⟨i,hi⟩
    have hdi : d i < 0 := by
      by_contra hd
      have hp := mul_nonneg (le_of_not_gt hd) (le_max_left 0 (b i))
      linarith only [hp,hi]
    have hbi : 0 < b i := by
      by_contra hb
      rw [max_eq_left (le_of_not_gt hb),mul_zero] at hi
      exact (lt_irrefl 0) hi
    refine ⟨i,hdi,?_,hbi⟩
    rcases hforms i with hd | ⟨ha,_hb⟩ | ⟨_ha,hb⟩
    · exact False.elim ((ne_of_lt hdi) hd)
    · exact ha
    · linarith only [hb,hbi]

end MaxCaterpillar.Fiber.Count65.Paired.QuadrantGroups
