import MaxCaterpillar.Fiber.Mixed65.Heads

/-! # Exact extraction of the affine tail of finitely many ReLUs

No activation pattern is assumed. A finite common threshold is constructed from
the actual real slopes and intercepts. Equality on the whole nonnegative ray then
identifies the eventual slope and invariant remainder exactly.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators
open MaxCaterpillar.Frontier

/-- Every finite signed sum of affine ReLUs is exactly affine after a finite
threshold, including zero slopes and zero intercepts. -/
lemma eventually_sum_relu_affine {ι : Type*} [Fintype ι] (d a C : ι → ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ z, P ≤ z →
      (∑ i, d i * relu (a i * z + C i)) =
        (∑ i, d i * relu (a i)) * z + ∑ i, d i * affineTail (a i) (C i) := by
  classical
  let p : ι → ℝ := fun i => Classical.choose (eventually_relu_affine (a i) (C i))
  have hp : ∀ i, 0 ≤ p i ∧ ∀ z, p i ≤ z →
      relu (a i * z + C i) = relu (a i) * z + affineTail (a i) (C i) :=
    fun i => Classical.choose_spec (eventually_relu_affine (a i) (C i))
  refine ⟨∑ i, p i, Finset.sum_nonneg (fun i _ => (hp i).1), ?_⟩
  intro z hz
  have hpi : ∀ i, p i ≤ z := by
    intro i
    exact (Finset.single_le_sum (fun j _ => (hp j).1) (Finset.mem_univ i)).trans hz
  calc
    (∑ i, d i * relu (a i * z + C i)) =
        ∑ i, ((d i * relu (a i)) * z + d i * affineTail (a i) (C i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hp i).2 z (hpi i)]
      ring
    _ = (∑ i, d i * relu (a i)) * z + ∑ i, d i * affineTail (a i) (C i) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Equality to an affine function on the whole nonnegative ray forces its exact
slope and intercept to agree with the finite ReLU tail. The index type may be empty. -/
theorem sum_relu_halfLine_coefficients {ι : Type*} [Fintype ι]
    (d a C : ι → ℝ) (s H : ℝ)
    (h : ∀ z : ℝ, 0 ≤ z → (∑ i, d i * relu (a i * z + C i)) = s * z + H) :
    (∑ i, d i * relu (a i)) = s ∧ (∑ i, d i * affineTail (a i) (C i)) = H := by
  obtain ⟨P, hP, he⟩ := eventually_sum_relu_affine d a C
  have h0 := h P hP
  have h1 := h (P + 1) (by linarith)
  rw [he P le_rfl] at h0
  rw [he (P + 1) (by linarith)] at h1
  have hs : (∑ i, d i * relu (a i)) = s := by nlinarith only [h0, h1]
  refine ⟨hs, ?_⟩
  rw [hs] at h0
  linarith only [h0]

lemma sum_relu_slope_eq_positive {ι : Type*} [Fintype ι] (d a : ι → ℝ) :
    (∑ i, d i * relu (a i)) = ∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : 0 < a i
  · rw [if_pos ha, relu_of_nonneg ha.le]
  · rw [if_neg ha, relu_of_nonpos (le_of_not_gt ha), mul_zero]

lemma sum_affineTail_eq_positive_zero {ι : Type*} [Fintype ι] (d a C : ι → ℝ) :
    (∑ i, d i * affineTail (a i) (C i)) =
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i) +
        ∑ i in Finset.univ.filter (fun i => a i = 0), d i * relu (C i) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : 0 < a i
  · simp only [affineTail, if_pos ha, if_neg ha.ne', add_zero]
  · by_cases hz : a i = 0
    · simp only [affineTail, if_neg ha, if_pos hz, zero_add]
    · simp only [affineTail, if_neg ha, if_neg hz, mul_zero, add_zero]

/-- The positive diagonal tail separates passing neurons from zero-slope neurons.
All parameters and all invariant states are arbitrary, and no gate consistency
hypothesis is introduced. -/
theorem finite_diagonal_extraction {ι α : Type*} [Fintype ι]
    (d a : ι → ℝ) (C : ι → α → ℝ) (H : α → ℝ) (s : ℝ)
    (h : ∀ x z, 0 ≤ z → (∑ i, d i * relu (a i * z + C i x)) = s * z + H x) :
    ∀ x,
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) = s ∧
      H x = (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in Finset.univ.filter (fun i => a i = 0), d i * relu (C i x) := by
  intro x
  obtain ⟨hs, hi⟩ := sum_relu_halfLine_coefficients d a (fun i => C i x) s (H x) (h x)
  rw [sum_relu_slope_eq_positive d a] at hs
  rw [sum_affineTail_eq_positive_zero d a (fun i => C i x)] at hi
  exact ⟨hs, hi.symm⟩

/-- If the invariant state domain is inhabited, the slope statement is global,
while the remainder identity holds on every state. -/
theorem finite_diagonal_extraction_nonempty {ι α : Type*} [Fintype ι] [Nonempty α]
    (d a : ι → ℝ) (C : ι → α → ℝ) (H : α → ℝ) (s : ℝ)
    (h : ∀ x z, 0 ≤ z → (∑ i, d i * relu (a i * z + C i x)) = s * z + H x) :
    (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) = s ∧
    ∀ x, H x = (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
      ∑ i in Finset.univ.filter (fun i => a i = 0), d i * relu (C i x) := by
  classical
  have he := finite_diagonal_extraction d a C H s h
  exact ⟨(he (Classical.choice inferInstance)).1, fun x => (he x).2⟩

/-- Apply the extraction to both translation half-lines of an actual signed-carrier
first hidden layer. The positive and negative passing slopes are `1` and `-1`. -/
theorem finite_signed_carrier_extraction {ι α : Type*} [Fintype ι] [Nonempty α]
    (d a b : ι → ℝ) (C : ι → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) = z + H x) :
    (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) = 1 ∧
    (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * b i) = -1 ∧
    ∀ x,
      (H x = (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in Finset.univ.filter (fun i => a i = 0), d i * relu (C i x)) ∧
      (H x = (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * C i x) +
        ∑ i in Finset.univ.filter (fun i => b i = 0), d i * relu (C i x)) := by
  have hp : ∀ x z, 0 ≤ z → (∑ i, d i * relu (a i * z + C i x)) = 1 * z + H x := by
    intro x z hz
    simpa only [relu_of_nonneg hz, relu_of_nonpos (neg_nonpos.mpr hz),
      mul_zero, add_zero, one_mul] using h x z
  have hn : ∀ x z, 0 ≤ z → (∑ i, d i * relu (b i * z + C i x)) = (-1) * z + H x := by
    intro x z hz
    simpa only [relu_of_nonpos (neg_nonpos.mpr hz), neg_neg, relu_of_nonneg hz,
      mul_zero, zero_add, neg_one_mul] using h x (-z)
  obtain ⟨ha, hPa⟩ := finite_diagonal_extraction_nonempty d a C H 1 hp
  obtain ⟨hb, hPb⟩ := finite_diagonal_extraction_nonempty d b C H (-1) hn
  exact ⟨ha, hb, fun x => ⟨hPa x, hPb x⟩⟩

/-- A positive total diagonal slope requires a passing neuron with positive output. -/
theorem exists_positive_passing_of_slope {ι : Type*} [Fintype ι] (d a : ι → ℝ)
    (hs : 0 < ∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) :
    ∃ i, 0 < a i ∧ 0 < d i := by
  classical
  by_contra hn
  push_neg at hn
  have hsum : (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have ha := (Finset.mem_filter.mp hi).2
    exact mul_nonpos_of_nonpos_of_nonneg (hn i ha) ha.le
  exact (not_lt_of_ge hsum hs).elim

/-- A negative total diagonal slope requires a passing neuron with negative output. -/
theorem exists_negative_passing_of_slope {ι : Type*} [Fintype ι] (d a : ι → ℝ)
    (hs : (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i) < 0) :
    ∃ i, 0 < a i ∧ d i < 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hsum : 0 ≤ ∑ i in Finset.univ.filter (fun i => 0 < a i), d i * a i := by
    apply Finset.sum_nonneg
    intro i hi
    have ha := (Finset.mem_filter.mp hi).2
    exact mul_nonneg (hn i ha) ha.le
  exact (not_lt_of_ge hsum hs).elim

end MaxCaterpillar.Fiber.Mixed65
