import MaxCaterpillar.Fiber.Mixed65.Heads

/-! # One full sign domain rigidifies two moving ReLU gates

The half-line identity is the actual identity of two original moving gates,
after their nonzero output magnitudes have been absorbed by positive scaling.
A full sign domain means that vanishing there determines a function in the
feature space. No residual chart or uniqueness comparison is needed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Mixed65

variable {α : Type*}

/-- Vanishing on the strict negative domain of C determines an E-function. -/
def DeterminesNegative (E : Submodule ℝ (α → ℝ)) (C : α → ℝ) : Prop :=
  ∀ F : α → ℝ, F ∈ E → (∀ x, C x < 0 → F x = 0) → ∀ x, F x = 0

/-- Vanishing on the strict positive domain of C determines an E-function. -/
def DeterminesPositive (E : Submodule ℝ (α → ℝ)) (C : α → ℝ) : Prop :=
  ∀ F : α → ℝ, F ∈ E → (∀ x, 0 < C x → F x = 0) → ∀ x, F x = 0

/-- A negative full-span domain of the positive-output intercept forces an
opposite pair, with slopes exactly +1 and -1. -/
theorem moving_pair_rigid_of_left (E : Submodule ℝ (α → ℝ))
    (a c : ℝ) (C Q : α → ℝ) (hC : C ∈ E) (hQ : Q ∈ E)
    (hneg : ∃ x, C x < 0) (hdet : DeterminesNegative E C)
    (h : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (a * p + C x) - relu (c * p + Q x) =
        p + (relu (C x) - relu (Q x))) :
    a = 1 ∧ c = -1 ∧ ∀ x, Q x = -C x := by
  obtain ⟨x₀, hx₀⟩ := hneg
  have hc : c < 0 := by
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exact hc
    · have hh : ∀ p : ℝ, 0 ≤ p →
          relu (a * p + C x₀) - relu (Q x₀) =
            p + (relu (C x₀) - relu (Q x₀)) := by
        simpa only [hc, zero_mul, zero_add] using h x₀
      have hh' := halfLine_zero_second a (C x₀) (Q x₀)
        (relu (C x₀) - relu (Q x₀)) hh
      linarith only [hh'.2.2, hx₀]
    · have hh := halfLine_positive_second a (C x₀) c (Q x₀)
        (relu (C x₀) - relu (Q x₀)) hc (h x₀)
      linarith only [hh.2.2.1, hx₀]
  have onNeg : ∀ x, C x < 0 → Q x = -C x ∧ c = -1 := by
    intro x hx
    have hh := halfLine_negative_second a (C x) c (Q x)
      (relu (C x) - relu (Q x)) hc (h x)
    rcases hh.2.2 with hp | hn
    · have he := hh.2.1
      linarith only [hp.1, he, hx]
    · exact ⟨by linarith only [hn.2.1, hh.2.1], hn.2.2⟩
  have hzero : ∀ x, Q x + C x = 0 := by
    apply hdet (fun x => Q x + C x) (E.add_mem hQ hC)
    intro x hx
    rw [(onNeg x hx).1]
    ring
  refine ⟨(halfLine_negative_second a (C x₀) c (Q x₀)
    (relu (C x₀) - relu (Q x₀)) hc (h x₀)).1,
    (onNeg x₀ hx₀).2, ?_⟩
  intro x
  linarith only [hzero x]

/-- The same rigidity follows from a full positive domain of the negative-output
intercept, provided this second gate actually moves. -/
theorem moving_pair_rigid_of_right (E : Submodule ℝ (α → ℝ))
    (a c : ℝ) (Q C : α → ℝ) (hQ : Q ∈ E) (hC : C ∈ E)
    (hc0 : c ≠ 0) (hneg : ∃ x, C x < 0) (hpos : ∃ x, 0 < C x)
    (hdet : DeterminesPositive E C)
    (h : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (a * p + Q x) - relu (c * p + C x) =
        p + (relu (Q x) - relu (C x))) :
    a = 1 ∧ c = -1 ∧ ∀ x, Q x = -C x := by
  obtain ⟨x₀, hx₀⟩ := hneg
  obtain ⟨x₁, hx₁⟩ := hpos
  have hc : c < 0 := by
    rcases lt_or_gt_of_ne hc0 with hc | hc
    · exact hc
    · have hh := halfLine_positive_second a (Q x₀) c (C x₀)
        (relu (Q x₀) - relu (C x₀)) hc (h x₀)
      linarith only [hh.2.2.2, hx₀]
  have onPos : ∀ x, 0 < C x → Q x = -C x ∧ c = -1 := by
    intro x hx
    have hh := halfLine_negative_second a (Q x) c (C x)
      (relu (Q x) - relu (C x)) hc (h x)
    have hQneg : Q x < 0 := by
      by_contra hn
      have hQnn : 0 ≤ Q x := le_of_not_gt hn
      have he := hh.2.1
      rw [relu_of_nonneg hQnn, relu_of_nonneg hx.le] at he
      linarith only [he, hx]
    have he : Q x = -C x := by
      have hh' := hh.2.1
      rw [relu_of_nonpos hQneg.le, relu_of_nonneg hx.le, zero_sub] at hh'
      exact hh'
    refine ⟨he, ?_⟩
    rcases hh.2.2 with hp | hn
    · linarith only [hh.2.1, hp.1, hQneg]
    · exact hn.2.2
  have hzero : ∀ x, Q x + C x = 0 := by
    apply hdet (fun x => Q x + C x) (E.add_mem hQ hC)
    intro x hx
    rw [(onPos x hx).1]
    ring
  refine ⟨(halfLine_negative_second a (Q x₁) c (C x₁)
    (relu (Q x₁) - relu (C x₁)) hc (h x₁)).1,
    (onPos x₁ hx₁).2, ?_⟩
  intro x
  linarith only [hzero x]

/-- A sign-rigid core on one side rigidifies the entire chain of two pairs. -/
theorem moving_pair_chain_rigid (E : Submodule ℝ (α → ℝ))
    (a b c d : ℝ) (C Q D : α → ℝ)
    (hC : C ∈ E) (hQ : Q ∈ E) (hD : D ∈ E)
    (hneg : ∃ x, C x < 0) (hpos : ∃ x, 0 < C x)
    (hdetNeg : DeterminesNegative E C) (hdetPos : DeterminesPositive E C)
    (hfirst : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (d * p + C x) - relu (b * p + Q x) =
        p + (relu (C x) - relu (Q x)))
    (hsecond : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (a * p + Q x) - relu (c * p + D x) =
        p + (relu (Q x) - relu (D x))) :
    d = 1 ∧ b = -1 ∧ a = 1 ∧ c = -1 ∧
      (∀ x, Q x = -C x) ∧ ∀ x, D x = C x := by
  obtain ⟨hd, hb, hQC⟩ := moving_pair_rigid_of_left E d b C Q hC hQ
    hneg hdetNeg hfirst
  have hQneg : ∃ x, Q x < 0 := by
    obtain ⟨x, hx⟩ := hpos
    exact ⟨x, by rw [hQC x]; linarith only [hx]⟩
  have hQdet : DeterminesNegative E Q := by
    intro F hF hv
    apply hdetPos F hF
    intro x hx
    apply hv x
    rw [hQC x]
    linarith only [hx]
  obtain ⟨ha, hc, hDQ⟩ := moving_pair_rigid_of_left E a c Q D hQ hD
    hQneg hQdet hsecond
  refine ⟨hd, hb, ha, hc, hQC, ?_⟩
  intro x
  rw [hDQ x, hQC x, neg_neg]

/-- A core has determining strict sign domains, both inhabited. -/
def CoreSignRigid (E : Submodule ℝ (α → ℝ)) (C : α → ℝ) : Prop :=
  (∃ x, C x < 0) ∧ (∃ x, 0 < C x) ∧
    DeterminesNegative E C ∧ DeterminesPositive E C

/-- The portion of a three-core residual classification needed for physical
extraction: the selected core is sign-rigid and the remainder is not parallel
to it. This is an explicit residual input, not an assumed physical normal form. -/
def TailProfile (E : Submodule ℝ (α → ℝ)) (H D K : α → ℝ) (ε : ℝ) : Prop :=
  ∀ R : α → ℝ, R ∈ E →
    (∀ x, H x = R x + ε * relu (D x) + K x) →
      CoreSignRigid E D ∧ ¬ ∃ k : ℝ, ∀ x, R x = k * D x

lemma affineTail_mem_of_ne_zero (E : Submodule ℝ (α → ℝ))
    (s : ℝ) (F : α → ℝ) (hs : s ≠ 0) (hF : F ∈ E) :
    (fun x => affineTail s (F x)) ∈ E := by
  by_cases hp : 0 < s
  · simpa only [affineTail, if_pos hp] using hF
  · have he : (fun x => affineTail s (F x)) = 0 := by
      funext x
      simp only [affineTail, if_neg hp, if_neg hs, Pi.zero_apply]
    rw [he]
    exact E.zero_mem

/-- Three moving gates with a positive shared output are impossible once
an actual three-core residual tail has the stated sign-span/nonparallel profile. -/
theorem no_three_moving_shared_positive (E : Submodule ℝ (α → ℝ))
    (a b c d : ℝ) (Q C D K H : α → ℝ)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0)
    (hQ : Q ∈ E) (hC : C ∈ E) (hD : D ∈ E)
    (hprofile : TailProfile E H D K (-1))
    (h : ∀ x, ∀ z : ℝ,
      relu (a * relu z + b * relu (-z) + Q x) -
        relu (c * relu z + C x) - relu (d * relu (-z) + D x) + K x = z + H x) :
    False := by
  have hz : ∀ x, H x = relu (Q x) - relu (C x) - relu (D x) + K x := by
    intro x
    have hh := h x 0
    simp only [neg_zero, show relu (0 : ℝ) = 0 from max_self 0,
      mul_zero, zero_add, add_zero] at hh
    exact hh.symm
  have hp : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (a * p + Q x) - relu (c * p + C x) =
        p + (relu (Q x) - relu (C x)) := by
    intro x p hp
    have hh := h x p
    simp only [relu_of_nonneg hp, relu_of_nonpos (neg_nonpos.mpr hp),
      mul_zero, add_zero, zero_add] at hh
    linarith only [hh, hz x]
  have hn : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (d * p + D x) - relu (b * p + Q x) =
        p + (relu (D x) - relu (Q x)) := by
    intro x p hp
    have hh := h x (-p)
    simp only [relu_of_nonpos (neg_nonpos.mpr hp), neg_neg,
      relu_of_nonneg hp, mul_zero, zero_add] at hh
    linarith only [hh, hz x]
  let R : α → ℝ := fun x => affineTail a (Q x) - affineTail c (C x)
  have hR : R ∈ E := E.sub_mem
    (affineTail_mem_of_ne_zero E a Q ha0 hQ)
    (affineTail_mem_of_ne_zero E c C hc0 hC)
  have hrepr : ∀ x, H x = R x + (-1) * relu (D x) + K x := by
    intro x
    have hh := (halfLine_slopes a (Q x) c (C x)
      (relu (Q x) - relu (C x)) (hp x)).2
    dsimp only [R]
    linarith only [hh, hz x]
  obtain ⟨⟨hneg,hpos,hdetN,hdetP⟩, hnot⟩ := hprofile R hR hrepr
  obtain ⟨_, _, ha, hc, hQD, _⟩ := moving_pair_chain_rigid E a b c d D Q C
    hD hQ hC hneg hpos hdetN hdetP hn hp
  apply hnot
  refine ⟨-1, fun x => ?_⟩
  dsimp only [R]
  rw [ha, hc]
  norm_num only [affineTail, zero_lt_one, if_true,
    show ¬ (0 : ℝ) < -1 by norm_num, show (-1 : ℝ) ≠ 0 by norm_num,
    if_false, sub_zero, neg_one_mul]
  exact hQD x

/-- The negative-shared-output pattern has the same proof, with reversed
half-line subtraction. The selected residual core alone supplies both spans. -/
theorem no_three_moving_shared_negative (E : Submodule ℝ (α → ℝ))
    (a b c d : ℝ) (Q C D K H : α → ℝ)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hQ : Q ∈ E) (hC : C ∈ E) (hD : D ∈ E)
    (hprofile : TailProfile E H D K 1)
    (h : ∀ x, ∀ z : ℝ,
      -relu (a * relu z + b * relu (-z) + Q x) +
        relu (c * relu z + C x) + relu (d * relu (-z) + D x) + K x = z + H x) :
    False := by
  have hz : ∀ x, H x = relu (C x) - relu (Q x) + relu (D x) + K x := by
    intro x
    have hh := h x 0
    simp only [neg_zero, show relu (0 : ℝ) = 0 from max_self 0,
      mul_zero, zero_add, add_zero] at hh
    linarith only [hh]
  have hp : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (c * p + C x) - relu (a * p + Q x) =
        p + (relu (C x) - relu (Q x)) := by
    intro x p hp
    have hh := h x p
    simp only [relu_of_nonneg hp, relu_of_nonpos (neg_nonpos.mpr hp),
      mul_zero, add_zero, zero_add] at hh
    linarith only [hh, hz x]
  have hn : ∀ x, ∀ p : ℝ, 0 ≤ p →
      relu (b * p + Q x) - relu (d * p + D x) =
        p + (relu (Q x) - relu (D x)) := by
    intro x p hp
    have hh := h x (-p)
    simp only [relu_of_nonpos (neg_nonpos.mpr hp), neg_neg,
      relu_of_nonneg hp, mul_zero, zero_add] at hh
    linarith only [hh, hz x]
  let R : α → ℝ := fun x => affineTail c (C x) - affineTail a (Q x)
  have hR : R ∈ E := E.sub_mem
    (affineTail_mem_of_ne_zero E c C hc0 hC)
    (affineTail_mem_of_ne_zero E a Q ha0 hQ)
  have hrepr : ∀ x, H x = R x + 1 * relu (D x) + K x := by
    intro x
    have hh := (halfLine_slopes c (C x) a (Q x)
      (relu (C x) - relu (Q x)) (hp x)).2
    dsimp only [R]
    linarith only [hh, hz x]
  obtain ⟨⟨hneg,hpos,hdetN,hdetP⟩, hnot⟩ := hprofile R hR hrepr
  obtain ⟨_, _, hQD⟩ := moving_pair_rigid_of_right E b d Q D hQ hD
    hd0 hneg hpos hdetP hn
  have hQneg : ∃ x, Q x < 0 := by
    obtain ⟨x,hx⟩ := hpos
    exact ⟨x, by rw [hQD x]; linarith only [hx]⟩
  have hQpos : ∃ x, 0 < Q x := by
    obtain ⟨x,hx⟩ := hneg
    exact ⟨x, by rw [hQD x]; linarith only [hx]⟩
  have hQdet : DeterminesPositive E Q := by
    intro F hF hv
    apply hdetN F hF
    intro x hx
    apply hv x
    rw [hQD x]
    linarith only [hx]
  obtain ⟨hc, ha, hCQ⟩ := moving_pair_rigid_of_right E c a C Q hC hQ
    ha0 hQneg hQpos hQdet hp
  apply hnot
  refine ⟨1, fun x => ?_⟩
  dsimp only [R]
  rw [hc, ha]
  norm_num only [affineTail, zero_lt_one, if_true,
    show ¬ (0 : ℝ) < -1 by norm_num, show (-1 : ℝ) ≠ 0 by norm_num,
    if_false, sub_zero, one_mul]
  rw [hCQ x, hQD x, neg_neg]

#print axioms moving_pair_rigid_of_left
#print axioms moving_pair_rigid_of_right
#print axioms moving_pair_chain_rigid
#print axioms no_three_moving_shared_positive
#print axioms no_three_moving_shared_negative
end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
