import MaxCaterpillar.Fiber.Mixed65.Heads

/-! # A reconstructed two-head remainder is genuinely feature-linear

The remainder is not assumed to belong to the invariant feature space. Exact
reconstruction forces it to be one of the three linear combinations A, -B,
or A-B of the actual physical head intercepts.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Mixed65
open MaxCaterpillar.Frontier

/-- Exact reconstruction supplies the feature-space hypothesis of the head
classifier; it need not be imposed as a normalization assumption. -/
theorem Heads.Reconstructs.remainder_mem {α : Type*}
    {h : Heads α} {L : α → ℝ} (hh : h.Reconstructs L)
    (E : Submodule ℝ (α → ℝ)) (hA : h.A ∈ E) (hB : h.B ∈ E) : L ∈ E := by
  rcases lt_trichotomy h.c 0 with hc | hc | hc
  · have he : L = h.A := by
      funext x
      exact ((halfLine_negative_second h.a (h.A x) h.c (h.B x) (L x)
        hc (hh.positive_halfLine x)).2.1).symm
    rw [he]
    exact hA
  · rcases lt_trichotomy h.b 0 with hb | hb | hb
    · have he : L = -h.B := by
        funext x
        have hx := (halfLine_negative_second h.d (h.B x) h.b (h.A x) (-L x)
          hb (hh.negative_halfLine x)).2.1
        change L x = -h.B x
        linarith only [hx]
      rw [he]
      exact E.neg_mem hB
    · have he : L = h.A-h.B := by
        funext x
        have hp := hh.positive_halfLine x
        have hn := hh.negative_halfLine x
        rw [hc] at hp
        rw [hb] at hn
        simp only [zero_mul,zero_add] at hp hn
        have hAz := (halfLine_zero_second h.a (h.A x) (h.B x) (L x) hp).2.2
        have hBz := (halfLine_zero_second h.d (h.B x) (h.A x) (-L x) hn).2.2
        have hx := hh x 0
        simp only [Heads.eval,show relu (0 : ℝ) = 0 from max_self 0,neg_zero,mul_zero,zero_add,
          relu_of_nonneg hAz,relu_of_nonneg hBz] at hx
        exact hx.symm
      rw [he]
      exact E.sub_mem hA hB
    · have he : L = h.A-h.B := by
        funext x
        have hx := (halfLine_positive_second h.d (h.B x) h.b (h.A x) (-L x)
          hb (hh.negative_halfLine x)).2.1
        change L x = h.A x-h.B x
        linarith only [hx]
      rw [he]
      exact E.sub_mem hA hB
  · have he : L = h.A-h.B := by
      funext x
      exact ((halfLine_positive_second h.a (h.A x) h.c (h.B x) (L x)
        hc (hh.positive_halfLine x)).2.1).symm
    rw [he]
    exact E.sub_mem hA hB

end MaxCaterpillar.Fiber.Mixed65
