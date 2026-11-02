import MaxCaterpillar.Frontier.StarCertificate.Checker

/-! # Extending a closed-halfspace certificate by actual evenness -/
set_option autoImplicit false

namespace MaxCaterpillar.Frontier.StarCertificate

/-- A certificate on the closed nonpositive halfspace covers all real
inputs when the represented function is even. Equality points stay in the
certified halfspace. No homogeneity or continuity is needed. -/
theorem even_zero_of_nonpositive_coordinate {n : ℕ} (j : Fin n)
    (F : (Fin n → ℝ) → ℝ) (heven : ∀ x, F (-x) = F x)
    (hhalf : ∀ x, x j ≤ 0 → F x = 0) : ∀ x, F x = 0 := by
  intro x
  rcases le_total (x j) 0 with hx | hx
  · exact hhalf x hx
  · rw [← heven x]
    exact hhalf (-x) (neg_nonpos.mpr hx)

end MaxCaterpillar.Frontier.StarCertificate
