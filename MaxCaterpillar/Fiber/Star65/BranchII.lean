import MaxCaterpillar.Fiber.Star65.BranchI

/-! # Exhaustive coefficient forcing in the second normalized residual branch

These statements concern arbitrary real coefficients and exact identities on
whole intervals of feature states. The slopes and offsets of the affine
remainder remain unrestricted throughout the necessity arguments.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

/-- The third feature cone fixes the negative threshold and both amplitudes
visible there. The first positive term carries the target kink. -/
theorem branchII_coneIII_coefficients (a b γ n l : ℝ) (slope offset : ℝ → ℝ)
    (hb : 0 < b)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + a * max 0 (A - w) + b * max 0 (1 - w) -
        γ * max 0 (n + l * A - w) = max A w) :
    n = 1 ∧ l = 0 ∧ γ = b ∧ a = 1 := by
  have hforced : ∀ A : ℝ, 0 < A → A < 1 → n + l * A = 1 ∧ γ = b := by
    intro A hA hA1
    have heq : ∀ w : ℝ, 0 ≤ w →
        slope A * w + offset A + b * max 0 (1 - w) + a * max 0 (A - w) -
          γ * max 0 (n + l * A - w) = max A w := by
      intro w hw
      linarith only [hid A hA hA1 w hw]
    exact three_hinge_spurious_forces_negative b a γ 1 A (n + l * A)
      (slope A) (offset A) A hb (by norm_num) (ne_of_lt hA1) (ne_of_lt hA1) heq
  have hthird := hforced (1 / 3) (by norm_num) (by norm_num)
  have htwo := hforced (2 / 3) (by norm_num) (by norm_num)
  have hl : l = 0 := by linarith only [hthird.1, htwo.1]
  have hn : n = 1 := by rw [hl] at hthird; linarith only [hthird.1]
  have ha := three_hinge_breakpoint_mass a b γ (1 / 3) 1 (n + l * (1 / 3))
    (slope (1 / 3)) (offset (1 / 3)) (1 / 3) (1 / 3) (by norm_num)
    (hid (1 / 3) (by norm_num) (by norm_num))
  rw [hn, hl] at ha
  norm_num at ha
  exact ⟨hn, hl, hthird.2, ha⟩

/-- The first feature cone forces `h ≤ -1`: otherwise a moving spurious
threshold would have to lie in a fixed two-point set throughout an interval. -/
theorem branchII_coneI_slack_le (b γ m h : ℝ) (slope offset : ℝ → ℝ)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + max 0 (A + h - w) + b * max 0 (1 - w) -
        γ * max 0 (m - w) = max 1 w) : h ≤ -1 := by
  by_contra hh
  have hh' : -1 < h := lt_of_not_ge hh
  let δ : ℝ := min (1 + h) 1
  have hd : 0 < δ := lt_min (by linarith only [hh']) (by norm_num)
  have hdh : δ ≤ 1 + h := min_le_left _ _
  have hd1 : δ ≤ 1 := min_le_right _ _
  have hforced : ∀ A : ℝ, 0 < A → A < 1 → 0 < A + h →
      A + h = 1 ∨ A + h = m := by
    intro A hA hA1 hAh
    by_cases he : A + h = 1
    · exact Or.inl he
    · have heq : ∀ w : ℝ, 0 ≤ w →
          slope A * w + offset A + 1 * max 0 (A + h - w) + b * max 0 (1 - w) -
            γ * max 0 (m - w) = max 1 w := by
        intro w hw
        simpa only [one_mul] using hid A hA hA1 w hw
      exact Or.inr (three_hinge_spurious_forces_negative 1 b γ (A + h) 1 m
        (slope A) (offset A) 1 (by norm_num) hAh (Ne.symm he) (Ne.symm he) heq).1.symm
  have h1 := hforced (1 - δ / 4) (by linarith only [hd1]) (by linarith only [hd])
    (by linarith only [hd, hdh])
  have h2 := hforced (1 - δ / 2) (by linarith only [hd1]) (by linarith only [hd])
    (by linarith only [hd, hdh])
  have h3 := hforced (1 - 3 * δ / 4) (by linarith only [hd1]) (by linarith only [hd])
    (by linarith only [hd, hdh])
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    linarith only [hd, h1, h2, h3]

/-- With `h ≤ -1`, the first cone forces unit amplitude and a nonpositive
negative threshold. This includes the boundary `h = -1`. -/
theorem branchII_coneI_coefficients (b m h : ℝ) (slope offset : ℝ → ℝ)
    (hh : h ≤ -1)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + max 0 (A + h - w) + b * max 0 (1 - w) -
        b * max 0 (m - w) = max 1 w) : b = 1 ∧ m ≤ 0 := by
  have hid' : ∀ w : ℝ, 0 ≤ w →
      slope (1 / 2) * w + offset (1 / 2) + 1 * max 0 ((1 / 2 + h) - w) +
        b * max 0 (1 - w) - b * max 0 (m - w) = max 1 w := by
    intro w hw
    simpa only [one_mul] using hid (1 / 2) (by norm_num) (by norm_num) w hw
  have hp : 1 / 2 + h < 0 := by linarith only [hh]
  have mass := three_hinge_breakpoint_mass 1 b b (1 / 2 + h) 1 m
    (slope (1 / 2)) (offset (1 / 2)) 1 1 (by norm_num) hid'
  rw [if_neg (by linarith only [hp] : 1 / 2 + h ≠ 1), if_pos rfl, zero_add] at mass
  norm_num at mass
  have hm1 : m ≠ 1 := by
    intro hm
    rw [if_pos hm] at mass
    linarith only [mass]
  rw [if_neg hm1, sub_zero] at mass
  refine ⟨mass, ?_⟩
  by_contra hm
  have hmpos : 0 < m := lt_of_not_ge hm
  have mass' := three_hinge_breakpoint_mass 1 b b (1 / 2 + h) 1 m
    (slope (1 / 2)) (offset (1 / 2)) 1 m hmpos hid'
  rw [if_neg (by linarith only [hp, hmpos] : 1 / 2 + h ≠ m), if_neg (Ne.symm hm1),
    if_pos rfl, zero_add, zero_sub, if_neg (Ne.symm hm1)] at mass'
  linarith only [mass, mass']

/-- The middle feature cone identifies the final negative coefficient. -/
theorem branchII_middle_coefficient (m h : ℝ) (slope offset : ℝ → ℝ)
    (hh : h ≤ -1)
    (hid : ∀ U : ℝ, 0 < U → ∀ w : ℝ, 0 ≤ w →
      slope U * w + offset U + max 0 (U + 1 + h - w) + max 0 (U + 1 - w) -
        max 0 (U + m - w) = max (U + 1) w) : m = 1 + h := by
  have hU : 0 < 1 - h := by linarith only [hh]
  have heq : ∀ w : ℝ, 0 ≤ w →
      slope (1 - h) * w + offset (1 - h) + 1 * max 0 (2 - w) +
        1 * max 0 ((2 - h) - w) - 1 * max 0 ((1 - h + m) - w) =
        max (2 - h) w := by
    intro w hw
    have H := hid (1 - h) hU w hw
    convert H using 1 <;> ring
  have hforced := three_hinge_spurious_forces_negative 1 1 1 2 (2 - h) (1 - h + m)
    (slope (1 - h)) (offset (1 - h)) (2 - h)
    (by norm_num) (by norm_num) (by linarith only [hh]) (by linarith only [hh]) heq
  linarith only [hforced.1]

/-- Complete coefficient necessity in the normalized second branch. The
negative threshold is written `n U + m V + l A`; the three necessary feature
cones already force every coefficient and the closed slack inequality. -/
theorem branchII_normalized_coefficients (a b γ n m l h : ℝ)
    (slopeI offsetI slopeIII offsetIII slopeII offsetII : ℝ → ℝ)
    (hb : 0 < b)
    (hI : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slopeI A * w + offsetI A + a * max 0 (A + h - w) + b * max 0 (1 - w) -
        γ * max 0 (m + l * A - w) = max 1 w)
    (hIII : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slopeIII A * w + offsetIII A + a * max 0 (A - w) + b * max 0 (1 - w) -
        γ * max 0 (n + l * A - w) = max A w)
    (hII : ∀ U : ℝ, 0 < U → ∀ w : ℝ, 0 ≤ w →
      slopeII U * w + offsetII U + a * max 0 (U + 1 + h - w) +
        b * max 0 (U + 1 - w) - γ * max 0 (n * U + m + l * (U + 1) - w) =
        max (U + 1) w) :
    a = 1 ∧ b = 1 ∧ γ = 1 ∧ n = 1 ∧ m = 1 + h ∧ l = 0 ∧ h ≤ -1 := by
  obtain ⟨hn, hl, hg, ha⟩ := branchII_coneIII_coefficients a b γ n l
    slopeIII offsetIII hb hIII
  subst n l γ a
  simp only [one_mul, zero_mul, add_zero] at hI hII
  have hh := branchII_coneI_slack_le b b m h slopeI offsetI hI
  obtain ⟨hb1, _⟩ := branchII_coneI_coefficients b m h slopeI offsetI hh hI
  subst b
  simp only [one_mul] at hII
  have hm := branchII_middle_coefficient m h slopeII offsetII hh hII
  exact ⟨rfl, rfl, rfl, rfl, hm, rfl, hh⟩

end MaxCaterpillar.Fiber.Star65
