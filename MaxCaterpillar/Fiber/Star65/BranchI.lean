import MaxCaterpillar.Fiber.Star65.Breakpoint

/-! # Coefficient forcing in the first normalized star residual branch

These are necessary consequences of all-input identities on the indicated
feature cones. The affine remainder is arbitrary. No coefficient normal form
is assumed in place of its proof.
-/

set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Star65

open BigOperators

/-- The explicit three-term specialization of the breakpoint mass theorem. -/
theorem three_hinge_breakpoint_mass (a b γ P Q N α β target p : ℝ) (hp : 0 < p)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + a * max 0 (P - w) + b * max 0 (Q - w) -
        γ * max 0 (N - w) = max target w) :
    (if P = p then a else 0) + (if Q = p then b else 0) -
      (if N = p then γ else 0) = if target = p then 1 else 0 := by
  classical
  have hf : ∀ w : ℝ, 0 ≤ w →
      α * w + β + ∑ j : Fin 3, (![a, b, -γ] j) * max 0 (![P, Q, N] j - w) =
        max target w := by
    intro w hw
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hid w hw
  have hm := breakpoint_mass_of_identity Finset.univ ![a, b, -γ] ![P, Q, N]
    α β target p hp hf
  by_cases hN : N = p
  · simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc, hN] using hm
  · simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc, hN] using hm

/-- An isolated spurious positive threshold among three terms forces the
negative threshold to coincide with it, with equal absolute amplitude. -/
theorem three_hinge_spurious_forces_negative (a b γ P Q N α β target : ℝ)
    (ha : 0 < a) (hP : 0 < P) (hQP : Q ≠ P) (htP : target ≠ P)
    (hid : ∀ w : ℝ, 0 ≤ w →
      α * w + β + a * max 0 (P - w) + b * max 0 (Q - w) -
        γ * max 0 (N - w) = max target w) :
    N = P ∧ γ = a := by
  classical
  have hm := three_hinge_breakpoint_mass a b γ P Q N α β target P hP hid
  rw [if_pos rfl, if_neg hQP, if_neg htP, add_zero] at hm
  have hNP : N = P := by
    by_contra h
    rw [if_neg h, sub_zero] at hm
    exact (ne_of_gt ha) hm
  refine ⟨hNP, ?_⟩
  rw [if_pos hNP] at hm
  linarith only [hm]

/-- On the first feature cone, exactness determines the entire negative
threshold, the negative amplitude, and the second positive amplitude.
The first positive amplitude is determined on a different feature cone. -/
theorem branchI_coneI_coefficients (a b γ m l : ℝ) (slope offset : ℝ → ℝ)
    (ha : 0 < a)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + a * max 0 (A - w) + b * max 0 (1 - w) -
        γ * max 0 (m + l * A - w) = max 1 w) :
    m = 0 ∧ l = 1 ∧ γ = a ∧ b = 1 := by
  have hforced : ∀ A : ℝ, 0 < A → A < 1 → m + l * A = A ∧ γ = a := by
    intro A hA hA1
    exact three_hinge_spurious_forces_negative a b γ A 1 (m + l * A)
      (slope A) (offset A) 1 ha hA (ne_of_gt hA1) (ne_of_gt hA1) (hid A hA hA1)
  have hthird := hforced (1 / 3) (by norm_num) (by norm_num)
  have htwo := hforced (2 / 3) (by norm_num) (by norm_num)
  have hl : l = 1 := by linarith only [hthird.1, htwo.1]
  have hm : m = 0 := by rw [hl] at hthird; linarith only [hthird.1]
  have hb := three_hinge_breakpoint_mass a b γ (1 / 3) 1 (m + l * (1 / 3))
    (slope (1 / 3)) (offset (1 / 3)) 1 1 (by norm_num)
    (hid (1 / 3) (by norm_num) (by norm_num))
  rw [hm, hl] at hb
  norm_num at hb
  exact ⟨hm, hl, hthird.2, hb⟩

/-- The third feature cone excludes a positive slack `k`. Otherwise its
fixed spurious threshold would force the moving negative threshold to be
constant on an interval. -/
theorem branchI_coneIII_slack_nonpos (a γ d k : ℝ) (slope offset : ℝ → ℝ)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + a * max 0 (A - w) + max 0 (k - w) -
        γ * max 0 (A + d - w) = max A w) : k ≤ 0 := by
  by_contra hk
  have hk' : 0 < k := lt_of_not_ge hk
  let δ : ℝ := min k 1
  have hd : 0 < δ := lt_min hk' (by norm_num)
  have hdk : δ ≤ k := min_le_left _ _
  have hd1 : δ ≤ 1 := min_le_right _ _
  have hforced : ∀ A : ℝ, 0 < A → A < 1 → A < k → A + d = k := by
    intro A hA hA1 hAk
    have heq : ∀ w : ℝ, 0 ≤ w →
        slope A * w + offset A + 1 * max 0 (k - w) + a * max 0 (A - w) -
          γ * max 0 (A + d - w) = max A w := by
      intro w hw
      linarith only [hid A hA hA1 w hw]
    exact (three_hinge_spurious_forces_negative 1 a γ k A (A + d)
      (slope A) (offset A) A (by norm_num) hk' (ne_of_lt hAk)
      (ne_of_lt hAk) heq).1
  have h1 := hforced (δ / 3) (by linarith only [hd]) (by linarith only [hd, hd1])
    (by linarith only [hd, hdk])
  have h2 := hforced (2 * δ / 3) (by linarith only [hd]) (by linarith only [hd, hd1])
    (by linarith only [hd, hdk])
  linarith only [hd, h1, h2]

/-- After the first cone's amplitude equalities, the third cone forces unit
amplitude and keeps the negative threshold nonpositive throughout that cone. -/
theorem branchI_coneIII_coefficients (a d k : ℝ) (slope offset : ℝ → ℝ)
    (ha : 0 < a) (hk : k ≤ 0)
    (hid : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slope A * w + offset A + a * max 0 (A - w) + max 0 (k - w) -
        a * max 0 (A + d - w) = max A w) : a = 1 ∧ d ≤ -1 := by
  have hmass := three_hinge_breakpoint_mass a 1 a (1 / 2) k (1 / 2 + d)
    (slope (1 / 2)) (offset (1 / 2)) (1 / 2) (1 / 2) (by norm_num)
    (by intro w hw; simpa using hid (1 / 2) (by norm_num) (by norm_num) w hw)
  have hkh : k ≠ 1 / 2 := ne_of_lt (by linarith only [hk])
  rw [if_pos rfl, if_neg hkh, if_pos rfl, add_zero] at hmass
  have hd : d ≠ 0 := by
    intro hd
    rw [hd, add_zero, if_pos rfl] at hmass
    linarith only [hmass]
  have hhalf : (1 : ℝ) / 2 + d ≠ 1 / 2 := by
    intro h
    apply hd
    linarith only [h]
  rw [if_neg hhalf, sub_zero] at hmass
  refine ⟨hmass, ?_⟩
  have hnon : ∀ A : ℝ, 0 < A → A < 1 → A + d ≤ 0 := by
    intro A hA hA1
    by_contra hN
    have hN' : 0 < A + d := lt_of_not_ge hN
    have hAN : A ≠ A + d := by
      intro h
      apply hd
      linarith only [h]
    have hkN : k ≠ A + d := ne_of_lt (lt_of_le_of_lt hk hN')
    have hm := three_hinge_breakpoint_mass a 1 a A k (A + d)
      (slope A) (offset A) A (A + d) hN'
      (by intro w hw; simpa using hid A hA hA1 w hw)
    rw [if_neg hAN, if_neg hkN, if_pos rfl, if_neg hAN] at hm
    linarith only [ha, hm]
  have hh := hnon (1 / 2) (by norm_num) (by norm_num)
  by_contra h
  have hd' : -1 < d := lt_of_not_ge h
  have hA := hnon ((1 - d) / 2) (by linarith only [hh]) (by linarith only [hd'])
  linarith only [hd', hA]

/-- On the middle feature cone, one positive spurious threshold fixes the
remaining negative-threshold coefficient. -/
theorem branchI_middle_coefficient (d k : ℝ) (slope offset : ℝ → ℝ) (hk : k ≤ 0)
    (hid : ∀ V : ℝ, 0 < V → ∀ w : ℝ, 0 ≤ w →
      slope V * w + offset V + max 0 (1 + V - w) + max 0 (V + k - w) -
        max 0 (1 + V + d - w) = max (1 + V) w) : d = k - 1 := by
  have hV : 0 < 1 - k := by linarith only [hk]
  have heq : ∀ w : ℝ, 0 ≤ w →
      slope (1 - k) * w + offset (1 - k) + 1 * max 0 (1 - w) +
        1 * max 0 (2 - k - w) - 1 * max 0 (2 - k + d - w) = max (2 - k) w := by
    intro w hw
    have he := hid (1 - k) hV w hw
    have h1 : 1 + (1 - k) = 2 - k := by ring
    have h2 : 1 - k + k = 1 := by ring
    rw [h1, h2] at he
    linarith only [he]
  have hne : 2 - k ≠ 1 := ne_of_gt (by linarith only [hk])
  have hf := three_hinge_spurious_forces_negative 1 1 1 1 (2 - k) (2 - k + d)
    (slope (1 - k)) (offset (1 - k)) (2 - k) (by norm_num) (by norm_num) hne hne heq
  linarith only [hf.1]

/-- Complete coefficient necessity for normalized branch I, from three
one-dimensional slices of the actual feature cones. The negative threshold
has coefficient form `n*U + m*V + l*A`; all three affine remainders are free. -/
theorem branchI_normalized_coefficients (a b γ n m l k : ℝ)
    (slopeI offsetI slopeIII offsetIII slopeII offsetII : ℝ → ℝ) (ha : 0 < a)
    (hI : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slopeI A * w + offsetI A + a * max 0 (A - w) + b * max 0 (1 - w) -
        γ * max 0 (m + l * A - w) = max 1 w)
    (hIII : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slopeIII A * w + offsetIII A + a * max 0 (A - w) + b * max 0 (k - w) -
        γ * max 0 (n + l * A - w) = max A w)
    (hII : ∀ V : ℝ, 0 < V → ∀ w : ℝ, 0 ≤ w →
      slopeII V * w + offsetII V + a * max 0 (1 + V - w) + b * max 0 (V + k - w) -
        γ * max 0 (n + m * V + l * (1 + V) - w) = max (1 + V) w) :
    a = 1 ∧ b = 1 ∧ γ = 1 ∧ m = 0 ∧ l = 1 ∧ n = k - 1 ∧ k ≤ 0 := by
  rcases branchI_coneI_coefficients a b γ m l slopeI offsetI ha hI with
    ⟨hm, hl, hγ, hb⟩
  have hIII' : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      slopeIII A * w + offsetIII A + a * max 0 (A - w) + max 0 (k - w) -
        a * max 0 (A + n - w) = max A w := by
    intro A hA hA1 w hw
    have he := hIII A hA hA1 w hw
    rw [hb, hγ, hl, one_mul, one_mul] at he
    have hn : n + A = A + n := add_comm _ _
    rw [hn] at he
    exact he
  have hk := branchI_coneIII_slack_nonpos a a n k slopeIII offsetIII hIII'
  have hac := branchI_coneIII_coefficients a n k slopeIII offsetIII ha hk hIII'
  have ha1 := hac.1
  have hγ1 : γ = 1 := hγ.trans ha1
  have hII' : ∀ V : ℝ, 0 < V → ∀ w : ℝ, 0 ≤ w →
      slopeII V * w + offsetII V + max 0 (1 + V - w) + max 0 (V + k - w) -
        max 0 (1 + V + n - w) = max (1 + V) w := by
    intro V hV w hw
    have he := hII V hV w hw
    rw [ha1, hb, hγ1, hm, hl] at he
    simp only [one_mul, zero_mul, add_zero] at he
    have hn : n + (1 + V) = 1 + V + n := by ring
    rw [hn] at he
    exact he
  have hn := branchI_middle_coefficient n k slopeII offsetII hk hII'
  exact ⟨ha1, hb, hγ1, hm, hl, hn, hk⟩

end MaxCaterpillar.Fiber.Star65
