import MaxCaterpillar.Fiber.Star65.BranchII
import MaxCaterpillar.Fiber.Star65.Independence

/-!
# Converse classification for normalized star-to-path residuals

The hypothesis is an equality of functions on every real input of the actual
four-feature dictionary. The proof derives the one-dimensional slice identities,
then invokes the existing breakpoint-mass lemmas. No cone identities are assumed.

Normalizing arbitrary physical gates to the two positive carrier roles is a
separate geometric step; this module does not claim that step or a component count.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.Star
open MaxCaterpillar.Fiber.Star65

noncomputable def target (q v w : ℝ) : ℝ :=
  max (max 0 (q + v)) (max v w)

/-- All-input identity with the two distinguished positive carrier directions.
The feature-linear remainder and all negative-gate coefficients are unrestricted. -/
def NormalizedIdentity (r a b γ h k n m l eU eV eW eA : ℝ) : Prop :=
  ∀ q v w : ℝ,
    eU * max 0 q + eV * max 0 v + eW * max 0 w + eA * comparison r q v +
      a * max 0 (comparison r q v - max 0 w + h * max 0 v) +
      b * max 0 (max 0 v - max 0 w + k * max 0 q) -
      γ * max 0 (n * max 0 q + m * max 0 v + l * comparison r q v - max 0 w) =
        target q v w

lemma comparison_coneI {r A : ℝ} (hr : 0 < r) (hA : 0 < A) (hA1 : A < 1) :
    comparison r (r * (A - 1)) 1 = A := by
  have hq : r * (A - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith)
  have ht : 0 ≤ r * (A - 1) + r * 1 := by nlinarith only [mul_pos hr hA]
  unfold comparison
  rw [max_eq_left hq, max_eq_right ht, mul_zero, sub_zero]
  apply (div_eq_iff (ne_of_gt hr)).mpr
  ring

lemma comparison_coneIII {r A : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 < A) :
    comparison r 1 (A - 1) = A := by
  have ht : 0 ≤ 1 + r * (A - 1) := by nlinarith only [hr1, mul_pos hr hA]
  unfold comparison
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_eq_right ht]
  apply (div_eq_iff (ne_of_gt hr)).mpr
  ring

lemma target_coneI {r A w : ℝ} (hr : 0 < r) (hA1 : A < 1) :
    target (r * (A - 1)) 1 w = max 1 w := by
  have hq : r * (A - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith)
  have h : max 0 (r * (A - 1) + 1) ≤ 1 := max_le (by norm_num) (by linarith only [hq])
  exact max_eq_right (h.trans (le_max_left 1 w))

lemma target_coneIII {A w : ℝ} (hA : 0 < A) :
    target 1 (A - 1) w = max A w := by
  unfold target
  rw [show (1 : ℝ) + (A - 1) = A by ring, max_eq_right hA.le, ← max_assoc,
    max_eq_left (by linarith : A - 1 ≤ A)]

lemma target_coneII {U V w : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    target U V w = max (U + V) w := by
  unfold target
  rw [max_eq_right (add_nonneg hU hV), ← max_assoc, max_eq_left (by linarith only [hU] : V ≤ U + V)]

/-- The two normalized coefficient alternatives are exhaustive for an actual
all-input identity; in particular the endpoint `r = 1` is included. -/
theorem normalized_coefficients {r a b γ h k n m l eU eV eW eA : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (hb : 0 < b) (hg : 0 < γ)
    (H : NormalizedIdentity r a b γ h k n m l eU eV eW eA) :
    (h = 0 ∧ a = 1 ∧ b = 1 ∧ γ = 1 ∧ n = k - 1 ∧ m = 0 ∧ l = 1 ∧ k ≤ 0) ∨
    (k = 1 ∧ a = 1 ∧ b = 1 ∧ γ = 1 ∧ n = 1 ∧ m = 1 + h ∧ l = 0 ∧ h ≤ -1) := by
  have hsplit : h = 0 ∨ k = 1 := by
    apply star_branch_split a b γ h k (n + m + 2 * l) eW
      (eU + eV + 2 * eA) hg
    intro w hw
    have he := H 1 1 w
    rw [comparison_of_nonneg hr (by norm_num) (by norm_num),
      target_coneII (by norm_num) (by norm_num), max_eq_right hw] at he
    norm_num at he
    convert he using 1 <;> ring
  have hI : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      eW * w + (eV + eA * A) + a * max 0 (A + h - w) +
        b * max 0 (1 - w) - γ * max 0 (m + l * A - w) = max 1 w := by
    intro A hA hA1 w hw
    have he := H (r * (A - 1)) 1 w
    have hq : r * (A - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith)
    rw [comparison_coneI hr hA hA1, target_coneI hr hA1, max_eq_left hq,
      max_eq_right hw] at he
    norm_num at he
    convert he using 1 <;> ring
  have hIII : ∀ A : ℝ, 0 < A → A < 1 → ∀ w : ℝ, 0 ≤ w →
      eW * w + (eU + eA * A) + a * max 0 (A - w) +
        b * max 0 (k - w) - γ * max 0 (n + l * A - w) = max A w := by
    intro A hA hA1 w hw
    have he := H 1 (A - 1) w
    rw [comparison_coneIII hr hr1 hA, target_coneIII hA,
      max_eq_left (by linarith : A - 1 ≤ 0), max_eq_right hw] at he
    norm_num at he
    convert he using 1 <;> ring
  rcases hsplit with hh | hk
  · have hII : ∀ V : ℝ, 0 < V → ∀ w : ℝ, 0 ≤ w →
        eW * w + (eU + eV * V + eA * (1 + V)) +
          a * max 0 (1 + V - w) + b * max 0 (V + k - w) -
          γ * max 0 (n + m * V + l * (1 + V) - w) = max (1 + V) w := by
      intro V hV w hw
      have he := H 1 V w
      rw [comparison_of_nonneg hr (by norm_num) hV.le,
        target_coneII (by norm_num) hV.le, max_eq_right hV.le,
        max_eq_right hw, hh] at he
      norm_num at he
      convert he using 1 <;> ring
    have hI' := hI
    simp only [hh, add_zero] at hI'
    obtain ⟨ha1, hb1, hg1, hm, hl, hn, hk⟩ := branchI_normalized_coefficients
      a b γ n m l k (fun _ => eW) (fun A => eV + eA * A)
      (fun _ => eW) (fun A => eU + eA * A)
      (fun _ => eW) (fun V => eU + eV * V + eA * (1 + V)) ha hI' hIII hII
    exact Or.inl ⟨hh, ha1, hb1, hg1, hn, hm, hl, hk⟩
  · have hII : ∀ U : ℝ, 0 < U → ∀ w : ℝ, 0 ≤ w →
        eW * w + (eU * U + eV + eA * (U + 1)) +
          a * max 0 (U + 1 + h - w) + b * max 0 (U + 1 - w) -
          γ * max 0 (n * U + m + l * (U + 1) - w) = max (U + 1) w := by
      intro U hU w hw
      have he := H U 1 w
      rw [comparison_of_nonneg hr hU.le (by norm_num),
        target_coneII hU.le (by norm_num), max_eq_right hU.le,
        max_eq_right hw, hk] at he
      norm_num at he
      convert he using 1 <;> ring
    have hIII' := hIII
    simp only [hk] at hIII'
    obtain ⟨ha1, hb1, hg1, hn, hm, hl, hh⟩ := branchII_normalized_coefficients
      a b γ n m l h (fun _ => eW) (fun A => eV + eA * A)
      (fun _ => eW) (fun A => eU + eA * A)
      (fun _ => eW) (fun U => eU * U + eV + eA * (U + 1)) hb hI hIII' hII
    exact Or.inr ⟨hk, ha1, hb1, hg1, hn, hm, hl, hh⟩

/-- The comparison coordinate is an independent fourth feature for `r > 0`. -/
lemma comparison_basis_independent {r : ℝ} (hr : 0 < r) (A B C D : ℝ)
    (H : ∀ q v w : ℝ, A * max 0 q + B * max 0 v + C * max 0 w +
      D * comparison r q v = 0) : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  obtain ⟨hU,hV,hW,hT⟩ := features_independent hr
    (r*A-(1-r)*D) (r*B) (r*C) D (by
      intro q v w
      have he := H q v w
      unfold comparison at he
      field_simp [hr0] at he
      nlinarith only [he])
  refine ⟨?_,(mul_eq_zero.mp hV).resolve_left hr0,
    (mul_eq_zero.mp hW).resolve_left hr0,hT⟩
  rw [hT,mul_zero,sub_zero] at hU
  exact (mul_eq_zero.mp hU).resolve_left hr0

/-- Once the three cores agree, the actual feature-linear remainder is unique. -/
lemma normalized_base_unique {r a b γ h k n m l eU eV eW eA fU fV fW fA : ℝ}
    (hr : 0 < r)
    (H : NormalizedIdentity r a b γ h k n m l eU eV eW eA)
    (F : NormalizedIdentity r a b γ h k n m l fU fV fW fA) :
    eU=fU ∧ eV=fV ∧ eW=fW ∧ eA=fA := by
  have Hdiff : ∀ q v w : ℝ, (eU-fU)*max 0 q + (eV-fV)*max 0 v +
      (eW-fW)*max 0 w + (eA-fA)*comparison r q v = 0 := by
    intro q v w
    nlinarith only [H q v w,F q v w]
  obtain ⟨hU,hV,hW,hA⟩ := comparison_basis_independent hr _ _ _ _ Hdiff
  exact ⟨sub_eq_zero.mp hU,sub_eq_zero.mp hV,sub_eq_zero.mp hW,sub_eq_zero.mp hA⟩

lemma canonicalI_identity {r k : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hk : k ≤ 0) :
    NormalizedIdentity r 1 1 1 0 k (k-1) 0 1 0 0 1 0 := by
  intro q v w
  have h := branchI_eq_max hr hr1 hk q v w
  dsimp only [branchI] at h
  change _ = max (max 0 (q+v)) (max v w)
  convert h using 1 <;> ring

lemma canonicalII_identity {r h : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hh : h ≤ -1) :
    NormalizedIdentity r 1 1 1 h 1 1 (1+h) 0 0 0 1 0 := by
  intro q v w
  have H := branchII_eq_max hr hr1 hh q v w
  dsimp only [branchII] at H
  change _ = max (max 0 (q+v)) (max v w)
  convert H using 1 <;> ring

/-- Complete normalized three-core classification, including the entire actual
feature-linear remainder. The two alternatives are disjoint, including `r=1`. -/
theorem normalized_identity_iff {r a b γ h k n m l eU eV eW eA : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (hb : 0 < b) (hg : 0 < γ) :
    NormalizedIdentity r a b γ h k n m l eU eV eW eA ↔
      (eU=0 ∧ eV=0 ∧ eW=1 ∧ eA=0) ∧
      ((h=0 ∧ a=1 ∧ b=1 ∧ γ=1 ∧ n=k-1 ∧ m=0 ∧ l=1 ∧ k≤0) ∨
       (k=1 ∧ a=1 ∧ b=1 ∧ γ=1 ∧ n=1 ∧ m=1+h ∧ l=0 ∧ h≤-1)) := by
  constructor
  · intro H
    have hdata := normalized_coefficients hr hr1 ha hb hg H
    refine ⟨?_,hdata⟩
    rcases hdata with ⟨hh,ha1,hb1,hg1,hn,hm,hl,hk⟩ | ⟨hk,ha1,hb1,hg1,hn,hm,hl,hh⟩
    · rw [hh,ha1,hb1,hg1,hn,hm,hl] at H
      exact normalized_base_unique hr H (canonicalI_identity hr hr1 hk)
    · rw [hk,ha1,hb1,hg1,hn,hm,hl] at H
      exact normalized_base_unique hr H (canonicalII_identity hr hr1 hh)
  · rintro ⟨⟨rfl,rfl,rfl,rfl⟩,hdata⟩
    rcases hdata with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hk⟩ |
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hh⟩
    · exact canonicalI_identity hr hr1 hk
    · exact canonicalII_identity hr hr1 hh

end MaxCaterpillar.Fiber.Count65.Star
