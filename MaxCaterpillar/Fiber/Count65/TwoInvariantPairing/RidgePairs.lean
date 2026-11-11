import MaxCaterpillar.Fiber.KinkCancellation
import Mathlib.Data.Finset.Card

/-!
# Opposite pairs forced by a linear anchor difference

Restrict to the line (a,b)=(1+t,t). Each non-invariant ridge has a nonzero
slope there, while the target is the constant one. Local crease cancellation
therefore forces a partner at the same knot. Positive-ray irredundancy turns
that partner into an opposite ray. This avoids an independence theorem for
multivariate ridge functions.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
open BigOperators

variable {ι : Type*} [Fintype ι]

/-- A nonzero coefficient in a linear ReLU representation has an opposite
first-row partner when positive duplicate rays are forbidden. -/
theorem opposite_partner_of_linear_identity (u : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (hs : ∀ j, u j 0 + u j 1 ≠ 0)
    (hno : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j)
    (h : ∀ a b : ℝ, a - b = ∑ j, c j * relu (u j 0 * a + u j 1 * b))
    (j : ι) (hc : c j ≠ 0) :
    ∃ i : ι, i ≠ j ∧ c i ≠ 0 ∧ ∃ t : ℝ, t < 0 ∧ u i = t • u j := by
  classical
  let s : ι → ℝ := fun i => u i 0 + u i 1
  let t₀ : ℝ := -u j 0 / s j
  let b₀ : ι → ℝ := fun i => u i 0 + s i * t₀
  have hsj : s j ≠ 0 := hs j
  have hjzero : b₀ j = 0 := by
    dsimp [b₀, t₀]
    field_simp
    ring
  have hid (t : ℝ) : ∑ i, c i * relu (s i * t + b₀ i) = 1 := by
    calc
      _ = ∑ i, c i * relu (u i 0 * (1 + (t + t₀)) + u i 1 * (t + t₀)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        dsimp [s, b₀]
        ring
      _ = (1 + (t + t₀)) - (t + t₀) := (h _ _).symm
      _ = 1 := by ring
  obtain ⟨i, hij, hci, hib⟩ : ∃ i : ι, i ≠ j ∧ c i ≠ 0 ∧ b₀ i = 0 := by
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · have hn (t : ℝ) : ∑ i, (-c i) * relu (s i * t + b₀ i) = -1 := by
        simp_rw [neg_mul, Finset.sum_neg_distrib, hid]
      obtain ⟨i, hi, hbi, _⟩ := exists_negative_active_zero_gate s b₀ (fun i => -c i)
        0 (-1) 1 (by norm_num) (fun t _ => by rw [hn]; ring)
        j (neg_pos.mpr hcneg) hjzero hsj
      refine ⟨i, ?_, ne_of_gt (neg_neg_iff_pos.mp hi), hbi⟩
      intro he
      subst i
      linarith
    · obtain ⟨i, hi, hbi, _⟩ := exists_negative_active_zero_gate s b₀ c
        0 1 1 (by norm_num) (fun t _ => by rw [hid]; ring)
        j hcpos hjzero hsj
      refine ⟨i, ?_, ne_of_lt hi, hbi⟩
      intro he
      subst i
      linarith
  let t : ℝ := s i / s j
  have ht0 : t ≠ 0 := div_ne_zero (hs i) hsj
  have hcross : u i 0 * s j = s i * u j 0 := by
    have hb : u i 0 - s i * u j 0 / s j = 0 := by
      simpa only [b₀, t₀, neg_div, mul_neg, mul_div_assoc, sub_eq_add_neg] using hib
    exact (eq_div_iff hsj).mp (show u i 0 = s i * u j 0 / s j by linarith only [hb])
  have hcoord : u i 0 = t * u j 0 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hsj).mpr hcross
  have heq : u i = t • u j := by
    funext k
    fin_cases k
    · exact hcoord
    · have hsum : t * s j = s i := div_mul_cancel _ hsj
      change u i 1 = t * u j 1
      dsimp only [s] at hsum
      nlinarith only [hcoord, hsum]
  have ht : t < 0 := by
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · exact hneg
    · exact (hno i j hij t hpos heq).elim
  exact ⟨i, hij, hci, t, ht, heq⟩

/-- Positive-ray irredundancy makes the opposite partner unique. -/
lemma negative_partners_unique (u : ι → Fin 2 → ℝ)
    (hno : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j)
    {i j k : ι} {a b : ℝ} (ha : a < 0) (hb : b < 0)
    (hi : u i = a • u j) (hk : u k = b • u j) : i = k := by
  by_contra hik
  have he : u i = (a / b) • u k := by
    rw [hk, smul_smul, div_mul_cancel _ hb.ne]
    exact hi
  exact hno i k hik (a / b) (div_pos_of_neg_of_neg ha hb) he

/-- A nonparallel second pair is forced: one opposite pair cannot recover
an anchor difference whose diagonal slope vanishes. -/
theorem two_opposite_pairs_of_linear_identity (u : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (hs : ∀ j, u j 0 + u j 1 ≠ 0)
    (hno : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j)
    (h : ∀ a b : ℝ, a - b = ∑ j, c j * relu (u j 0 * a + u j 1 * b)) :
    ∃ j k l m : ι, ∃ a b : ℝ,
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
      a < 0 ∧ b < 0 ∧ u k = a • u j ∧ u m = b • u l ∧
      u j 0 * u l 1 - u j 1 * u l 0 ≠ 0 := by
  classical
  obtain ⟨j, hcj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have bad := h 1 0
    simp only [hn, zero_mul, Finset.sum_const_zero] at bad
    norm_num at bad
  obtain ⟨k, hkj, hck, a, ha, hka⟩ :=
    opposite_partner_of_linear_identity u c hs hno h j hcj
  have hjarg : u j 0 * u j 1 + u j 1 * -u j 0 = 0 := by ring
  have hkarg : u k 0 * u j 1 + u k 1 * -u j 0 = 0 := by
    rw [hka]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨l, hlj, hlk, hcl⟩ : ∃ l, l ≠ j ∧ l ≠ k ∧ c l ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : ∑ i, c i * relu (u i 0 * u j 1 + u i 1 * -u j 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hij : i = j
      · subst i
        rw [hjarg]
        simp [relu]
      · by_cases hik : i = k
        · subst i
          rw [hkarg]
          simp [relu]
        · rw [hn i hij hik, zero_mul]
    have bad := h (u j 1) (-u j 0)
    rw [hz] at bad
    exact hs j (by linarith only [bad])
  obtain ⟨m, hml, hcm, b, hb, hmb⟩ :=
    opposite_partner_of_linear_identity u c hs hno h l hcl
  have hmj : m ≠ j := by
    intro he
    subst m
    have hkl : u k = (a * b) • u l := by rw [hka, hmb, smul_smul]
    exact hno k l hlk.symm (a * b) (mul_pos_of_neg_of_neg ha hb) hkl
  have hmk : m ≠ k := by
    intro he
    subst m
    have hlj' : u l = (a / b) • u j := by
      calc
        u l = b⁻¹ • u k := by rw [hmb, smul_smul, inv_mul_cancel hb.ne, one_smul]
        _ = (a / b) • u j := by rw [hka, smul_smul]; congr 1; ring
    exact hno l j hlj (a / b) (div_pos_of_neg_of_neg ha hb) hlj'
  have hdet : u j 0 * u l 1 - u j 1 * u l 0 ≠ 0 := by
    intro hd
    let r : ℝ := (u l 0 + u l 1) / (u j 0 + u j 1)
    have hr0 : r ≠ 0 := div_ne_zero (hs l) (hs j)
    have hc : u l 0 = r * u j 0 := by
      dsimp [r]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (hs j)).mpr
      nlinarith only [hd]
    have hmul : r * (u j 0 + u j 1) = u l 0 + u l 1 :=
      div_mul_cancel _ (hs j)
    have he : u l = r • u j := by
      funext i
      fin_cases i
      · exact hc
      · change u l 1 = r * u j 1
        nlinarith only [hc, hmul]
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact hlk (negative_partners_unique u hno hrneg ha he hka)
    · exact hno l j hlj r hrpos he
  exact ⟨j, k, l, m, a, b, hkj.symm, hlj.symm, hmj.symm,
    hlk.symm, hmk.symm, hml.symm, ha, hb, hka, hmb, hdet⟩

/-- With exactly four ridge features, the two opposite pairs exhaust them. -/
theorem four_ridges_pair (u : Fin 4 → Fin 2 → ℝ) (c : Fin 4 → ℝ)
    (hs : ∀ j, u j 0 + u j 1 ≠ 0)
    (hno : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j)
    (h : ∀ a b : ℝ, a - b = ∑ j, c j * relu (u j 0 * a + u j 1 * b)) :
    ∃ j k l m : Fin 4, ∃ a b : ℝ,
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
      a < 0 ∧ b < 0 ∧ u k = a • u j ∧ u m = b • u l ∧
      u j 0 * u l 1 - u j 1 * u l 0 ≠ 0 ∧
      ∀ i, i = j ∨ i = k ∨ i = l ∨ i = m := by
  classical
  obtain ⟨j,k,l,m,a,b,hjk,hjl,hjm,hkl,hkm,hlm,ha,hb,hka,hmb,hdet⟩ :=
    two_opposite_pairs_of_linear_identity u c hs hno h
  refine ⟨j,k,l,m,a,b,hjk,hjl,hjm,hkl,hkm,hlm,ha,hb,hka,hmb,hdet,?_⟩
  have hc : ({j,k,l,m} : Finset (Fin 4)).card = 4 := by
    simp [hjk, hjl, hjm, hkl, hkm, hlm]
  have hu : ({j,k,l,m} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hc)
  intro i
  have hi : i ∈ ({j,k,l,m} : Finset (Fin 4)) := by rw [hu]; exact Finset.mem_univ i
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hi

/-- The subtype-indexed version used by the four actual carrier neurons. -/
theorem four_ridges_pair_of_card_eq (hcard : Fintype.card ι = 4)
    (u : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (hs : ∀ j, u j 0 + u j 1 ≠ 0)
    (hno : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j)
    (h : ∀ a b : ℝ, a - b = ∑ j, c j * relu (u j 0 * a + u j 1 * b)) :
    ∃ j k l m : ι, ∃ a b : ℝ,
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
      a < 0 ∧ b < 0 ∧ u k = a • u j ∧ u m = b • u l ∧
      u j 0 * u l 1 - u j 1 * u l 0 ≠ 0 ∧
      ∀ i, i = j ∨ i = k ∨ i = l ∨ i = m := by
  classical
  obtain ⟨j,k,l,m,a,b,hjk,hjl,hjm,hkl,hkm,hlm,ha,hb,hka,hmb,hdet⟩ :=
    two_opposite_pairs_of_linear_identity u c hs hno h
  refine ⟨j,k,l,m,a,b,hjk,hjl,hjm,hkl,hkm,hlm,ha,hb,hka,hmb,hdet,?_⟩
  have hc : ({j,k,l,m} : Finset ι).card = 4 := by
    simp [hjk, hjl, hjm, hkl, hkm, hlm]
  have hu : ({j,k,l,m} : Finset ι) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa only [hcard] using hc)
  intro i
  have hi : i ∈ ({j,k,l,m} : Finset ι) := by rw [hu]; exact Finset.mem_univ i
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hi

#check @four_ridges_pair_of_card_eq
#print axioms opposite_partner_of_linear_identity
#print axioms two_opposite_pairs_of_linear_identity
#print axioms four_ridges_pair
#print axioms four_ridges_pair_of_card_eq
end MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
