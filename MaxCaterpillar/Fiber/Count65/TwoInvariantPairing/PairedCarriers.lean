import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.FeatureSpan
import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.RidgePairs

/-!
# The actual four carrier rows form two opposite pairs

This completes the two-invariant-row classification of first weight rows. The
hypotheses are actual all-input network exactness and the invariant-row
count; the frame and the opposite-pair certificate are conclusions.
The second hidden width is unrestricted. Arbitrary biases are allowed because
the exact homogeneous recession preserves the first weight rows.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
open BigOperators Frontier

variable {h₂ : ℕ} {net : Network 4 6 h₂}

/-- Coordinates of a carrier in the proved inactive-anchor plane. -/
noncomputable def carrierVector (fr : TwoInvariantAnchorFrame net) (j : Fin 6) : Fin 2 → ℝ :=
  ![net.W₁ j fr.q, net.W₁ j fr.s]

lemma carrier_vector_sum (fr : TwoInvariantAnchorFrame net) (j : Fin 6)
    (hj : (∑ i, net.W₁ j i) ≠ 0) :
    carrierVector fr j 0 + carrierVector fr j 1 = ∑ i, net.W₁ j i := by
  have he := lin_supported_on_anchors fr (net.W₁ j) (fr.carrier_plane j hj) (diag 1)
  simpa [carrierVector, lin, diag] using he.symm

/-- An anchor-coordinate identity is a full incoming-row identity because
both actual carrier rows are supported on the two inactive anchors. -/
lemma carrier_row_eq_of_vector_eq (fr : TwoInvariantAnchorFrame net) (i j : Fin 6)
    (hi : (∑ k, net.W₁ i k) ≠ 0) (hj : (∑ k, net.W₁ j k) ≠ 0)
    (t : ℝ) (he : carrierVector fr i = t • carrierVector fr j) :
    net.W₁ i = t • net.W₁ j := by
  funext k
  by_cases hkq : k = fr.q
  · subst k
    have h := congr_fun he 0
    simpa [carrierVector, Pi.smul_apply, smul_eq_mul] using h
  · by_cases hks : k = fr.s
    · subst k
      have h := congr_fun he 1
      simpa [carrierVector, Pi.smul_apply, smul_eq_mul] using h
    · rw [fr.carrier_plane i hi k hkq hks]
      simp only [Pi.smul_apply, smul_eq_mul, fr.carrier_plane j hj k hkq hks, mul_zero]

/-- Explicit row data certifying both opposite pairs and their independence. -/
structure PairedCarrierCertificate (net : Network 4 6 h₂) (fr : TwoInvariantAnchorFrame net) where
  j : Fin 6
  k : Fin 6
  l : Fin 6
  m : Fin 6
  firstRatio : ℝ
  secondRatio : ℝ
  jk_ne : j ≠ k
  jl_ne : j ≠ l
  jm_ne : j ≠ m
  kl_ne : k ≠ l
  km_ne : k ≠ m
  lm_ne : l ≠ m
  j_carrier : (∑ i, net.W₁ j i) ≠ 0
  k_carrier : (∑ i, net.W₁ k i) ≠ 0
  l_carrier : (∑ i, net.W₁ l i) ≠ 0
  m_carrier : (∑ i, net.W₁ m i) ≠ 0
  firstRatio_neg : firstRatio < 0
  secondRatio_neg : secondRatio < 0
  first_pair : net.W₁ k = firstRatio • net.W₁ j
  second_pair : net.W₁ m = secondRatio • net.W₁ l
  independent : net.W₁ j fr.q * net.W₁ l fr.s - net.W₁ j fr.s * net.W₁ l fr.q ≠ 0
  exhaustive : ∀ i, (∑ a, net.W₁ i a) ≠ 0 ↔ i = j ∨ i = k ∨ i = l ∨ i = m

/-- Every actual framed width-six Max4 realization has two opposite carrier
pairs. No pairing of the four carrier features is assumed. -/
theorem exists_pairedCarrierCertificate (net : Network 4 6 h₂)
    (hexact : ∀ x, net.eval x = Maximum 4 x) (fr : TwoInvariantAnchorFrame net) :
    Nonempty (PairedCarrierCertificate net fr) := by
  classical
  let C := {j : Fin 6 // (∑ i, net.W₁ j i) ≠ 0}
  have hcardzero : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2 := by
    rw [fr.invariant_rows]
    simp [fr.roots_ne]
  have hcard : Fintype.card C = 4 := by
    change Fintype.card {j : Fin 6 // ¬(∑ i, net.W₁ j i) = 0} = 4
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype, hcardzero]
  obtain ⟨c,hc⟩ := actual_anchor_difference_feature_span net hexact fr
  let u : C → Fin 2 → ℝ := fun j => carrierVector fr j.val
  have hs : ∀ j, u j 0 + u j 1 ≠ 0 := by
    intro j
    change carrierVector fr j.val 0 + carrierVector fr j.val 1 ≠ 0
    rw [carrier_vector_sum fr j.val j.property]
    exact j.property
  have hno : ∀ i j : C, i ≠ j → ∀ t : ℝ, 0 < t → u i ≠ t • u j := by
    intro i j hij t ht he
    have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact net.first_rows_not_pos_proportional_of_max4_six hexact hij' ht
      (carrier_row_eq_of_vector_eq fr i.val j.val i.property j.property t he)
  have hidentity : ∀ a b : ℝ, a - b =
      ∑ j : C, c j.val * relu (u j 0 * a + u j 1 * b) := by
    intro a b
    calc
      a - b = ∑ j, c j * feature fr j a b := hc a b
      _ = ∑ j in Finset.univ.filter (fun j => (∑ i, net.W₁ j i) ≠ 0),
          c j * feature fr j a b := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hz : (∑ i, net.W₁ j i) = 0 := by
          by_contra hn
          exact hj (by simp [hn])
        have hm : j ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by simp [hz]
        rw [fr.invariant_rows] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl <;> simp
      _ = ∑ j : C, c j.val * feature fr j.val a b :=
        Finset.sum_subtype _ (by intro j; simp) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [carrier_feature_formula fr j.val j.property]
        rfl
  obtain ⟨j,k,l,m,a,b,hjk,hjl,hjm,hkl,hkm,hlm,ha,hb,hka,hmb,hdet,hall⟩ :=
    four_ridges_pair_of_card_eq hcard u (fun j => c j.val) hs hno hidentity
  have hval (i j : C) (hij : i ≠ j) : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  refine ⟨⟨j.val,k.val,l.val,m.val,a,b,
    hval j k hjk,hval j l hjl,hval j m hjm,hval k l hkl,hval k m hkm,hval l m hlm,
    j.property,k.property,l.property,m.property,ha,hb,
    carrier_row_eq_of_vector_eq fr k.val j.val k.property j.property a hka,
    carrier_row_eq_of_vector_eq fr m.val l.val m.property l.property b hmb,?_,?_⟩⟩
  · simpa [u,carrierVector] using hdet
  · intro i
    constructor
    · intro hi
      have hx := hall (⟨i,hi⟩ : C)
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (congrArg Subtype.val hx)
      · exact Or.inr (Or.inl (congrArg Subtype.val hx))
      · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val hx)))
      · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val hx)))
    · intro hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact j.property
      · exact k.property
      · exact l.property
      · exact m.property

/-- The complete two-invariant-row first weight-row conclusion for arbitrary
second hidden width and arbitrary biases. Both certificates are proved from
actual all-input network exactness. -/
theorem max4_two_invariant_paired_carriers (net : Network 4 6 h₂)
    (hexact : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2) :
    ∃ fr : TwoInvariantAnchorFrame net, Nonempty (PairedCarrierCertificate net fr) := by
  obtain ⟨fr⟩ := exists_twoInvariantAnchorFrame net hexact hcard
  exact ⟨fr,exists_pairedCarrierCertificate net hexact fr⟩

#check @max4_two_invariant_paired_carriers
#print axioms max4_two_invariant_paired_carriers
end MaxCaterpillar.Fiber.Count65.TwoInvariantPairing
