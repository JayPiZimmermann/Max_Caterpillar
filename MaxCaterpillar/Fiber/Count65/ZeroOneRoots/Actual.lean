import MaxCaterpillar.Fiber.Count65.ZeroOneRoots.Exclusion
import MaxCaterpillar.Fiber.Count65.FourFeatures
import MaxCaterpillar.Fiber.Count65.ZeroPatterns

/-! # Actual width-six networks have at least two invariant root rows

The circuit and all feature representations are constructed from the
network. There is no first-layer classification assumption.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ZeroOneRoots
open BigOperators Frontier

private theorem no_representation_with_three_large_rows (A : Fin 4 → Point 4)
    (ell : Point 4) (Phi : (Fin 4 → ℝ) → ℝ)
    (h : ∀ x, Maximum 4 x = lin ell x + Phi (fun j => relu (lin (A j) x)))
    (hph : ∀ z t, 0 < t → Phi (t • z) = t * Phi z)
    (hsum : ∀ j, ∑ i, A j i = 0)
    (hcover : ∀ i, ∃ j, A j i = 0)
    (hmin : ∀ j, 2 ≤ (nonzeroCoordinates (A j)).card)
    (hn : 3 ≤ (Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card).card) :
    False := by
  classical
  have hused : ∀ i, ∃ j k, j ≠ k ∧ A j i ≠ 0 ∧ A k i ≠ 0 := by
    by_cases hall : ∀ j, 3 ≤ (nonzeroCoordinates (A j)).card
    · exact four_large_rows_columns_used A hall hcover
    · push_neg at hall
      obtain ⟨r, hr⟩ := hall
      have hlarge : ∀ j, j ≠ r → 3 ≤ (nonzeroCoordinates (A j)).card := by
        intro j hjr
        by_contra hj
        have hsub : (Finset.univ.filter fun k => 3 ≤ (nonzeroCoordinates (A k)).card) ⊆
            ((Finset.univ : Finset (Fin 4)).erase r).erase j := by
          intro k hk
          have hk' := (Finset.mem_filter.mp hk).2
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩⟩
          · intro hkj
            exact hj (hkj ▸ hk')
          · intro hkr
            exact not_le_of_gt hr (hkr ▸ hk')
        have hc := Finset.card_le_of_subset hsub
        have he : (((Finset.univ : Finset (Fin 4)).erase r).erase j).card = 2 := by
          simp [hjr]
        rw [he] at hc
        linarith only [hn, hc]
      obtain ⟨u, v, hu, hv, huv⟩ :=
        Finset.one_lt_card_iff.mp (show 1 < (nonzeroCoordinates (A r)).card by
          exact lt_of_lt_of_le (by norm_num : 1 < 2) (hmin r))
      exact three_large_rows_columns_used A r u v huv
        ((mem_nonzeroCoordinates (A r) u).mp hu)
        ((mem_nonzeroCoordinates (A r) v).mp hv) hlarge hcover
  exact no_four_features_with_three_nonroots A ell Phi h hph hsum hcover hused hn

/-- Every actual exact Max4 network in the four-invariant-row stratum has
two distinct invariant coordinate-difference rows. Support cardinality two
is equivalent to a positively scaled, oriented root by
`positive_coordinate_difference_of_card_two`. Biases are arbitrary. -/
theorem max4_four_invariant_rows_have_two_roots (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4) :
    ∃ j k : Fin 6, j ≠ k ∧ (∑ i, net.W₁ j i) = 0 ∧ (∑ i, net.W₁ k i) = 0 ∧
      (nonzeroCoordinates (net.W₁ j)).card = 2 ∧
      (nonzeroCoordinates (net.W₁ k)).card = 2 := by
  classical
  obtain ⟨e, ell, Phi, hfactor, _, hph, _, hsum, hcover, _⟩ :=
    four_feature_factorization net hnet hcard
  let A : Fin 4 → Point 4 := fun j => net.W₁ (e j).val
  have hmin : ∀ j, 2 ≤ (nonzeroCoordinates (A j)).card := by
    intro j
    apply two_le_card_nonzeroCoordinates (A j) (hsum j)
    intro he
    obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six hnet (e j).val
    exact hi (congr_fun he i)
  have hfirst : ∃ p, (nonzeroCoordinates (A p)).card = 2 := by
    by_contra hn
    push_neg at hn
    have hlarge : ∀ j, 3 ≤ (nonzeroCoordinates (A j)).card := by
      intro j
      exact Nat.succ_le_of_lt (lt_of_le_of_ne (hmin j) (Ne.symm (hn j)))
    have hN : (Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card) =
        Finset.univ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlarge j]
    apply no_representation_with_three_large_rows A ell Phi hfactor hph hsum hcover hmin
    rw [hN, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, hp⟩ := hfirst
  have hsecond : ∃ q, q ≠ p ∧ (nonzeroCoordinates (A q)).card = 2 := by
    by_contra hn
    push_neg at hn
    have hlarge : ∀ j, j ≠ p → 3 ≤ (nonzeroCoordinates (A j)).card := by
      intro j hj
      exact Nat.succ_le_of_lt (lt_of_le_of_ne (hmin j) (Ne.symm (hn j hj)))
    have hsub : (Finset.univ : Finset (Fin 4)).erase p ⊆
        Finset.univ.filter fun j => 3 ≤ (nonzeroCoordinates (A j)).card := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlarge j (Finset.ne_of_mem_erase hj)⟩
    have hc := Finset.card_le_of_subset hsub
    have he : ((Finset.univ : Finset (Fin 4)).erase p).card = 3 := by simp
    rw [he] at hc
    exact no_representation_with_three_large_rows A ell Phi hfactor hph hsum hcover hmin hc
  obtain ⟨q, hqp, hq⟩ := hsecond
  refine ⟨(e p).val, (e q).val, ?_, hsum p, hsum q, hp, hq⟩
  intro he
  exact hqp (e.injective (Subtype.ext he)).symm

end MaxCaterpillar.Fiber.Count65.ZeroOneRoots
