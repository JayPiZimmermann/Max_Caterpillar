import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.CarrierPlane

/-! # Actual width-six networks on the two-invariant-row stratum

This conclusion concerns the weight rows of every exact network, including
networks with arbitrary biases. The proof applies the bias-free recession,
which preserves all first-layer weights and the second hidden width.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65
open BigOperators Frontier

/-- The two comparison directions together with the carrier anchor plane.
This is an output certificate of the actual-network theorem below. -/
structure TwoInvariantAnchorFrame {h₂ : ℕ} (net : Network 4 6 h₂) where
  firstRoot : Fin 6
  secondRoot : Fin 6
  p : Fin 4
  q : Fin 4
  r : Fin 4
  s : Fin 4
  firstScale : ℝ
  secondScale : ℝ
  roots_ne : firstRoot ≠ secondRoot
  invariant_rows : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0) =
    {firstRoot, secondRoot}
  pq_ne : p ≠ q
  rs_ne : r ≠ s
  pr_ne : p ≠ r
  ps_ne : p ≠ s
  qr_ne : q ≠ r
  qs_ne : q ≠ s
  firstScale_pos : 0 < firstScale
  secondScale_pos : 0 < secondScale
  first_form : ∀ i, net.W₁ firstRoot i =
    firstScale * (if i = p then 1 else 0) - firstScale * (if i = q then 1 else 0)
  second_form : ∀ i, net.W₁ secondRoot i =
    secondScale * (if i = r then 1 else 0) - secondScale * (if i = s then 1 else 0)
  carrier_plane : ∀ j, (∑ i, net.W₁ j i) ≠ 0 →
    ∀ i, i ≠ q → i ≠ s → net.W₁ j i = 0

/-- Every exact first-width-six Max4 network with exactly two invariant
rows has all four remaining rows in the inactive two-anchor plane. -/
theorem exists_twoInvariantAnchorFrame {h₂ : ℕ} (net : Network 4 6 h₂)
    (hexact : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2) :
    Nonempty (TwoInvariantAnchorFrame net) := by
  classical
  obtain ⟨j,k,p,q,r,s,ca,cb,hjk,hset,hpq,hrs,hpr,hps,hqr,hqs,hca,hcb,hAj,hAk⟩ :=
    max4_two_invariant_rows_are_complementary_roots net hexact hcard
  have hcounts : (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 2 ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0).card = 2 := by
    rcases max4_six_slope_counts net hexact with hp | hm
    · exact ⟨hp.1, hp.2.1⟩
    · have hbad := hm.2.2
      rw [hcard] at hbad
      contradiction
  obtain ⟨a,b,hab,hpos⟩ := Finset.card_eq_two.mp hcounts.1
  obtain ⟨c,d,hcd,hneg⟩ := Finset.card_eq_two.mp hcounts.2
  have hroots : ∀ e, net.toZ.s e = 0 →
      (∃ t : ℝ, 0 < t ∧ net.toZ.A e = t • (unitVec p - unitVec q)) ∨
      (∃ t : ℝ, 0 < t ∧ net.toZ.A e = t • (unitVec r - unitVec s)) := by
    intro e he
    have hm : e ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ZNet.s,
        Network.toZ] using he
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Or.inl ⟨ca,hca,root_vector_of_coordinates _ p q ca hAj⟩
    · exact Or.inr ⟨cb,hcb,root_vector_of_coordinates _ r s cb hAk⟩
  have hposcarriers : ∀ e, 0 < (1 : ℝ) * net.toZ.s e → e = a ∨ e = b := by
    intro e he
    have hm : e ∈ Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i := by
      simpa only [one_mul, Finset.mem_filter, Finset.mem_univ, true_and,
        ZNet.s, Network.toZ] using he
    rw [hpos] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hnegcarriers : ∀ e, 0 < (-1 : ℝ) * net.toZ.s e → e = c ∨ e = d := by
    intro e he
    have hs : net.toZ.s e < 0 := by linarith
    have hm : e ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        ZNet.s, Network.toZ] using hs
    rw [hneg] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hpgeom := two_carriers_anchor_geometry net.toZ (net.toZ_eval_of_max hexact)
    p q r s hpq hpr hps hqr hqs hrs hroots 1 (by norm_num) a b hposcarriers
  have hngeom := two_carriers_anchor_geometry net.toZ (net.toZ_eval_of_max hexact)
    p q r s hpq hpr hps hqr hqs hrs hroots (-1) (by norm_num) c d hnegcarriers
  refine ⟨⟨j,k,p,q,r,s,ca,cb,hjk,hset,hpq,hrs,hpr,hps,hqr,hqs,hca,hcb,hAj,hAk,?_⟩⟩
  intro e he i hiq his
  rcases lt_or_gt_of_ne he with he | he
  · have hm : e ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0 := by simp [he]
    rw [hneg] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact (hngeom.2 i hiq his).1
    · exact (hngeom.2 i hiq his).2
  · have hm : e ∈ Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i := by simp [he]
    rw [hpos] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact (hpgeom.2 i hiq his).1
    · exact (hpgeom.2 i hiq his).2

#check @exists_twoInvariantAnchorFrame
#print axioms exists_twoInvariantAnchorFrame
end MaxCaterpillar.Fiber.Count65
