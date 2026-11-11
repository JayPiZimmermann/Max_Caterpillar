import MaxCaterpillar.Fiber.Count65.Star.PhysicalBridge
import MaxCaterpillar.Fiber.Count65.Star.CarrierForcing
import MaxCaterpillar.Fiber.Mixed65.MinimalExtraction

/-! # Exact output signs of every actual star completion

Both physical diagonal tails force residual facet carriers and a negative core;
the passing tail slope adds the missing sign. Five neurons saturate the bounds.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Mixed65 (finite_signed_carrier_extraction
  exists_positive_passing_of_slope exists_negative_passing_of_slope)

variable {m : ℕ}
/-- Collecting a linear combination changes only the four remainder
coefficients; it does not change any original residual gate. -/
theorem physicalInvariantPart_linearCombination (net : Network 4 6 m)
    (t : ℝ) (l : Fin m → ℝ) (x : InvariantState) :
    (∑ j, l j * physicalInvariantPart net t j x) =
      readout t (∑ j, l j * net.W₂ j 0) (∑ j, l j * net.W₂ j 1)
        (∑ j, l j * net.W₂ j 2) (∑ j, l j * net.W₂ j 3) x := by
  simp only [physicalInvariantPart, readout, starLinearForm, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

/-- The extracted system retains the selected physical gate coefficients;
only the remainder is collected into four coefficients. -/
noncomputable def physicalResidualSystem (net : Network 4 6 m)
    (S : Finset (Fin m)) (l : Fin m → ℝ) : CoefficientSystem S := {
    lU := ∑ j, l j * net.W₂ j 0
    lV := ∑ j, l j * net.W₂ j 1
    lW := ∑ j, l j * net.W₂ j 2
    lT := ∑ j, l j * net.W₂ j 3
    out := fun j => net.w₃ j.val
    U := fun j => net.W₂ j.val 0
    V := fun j => net.W₂ j.val 1
    W := fun j => net.W₂ j.val 2
    T := fun j => net.W₂ j.val 3 }

theorem physicalResidualSystem_represents (net : Network 4 6 m) (t : ℝ)
    (S : Finset (Fin m)) (l : Fin m → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j, l j * physicalInvariantPart net t j x) +
        ∑ j in S, net.w₃ j * relu (physicalInvariantPart net t j x)) :
    RepresentsStar (physicalResidualSystem net S l) t := by
  intro q b c
  have hh := h (q, b, c)
  have htgt : max (max 0 (q+b)) (max b (relu c))=invariantTarget (q,b,c) := by
    change max (max 0 (q+b)) (max b (max 0 c))=max (max (q+b) b) (max 0 c)
    ac_rfl
  change max (max 0 (q+b)) (max b (relu c)) = _
  rw [htgt]
  rw [physicalInvariantPart_linearCombination] at hh
  change invariantTarget (q, b, c) =
    readout t (∑ j, l j * net.W₂ j 0) (∑ j, l j * net.W₂ j 1)
      (∑ j, l j * net.W₂ j 2) (∑ j, l j * net.W₂ j 3) (q, b, c) +
    ∑ j : S, net.w₃ j.val * relu (physicalInvariantPart net t j.val (q, b, c))
  rw [Finset.sum_coe_sort S
    (fun j => net.w₃ j * relu (physicalInvariantPart net t j (q, b, c)))]
  exact hh

/-- Both diagonal tails are valid with arbitrary original biases, because the
underlying weight arrays are unchanged by the proved recession operation. -/
theorem physical_recession_diagonal_extraction (net : Network 4 6 m) (t : ℝ)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 4),
      net.w₃ j * net.W₂ j 4) = 1 ∧
    (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 5),
      net.w₃ j * net.W₂ j 5) = -1 ∧
    ∀ x : InvariantState,
      (invariantTarget x =
        (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 4),
          net.w₃ j * physicalInvariantPart net t j x) +
        ∑ j in Finset.univ.filter (fun j => net.W₂ j 4 = 0),
          net.w₃ j * relu (physicalInvariantPart net t j x)) ∧
      (invariantTarget x =
        (∑ j in Finset.univ.filter (fun j => 0 < net.W₂ j 5),
          net.w₃ j * physicalInvariantPart net t j x) +
        ∑ j in Finset.univ.filter (fun j => net.W₂ j 5 = 0),
          net.w₃ j * relu (physicalInvariantPart net t j x)) := by
  classical
  exact finite_signed_carrier_extraction net.w₃ (fun j => net.W₂ j 4)
    (fun j => net.W₂ j 5) (physicalInvariantPart net t) invariantTarget
    (physical_signed_carrier_identity_any_bias net t hW hmax)

/-- The arbitrary finite residual floor, applied to any subset of actual
physical neurons and any feature-linear remainder. -/
theorem physical_residual_card_ge_three (net : Network 4 6 m) (t : ℝ)
    (ht : 0 < t) (ht1 : t≤1) (S : Finset (Fin m)) (l : Fin m → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j, l j * physicalInvariantPart net t j x) +
        ∑ j in S, net.w₃ j * relu (physicalInvariantPart net t j x)) :
    3 ≤ S.card := by
  classical
  simpa only [Fintype.card_coe] using
    residual_card_ge_three (physicalResidualSystem net S l) t ht ht1
      (physicalResidualSystem_represents net t S l h)

/-- Each translation tail leaves at least three neurons with zero slope.
No output sign or nonzero-weight hypothesis is imposed. -/
theorem physical_zero_carrier_cards (net : Network 4 6 m) (t : ℝ) (ht : 0 < t) (ht1 : t≤1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ y, net.eval y = Maximum 4 y) :
    3 ≤ (Finset.univ.filter fun j => net.W₂ j 4 = 0).card ∧
    3 ≤ (Finset.univ.filter fun j => net.W₂ j 5 = 0).card := by
  classical
  obtain ⟨_, _, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  constructor
  · apply physical_residual_card_ge_three net t ht ht1
      (Finset.univ.filter fun j => net.W₂ j 4 = 0)
      (fun j => if 0 < net.W₂ j 4 then net.w₃ j else 0)
    intro x
    convert (hrem x).1 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj <;> simp [hj]
  · apply physical_residual_card_ge_three net t ht ht1
      (Finset.univ.filter fun j => net.W₂ j 5 = 0)
      (fun j => if 0 < net.W₂ j 5 then net.w₃ j else 0)
    intro x
    convert (hrem x).2 using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj <;> simp [hj]

private theorem tail_represents (net : Network 4 6 5) (t : ℝ) (a : Fin 5 → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j in Finset.univ.filter (fun j => 0 < a j),
        net.w₃ j * physicalInvariantPart net t j x) +
      ∑ j in Finset.univ.filter (fun j => a j = 0),
        net.w₃ j * relu (physicalInvariantPart net t j x)) :
    RepresentsStar (physicalResidualSystem net (Finset.univ.filter (fun j => a j = 0))
      (fun j => if 0 < a j then net.w₃ j else 0)) t := by
  classical
  apply physicalResidualSystem_represents
  intro x
  convert h x using 1
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hh <;> simp [hh]

/-- There are three distinct positive-output physical neurons. -/
theorem physical_three_positive_outputs (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t≤1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < net.w₃ i ∧ 0 < net.w₃ j ∧ 0 < net.w₃ k := by
  classical
  obtain ⟨hplus, _, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  let a : Fin 5 → ℝ := fun j => net.W₂ j 4
  let S : Finset (Fin 5) := Finset.univ.filter fun j => a j = 0
  let d := physicalResidualSystem net S (fun j => if 0 < a j then net.w₃ j else 0)
  have hd : RepresentsStar d t := tail_represents net t a (fun x => (hrem x).1)
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := two_positive_carriers d t ht ht1 hd
  obtain ⟨k, hka, hk⟩ := exists_positive_passing_of_slope net.w₃ a
    (by simpa only [a, hplus] using (show (0 : ℝ) < 1 by norm_num))
  have hia : a i.val = 0 := (Finset.mem_filter.mp i.property).2
  have hja : a j.val = 0 := (Finset.mem_filter.mp j.property).2
  refine ⟨i.val, j.val, k, ?_, ?_, ?_, hi, hj, hk⟩
  · intro he
    exact hij (Subtype.ext he)
  · intro he
    rw [he] at hia
    linarith only [hka, hia]
  · intro he
    rw [he] at hja
    linarith only [hka, hja]

/-- There are two distinct negative-output physical neurons. -/
theorem physical_two_negative_outputs (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t≤1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ i j : Fin 5, i ≠ j ∧ net.w₃ i < 0 ∧ net.w₃ j < 0 := by
  classical
  obtain ⟨_, hminus, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  let a : Fin 5 → ℝ := fun j => net.W₂ j 5
  let S : Finset (Fin 5) := Finset.univ.filter fun j => a j = 0
  let d := physicalResidualSystem net S (fun j => if 0 < a j then net.w₃ j else 0)
  have hd : RepresentsStar d t := tail_represents net t a (fun x => (hrem x).2)
  obtain ⟨i, hi⟩ := exists_negative_gate d t ht ht1 hd
  obtain ⟨j, hja, hj⟩ := exists_negative_passing_of_slope net.w₃ a
    (by simpa only [a, hminus] using (show (-1 : ℝ) < 0 by norm_num))
  have hia : a i.val = 0 := (Finset.mem_filter.mp i.property).2
  refine ⟨i.val, j, ?_, hi, hj⟩
  intro he
  rw [he] at hia
  linarith only [hja, hia]

/-- The exact physical sign counts. All five outputs are nonzero. -/
theorem physical_output_sign_counts (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t≤1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    (Finset.univ.filter fun i => 0 < net.w₃ i).card = 3 ∧
      (Finset.univ.filter fun i => net.w₃ i < 0).card = 2 ∧
      ∀ i, net.w₃ i ≠ 0 := by
  classical
  let P : Finset (Fin 5) := Finset.univ.filter fun i => 0 < net.w₃ i
  let N : Finset (Fin 5) := Finset.univ.filter fun i => net.w₃ i < 0
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    physical_three_positive_outputs net t ht ht1 hW hmax
  have hP : 3 ≤ P.card := by
    have hsub : ({i, j, k} : Finset (Fin 5)) ⊆ P := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [P, hi, hj, hk]
    have hc : ({i, j, k} : Finset (Fin 5)).card = 3 := by simp [hij, hik, hjk]
    simpa only [hc] using Finset.card_le_of_subset hsub
  obtain ⟨u, v, huv, hu, hv⟩ := physical_two_negative_outputs net t ht ht1 hW hmax
  have hN : 2 ≤ N.card := by
    have hsub : ({u, v} : Finset (Fin 5)) ⊆ N := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp [N, hu, hv]
    have hc : ({u, v} : Finset (Fin 5)).card = 2 := by simp [huv]
    simpa only [hc] using Finset.card_le_of_subset hsub
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hpa := (Finset.mem_filter.mp ha).2
    have hna := (Finset.mem_filter.mp hb).2
    linarith only [hpa, hna]
  have htotal : P.card + N.card ≤ 5 := by
    rw [← Finset.card_union_eq hdisj]
    exact Finset.card_le_univ _
  have heP : P.card = 3 := by linarith only [hP, hN, htotal]
  have heN : N.card = 2 := by linarith only [hP, hN, htotal]
  have huall : P ∪ N = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_eq hdisj, heP, heN]
    norm_num
  refine ⟨heP, heN, ?_⟩
  intro a
  have ham : a ∈ P ∪ N := by rw [huall]; exact Finset.mem_univ a
  rcases Finset.mem_union.mp ham with ha | ha
  · exact ((Finset.mem_filter.mp ha).2).ne'
  · exact ((Finset.mem_filter.mp ha).2).ne


end MaxCaterpillar.Fiber.Count65.Star
