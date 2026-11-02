import MaxCaterpillar.Fiber.Mixed65.PhysicalMinimalExtraction

/-!
# Every physical mixed completion has exactly three positive and two negative outputs

The proof uses both actual diagonal tails. Each tail contains two positive
residual facet carriers and a negative residual gate. Its passing slope then
supplies the missing output sign. Five physical gates saturate these bounds.
No output normalization or residual normal form is assumed.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Mixed65

private theorem tail_represents (net : Network 4 6 5) (t : ℝ) (a : Fin 5 → ℝ)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j in Finset.univ.filter (fun j => 0 < a j),
        net.w₃ j * physicalInvariantPart net t j x) +
      ∑ j in Finset.univ.filter (fun j => a j = 0),
        net.w₃ j * relu (physicalInvariantPart net t j x)) :
    (physicalResidualSystem net (Finset.univ.filter (fun j => a j = 0))
      (fun j => if 0 < a j then net.w₃ j else 0)).Represents t := by
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
theorem physical_three_positive_outputs (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < net.w₃ i ∧ 0 < net.w₃ j ∧ 0 < net.w₃ k := by
  classical
  obtain ⟨hplus, _, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  let a : Fin 5 → ℝ := fun j => net.W₂ j 4
  let S : Finset (Fin 5) := Finset.univ.filter fun j => a j = 0
  let d := physicalResidualSystem net S (fun j => if 0 < a j then net.w₃ j else 0)
  have hd : d.Represents t := tail_represents net t a (fun x => (hrem x).1)
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := d.two_positive_carriers t ht hd
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
theorem physical_two_negative_outputs (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ i j : Fin 5, i ≠ j ∧ net.w₃ i < 0 ∧ net.w₃ j < 0 := by
  classical
  obtain ⟨_, hminus, hrem⟩ := physical_recession_diagonal_extraction net t hW hmax
  let a : Fin 5 → ℝ := fun j => net.W₂ j 5
  let S : Finset (Fin 5) := Finset.univ.filter fun j => a j = 0
  let d := physicalResidualSystem net S (fun j => if 0 < a j then net.w₃ j else 0)
  have hd : d.Represents t := tail_represents net t a (fun x => (hrem x).2)
  obtain ⟨i, hi⟩ := d.exists_negative_gate t ht hd
  obtain ⟨j, hja, hj⟩ := exists_negative_passing_of_slope net.w₃ a
    (by simpa only [a, hminus] using (show (-1 : ℝ) < 0 by norm_num))
  have hia : a i.val = 0 := (Finset.mem_filter.mp i.property).2
  refine ⟨i.val, j, ?_, hi, hj⟩
  intro he
  rw [he] at hia
  linarith only [hja, hia]

/-- The exact physical sign counts. All five outputs are nonzero. -/
theorem physical_output_sign_counts (net : Network 4 6 5) (t : ℝ) (ht : 0 < t)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    (Finset.univ.filter fun i => 0 < net.w₃ i).card = 3 ∧
      (Finset.univ.filter fun i => net.w₃ i < 0).card = 2 ∧
      ∀ i, net.w₃ i ≠ 0 := by
  classical
  let P : Finset (Fin 5) := Finset.univ.filter fun i => 0 < net.w₃ i
  let N : Finset (Fin 5) := Finset.univ.filter fun i => net.w₃ i < 0
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    physical_three_positive_outputs net t ht hW hmax
  have hP : 3 ≤ P.card := by
    have hsub : ({i, j, k} : Finset (Fin 5)) ⊆ P := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> simp [P, hi, hj, hk]
    have hc : ({i, j, k} : Finset (Fin 5)).card = 3 := by simp [hij, hik, hjk]
    simpa only [hc] using Finset.card_le_of_subset hsub
  obtain ⟨u, v, huv, hu, hv⟩ := physical_two_negative_outputs net t ht hW hmax
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

end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
