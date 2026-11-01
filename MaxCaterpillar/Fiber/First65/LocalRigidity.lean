import MaxCaterpillar.Fiber.First65.LocalWitnesses

/-! # Exact local mixed rigidity from finite first-state certificates

This theorem applies to arbitrary real weights and biases and arbitrary
second hidden width. The certificate is an open, nonvacuous condition on
the first matrix; exactness is required on every input.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MaxCaterpillar.Fiber.Mixed65

open BigOperators Frontier

variable {h₂ : ℕ}

@[simp] private theorem fin4_succ_two : (Fin.succ 2 : Fin 4) = 3 := rfl
@[simp] private theorem vec4_three {α : Type*} (a b c d : α) :
    (![a,b,c,d] : Fin 4 → α) 3 = d := rfl
@[simp] private theorem vec6_three {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 3 = d := rfl
@[simp] private theorem vec6_four {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 4 = e := rfl
@[simp] private theorem vec6_five {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 5 = f := rfl

theorem LocalCertificate.scaled_mixed_rows (t : ℝ) (ht : 0 < t)
    (net : Network 4 6 h₂) (h : ∀ x, net.eval x = Maximum 4 x)
    (hc : LocalCertificate t net.W₁) :
    ∃ u : ℝ, 0 < u ∧ ∃ c : Fin 6 → ℝ,
      (∀ j, 0 < c j) ∧ ∀ j, net.W₁ j = c j • firstRows u j := by
  classical
  let A := net.W₁
  have h4 : ∀ j, j ≠ (2 : Fin 4) → A 4 j = 0 :=
    row_support_of_single_active net h (carrierPlusPoint t) 4 2
      hc.carrierPlus (carrierPlusPoint_winner t ht)
  have h5 : ∀ j, j ≠ (2 : Fin 4) → A 5 j = 0 :=
    row_support_of_single_active net h (carrierMinusPoint t) 5 2
      hc.carrierMinus (carrierMinusPoint_winner t ht)
  have hB : ∀ j, j ≠ (1 : Fin 4) → j ≠ (2 : Fin 4) → A 1 j = 0 :=
    row_support_of_two_active net h bPoint 1 4 1 2 (by decide)
      hc.bCell bPoint_winner h4
  have hC : ∀ j, j ≠ (3 : Fin 4) → j ≠ (2 : Fin 4) → A 2 j = 0 :=
    row_support_of_two_active net h (cPoint t) 2 4 3 2 (by decide)
      hc.cCell (cPoint_winner t ht) h4
  have b0 : A 1 0 = 0 := hB 0 (by decide) (by decide)
  have b3 : A 1 3 = 0 := hB 3 (by decide) (by decide)
  have c0 : A 2 0 = 0 := hC 0 (by decide) (by decide)
  have c1 : A 2 1 = 0 := hC 1 (by decide) (by decide)
  have bplus := row_nonneg_of_two_active net h bTiePlus 1 4 1 2 (by decide)
    hc.bTiePlusCell bTiePlus_winner h4
  have bminus := row_nonneg_of_two_active net h bTieMinus 1 5 1 2 (by decide)
    hc.bTieMinusCell bTieMinus_winner h5
  change 0 ≤ lin (A 1) bTiePlus at bplus
  change 0 ≤ lin (A 1) bTieMinus at bminus
  simp [lin, bTiePlus, bTieMinus, Fin.sum_univ_succ, b0, b3] at bplus bminus
  have b2 : A 1 2 = -A 1 1 := by linarith
  have cplus := row_nonneg_of_two_active net h (cTiePlus t) 2 4 3 2 (by decide)
    hc.cTiePlusCell (cTiePlus_winner t ht) h4
  have cminus := row_nonneg_of_two_active net h (cTieMinus t) 2 5 3 2 (by decide)
    hc.cTieMinusCell (cTieMinus_winner t ht) h5
  change 0 ≤ lin (A 2) (cTiePlus t) at cplus
  change 0 ≤ lin (A 2) (cTieMinus t) at cminus
  simp [lin, cTiePlus, cTieMinus, Fin.sum_univ_succ, c0, c1] at cplus cminus
  have c2 : A 2 2 = -A 2 3 := by linarith
  have s1 : (∑ i, A 1 i) = 0 := by simp [Fin.sum_univ_succ, b0, b3, b2]
  have s2 : (∑ i, A 2 i) = 0 := by simp [Fin.sum_univ_succ, c0, c1, c2]
  have s4 : (∑ i, A 4 i) = A 4 2 := by
    simp [Fin.sum_univ_succ, h4 0 (by decide), h4 1 (by decide), h4 3 (by decide)]
  have s5 : (∑ i, A 5 i) = A 5 2 := by
    simp [Fin.sum_univ_succ, h5 0 (by decide), h5 1 (by decide), h5 3 (by decide)]
  have bp : 0 < A 1 1 := hc.b_pos
  have cp : 0 < A 2 3 := hc.c_pos
  have tp : 0 < A 3 0 := hc.t_pos
  have tm : 0 < A 3 2 := hc.t_mid_pos
  have p4 : 0 < A 4 2 := hc.carrier_pos
  have p5 : A 5 2 < 0 := hc.carrier_neg
  obtain ⟨j, sj, j2⟩ := max4_invariant_row_at_top_tie net h 2
  change (∑ i, A j i) = 0 at sj
  change A j 2 = 0 at j2
  have hj : j = 0 := by
    fin_cases j
    · rfl
    · change A 1 2 = 0 at j2
      rw [b2] at j2; linarith
    · change A 2 2 = 0 at j2
      rw [c2] at j2; linarith
    · change A 3 2 = 0 at j2
      linarith
    · change A 4 2 = 0 at j2
      linarith
    · change A 5 2 = 0 at j2
      linarith
  subst j
  have s0 : (∑ i, A 0 i) = 0 := sj
  have q2 : A 0 2 = 0 := j2
  have s3 : (∑ i, A 3 i) = 0 := by
    by_contra hn
    have hf : (Finset.univ.filter fun j : Fin 6 => (∑ i, A j i) = 0) = {0,1,2} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases j
      · change ((∑ i, A 0 i) = 0) ↔ (0 : Fin 6) ∈ {0,1,2}
        simp [s0]
      · change ((∑ i, A 1 i) = 0) ↔ (1 : Fin 6) ∈ {0,1,2}
        simp [s1]
      · change ((∑ i, A 2 i) = 0) ↔ (2 : Fin 6) ∈ {0,1,2}
        simp [s2]
      · change ((∑ i, A 3 i) = 0) ↔ (3 : Fin 6) ∈ {0,1,2}
        simp only [hn, false_iff]
        decide
      · change ((∑ i, A 4 i) = 0) ↔ (4 : Fin 6) ∈ {0,1,2}
        simp only [s4, ne_of_gt p4, false_iff]
        decide
      · change ((∑ i, A 5 i) = 0) ↔ (5 : Fin 6) ∈ {0,1,2}
        simp only [s5, ne_of_lt p5, false_iff]
        decide
    have hd := max4_six_invariant_row_count net h
    change (Finset.univ.filter fun j : Fin 6 => (∑ i, A j i) = 0).card = 2 ∨
      (Finset.univ.filter fun j : Fin 6 => (∑ i, A j i) = 0).card = 4 at hd
    rw [hf] at hd
    have hcard : ({0,1,2} : Finset (Fin 6)).card = 3 := by decide
    rw [hcard] at hd
    omega
  let wq : Point 4 := ![A 0 3, 0, 0, -A 0 0]
  have q3 : A 0 3 = 0 := by
    have he := net.first_kernel_top_coordinate h (qPoint t) wq (fun j hj => by
      have hm : j ∈ ({0,1,4} : Finset (Fin 6)) := by
        by_contra hn
        have hn' := hc.qCell j hn
        linarith
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · change lin (A 0) wq = 0
        simp [lin, wq, Fin.sum_univ_succ]; ring
      · change lin (A 1) wq = 0
        simp [lin, wq, Fin.sum_univ_succ, b0, b3]
      · change lin (A 4) wq = 0
        simp [lin, wq, Fin.sum_univ_succ, h4 0 (by decide), h4 3 (by decide)])
      0 (qPoint_winner t ht)
    exact he
  have q1 : A 0 1 = -A 0 0 := by
    simp [Fin.sum_univ_succ, q2, q3] at s0
    linarith
  let wt : Point 4 := ![A 3 3, A 3 3, 0, -(A 3 0 + A 3 1)]
  have t3 : A 3 3 = 0 := by
    have he := net.first_kernel_top_coordinate h tPoint wt (fun j hj => by
      have hm : j ∈ ({0,3,4} : Finset (Fin 6)) := by
        by_contra hn
        have hn' := hc.tCell j hn
        linarith
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · change lin (A 0) wt = 0
        simp [lin, wt, Fin.sum_univ_succ, q1, q2, q3]
      · change lin (A 3) wt = 0
        simp [lin, wt, Fin.sum_univ_succ]; ring
      · change lin (A 4) wt = 0
        simp [lin, wt, Fin.sum_univ_succ, h4 0 (by decide), h4 1 (by decide),
          h4 3 (by decide)]) 0 tPoint_winner
    exact he
  have t1 : A 3 1 = -(A 3 0 + A 3 2) := by
    simp [Fin.sum_univ_succ, t3] at s3
    linarith
  refine ⟨A 3 0 / A 3 2, div_pos tp tm,
    ![A 0 0, A 1 1, A 2 3, A 3 2, A 4 2, -A 5 2], ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num
    · exact hc.q_pos
    · exact bp
    · exact cp
    · exact tm
    · exact p4
    · exact p5
  · intro j
    funext i
    change A j i = _
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
      fin_cases j <;> decide
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      fin_cases i <;> decide
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hi with rfl | rfl | rfl | rfl <;>
      simp [firstRows, q1, q2, q3, b0, b2, b3, c0, c1, c2, t1, t3,
        h4 0 (by decide), h4 1 (by decide), h4 3 (by decide),
        h5 0 (by decide), h5 1 (by decide), h5 3 (by decide)]
    all_goals field_simp [ne_of_gt tm] <;> ring

end MaxCaterpillar.Fiber.Mixed65
