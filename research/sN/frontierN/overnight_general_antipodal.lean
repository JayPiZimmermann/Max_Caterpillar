import MaxCaterpillar.Frontier.SecondWidthPlus

/-!
Unrestricted second-width improvement by comparing the positive-diagonal
identity at x with the negative-diagonal identity at -x. Scratch leaf only.
-/

namespace MaxCaterpillar.Frontier.OvernightGeneral

open BigOperators FiniteDimensional

variable {N h₁ h₂ : ℕ}

/-- Comparing the two asymptotic intercepts at opposite inputs gives exactly
the linear odd part of the original second-layer preactivation. -/
lemma Gp_sub_negIn_same (net : ZNet N h₁ h₂) (k : Fin h₂) :
    ∃ b : Point N, ∀ x, net.Gp k x - net.negIn.Gp k x = lin b x := by
  refine ⟨∑ j, net.W k j • net.A j, fun x => ?_⟩
  rw [lin_sum_left]
  simp only [ZNet.Gp, ← Finset.sum_sub_distrib, ZNet.negIn_s]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ZNet.negIn, lin_neg_left, lin_smul_left, pick]
  rcases lt_trichotomy (net.s j) 0 with hj | hj | hj
  · simp [hj, not_lt.2 hj.le, neg_pos.2 hj]
  · simp only [hj, neg_zero, lt_irrefl, if_false]
    rw [← mul_sub, relu_sub_relu_neg]
  · simp [hj, not_lt.2 hj.le, neg_neg, neg_lt_zero.2 hj]

/-- Every exact two-hidden-layer network without skips has
`h₂ >= ceil(N/2)+1`, at every positive arity. -/
theorem second_width_half_plus_one [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ 2 * h₂ := by
  classical
  have b1 := net.card_Zp h
  have b2 := net.card_Zm h
  obtain ⟨hsl, hrest⟩ := net.max_plus h
  obtain ⟨hsl', hrest'⟩ := net.max_minus h
  obtain ⟨n, hTn, hdn⟩ := exists_pos_term net.d net.Tp (by
    unfold ZNet.slope at hsl; rw [hsl]; norm_num)
  obtain ⟨m, hTm, hdm⟩ := exists_neg_term net.d net.negIn.Tp (by
    unfold ZNet.slope at hsl'; simp only [ZNet.negIn] at hsl' ⊢; rw [hsl']; norm_num)
  have hnm : n ≠ m := fun e => by rw [e] at hdn; linarith
  have two : ∀ (Z : Finset (Fin h₂)) (a b : Fin h₂), a ∉ Z → b ∉ Z → a ≠ b →
      Z.card + 2 ≤ h₂ := by
    intro Z a b ha hb hab
    have he := Finset.card_le_univ (insert a (insert b Z))
    rw [Finset.card_insert_of_not_mem (by simp [hab, ha]),
      Finset.card_insert_of_not_mem hb, Fintype.card_fin] at he
    exact he
  by_cases c1 : ∃ k, k ≠ n ∧ net.Tp k ≠ 0
  · obtain ⟨k, hkn, hk⟩ := c1
    have he := two (Finset.univ.filter fun k => net.Tp k = 0) n k
      (by simp [hTn.ne']) (by simp [hk]) hkn.symm
    linarith
  by_cases c2 : ∃ k, k ≠ m ∧ net.negIn.Tp k ≠ 0
  · obtain ⟨k, hkm, hk⟩ := c2
    have he := two (Finset.univ.filter fun k => net.negIn.Tp k = 0) m k
      (by simp [hTm.ne']) (by simp [hk]) hkm.symm
    linarith
  push_neg at c1 c2
  let K := (Finset.univ.erase n).erase m
  have hm : m ∈ Finset.univ.erase n := Finset.mem_erase.2 ⟨hnm.symm, Finset.mem_univ m⟩
  have htwo : 2 ≤ h₂ := by
    have he := Finset.card_le_univ ({n,m} : Finset (Fin h₂))
    rwa [Finset.card_doubleton hnm, Fintype.card_fin] at he
  have hK : K.card + 2 = h₂ := by
    simp only [K, Finset.card_erase_of_mem hm, Finset.card_erase_of_mem (Finset.mem_univ n),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hKn : ∀ k ∈ K, k ≠ n ∧ k ≠ m := by
    intro k hk
    exact ⟨(Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1,
      (Finset.mem_erase.1 hk).1⟩
  have split : ∀ f : Fin h₂ → ℝ, ∑ k, f k = f n + f m + ∑ k in K, f k := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n), ← Finset.add_sum_erase _ _ hm]
    ring
  have Ep : ∀ x, Maximum N x = net.d n * net.Gp n x +
      net.d m * relu (net.Gp m x) + ∑ k in K, net.d k * relu (net.Gp k x) := by
    intro x
    rw [hrest x, ZNet.rest, split]
    simp only [pick, if_pos hTn, c1 m hnm.symm, lt_self_iff_false, if_false]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by simp [pick, c1 k (hKn k hk).1]
  have Em : ∀ x, Maximum N (-x) = net.d n * relu (net.negIn.Gp n x) +
      net.d m * net.negIn.Gp m x + ∑ k in K, net.d k * relu (net.negIn.Gp k x) := by
    intro x
    rw [hrest' (-x), ZNet.rest, split, neg_neg]
    have hd : net.negIn.d = net.d := rfl
    rw [hd]
    simp only [pick, if_pos hTm, c2 n hnm, lt_self_iff_false, if_false]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by simp [pick, c2 k (hKn k hk).2]
  choose b hb using fun k => Gp_sub_negIn_same net k
  let Φ : Point N →ₗ[ℝ] (K → ℝ) :=
    { toFun := fun x k => lin (b k) x
      map_add' := fun x y => funext fun k => lin_add_right _ _ _
      map_smul' := fun a x => funext fun k => by
        simp only [lin_smul_right, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }
  let L := net.d n • b n + net.d m • b m
  have hbound : ∀ x ∈ LinearMap.ker Φ,
      Maximum N x - Maximum N (-x) ≤ lin L x := by
    intro x hx
    have hzero : ∀ k ∈ K, lin (b k) x = 0 := fun k hk =>
      congr_fun (LinearMap.mem_ker.1 hx) ⟨k,hk⟩
    have heq : ∀ k ∈ K, net.Gp k x = net.negIn.Gp k x := by
      intro k hk
      have he := hb k x
      rw [hzero k hk] at he
      exact sub_eq_zero.1 he
    have hsum : ∑ k in K, net.d k * relu (net.Gp k x) =
        ∑ k in K, net.d k * relu (net.negIn.Gp k x) :=
      Finset.sum_congr rfl fun k hk => by rw [heq k hk]
    have hp := Ep x
    have hm' := Em x
    rw [hsum] at hp
    have hnrelu := relu_sub_relu_neg (net.negIn.Gp n x)
    have hmrelu := relu_sub_relu_neg (net.Gp m x)
    have hid : Maximum N x - Maximum N (-x) = lin L x -
        net.d n * relu (-net.negIn.Gp n x) + net.d m * relu (-net.Gp m x) := by
      dsimp [L]
      rw [lin_add_left, lin_smul_left, lin_smul_left]
      linear_combination hp - hm' + net.d n * hb n x + net.d m * hb m x -
        net.d n * hnrelu + net.d m * hmrelu
    rw [hid]
    have hnpos := mul_nonneg hdn.le (relu_nonneg (-net.negIn.Gp n x))
    have hmneg := mul_nonpos_of_nonpos_of_nonneg hdm.le (relu_nonneg (-net.Gp m x))
    linarith
  have hodd : ∀ x ∈ LinearMap.ker Φ,
      Maximum N x - Maximum N (-x) = lin L x := by
    intro x hx
    have hp := hbound x hx
    have hm' := hbound (-x) ((LinearMap.ker Φ).neg_mem hx)
    rw [neg_neg, lin_neg_right] at hm'
    linarith
  have hL : ∀ x ∈ LinearMap.ker Φ, Finset.univ.sup' Finset.univ_nonempty x +
      Finset.univ.inf' Finset.univ_nonempty x = linMap L x := by
    intro x hx
    have he := hodd x hx
    rw [Maximum_neg] at he
    change _ = lin L x
    change Maximum N x + _ = _
    linarith
  have hd := finrank_le_of_maxmin_univ (LinearMap.ker Φ) (linMap L) hL
  rw [Fintype.card_fin] at hd
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank ℝ (LinearMap.range Φ) ≤ K.card := by
    have he := Submodule.finrank_le (LinearMap.range Φ)
    rwa [finrank_fintype_fun_eq_card, Fintype.card_coe] at he
  rw [finrank_fin_fun] at hr
  have hdiv := Nat.mul_div_le N 2
  linarith

/-- The unrestricted theorem in the actual network model, with arbitrary biases. -/
theorem network_second_width_half_plus_one [NeZero N] (net : Network N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N + 2 ≤ 2 * h₂ :=
  second_width_half_plus_one net.toZ (net.toZ_eval_of_max h)

#print axioms second_width_half_plus_one
#print axioms network_second_width_half_plus_one

end MaxCaterpillar.Frontier.OvernightGeneral
