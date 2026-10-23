import MaxCaterpillar.Frontier.Asymptotics

/-! # Theorem 1: the second hidden layer needs at least three neurons (`N ≥ 3`)

With at most two second-hidden-layer neurons, the identities `(+∞)` and `(-∞)` of
`ZNet.max_plus` / `ZNet.max_minus` force one neuron `n` with `T⁺ > 0`, `T⁻ = 0`, `d > 0` and
one neuron `m` with `T⁻ > 0`, `T⁺ = 0`, `d < 0`. Subtracting the two identities gives a
nonnegative function equal to a linear form, hence zero; then `(+∞)` writes the maximum as a
function whose odd part is linear, contradicting `not_oddLin_max`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

lemma OddLin.comp_neg {f : Point N → ℝ} (hf : OddLin f) : OddLin (fun x => f (-x)) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨-c, fun x => ?_⟩
  have := hc x
  show f (-x) - f (- -x) = _
  rw [neg_neg, lin_neg_left]; linarith

lemma ZNet.oddLin_Gp (net : ZNet N h₁ h₂) (k : Fin h₂) : OddLin (net.Gp k) := by
  refine OddLin.sum _ fun j _ => ?_
  rcases lt_trichotomy (net.s j) 0 with h | h | h
  · have : ∀ x : Point N, (0 : ℝ) = net.W k j * pick (net.s j) (lin (net.A j) x)
        (relu (lin (net.A j) x)) := fun x => by
      simp [pick, h, not_lt.2 h.le]
    exact oddLin_zero.congr this
  · simp only [pick, h, lt_irrefl, if_false]
    exact (oddLin_relu_lin _).const_mul _
  · simp only [pick, if_pos h]
    exact (oddLin_lin _).const_mul _

lemma ZNet.Gp_sub_negIn (net : ZNet N h₁ h₂) (k : Fin h₂) :
    ∃ c : Point N, ∀ x, net.Gp k x - net.negIn.Gp k (-x) = lin c x := by
  refine ⟨∑ j, (net.W k j * (if 0 < net.s j then 1 else if net.s j < 0 then -1 else 0)) •
    net.A j, fun x => ?_⟩
  rw [lin_sum_left]
  simp only [ZNet.Gp, ← Finset.sum_sub_distrib, ZNet.negIn_s]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ZNet.negIn, lin_neg_left, lin_neg_right, neg_neg, lin_smul_left, pick]
  rcases lt_trichotomy (net.s j) 0 with h | h | h
  · simp [h, not_lt.2 h.le]
  · simp [h]
  · simp [h, not_lt.2 h.le]

lemma exists_pos_term {ι : Type*} [Fintype ι] (d T : ι → ℝ)
    (h : 0 < ∑ k, d k * pick (T k) (T k) 0) : ∃ k, 0 < T k ∧ 0 < d k := by
  by_contra hc
  push_neg at hc
  have : ∑ k, d k * pick (T k) (T k) 0 ≤ 0 := Finset.sum_nonpos fun k _ => by
    unfold pick
    split_ifs with h1
    · exact mul_nonpos_of_nonpos_of_nonneg (hc k h1) h1.le
    · simp
    · simp
  linarith

lemma exists_neg_term {ι : Type*} [Fintype ι] (d T : ι → ℝ)
    (h : ∑ k, d k * pick (T k) (T k) 0 < 0) : ∃ k, 0 < T k ∧ d k < 0 := by
  obtain ⟨k, h1, h2⟩ := exists_pos_term (fun k => -d k) T (by
    simp only [neg_mul, Finset.sum_neg_distrib]; linarith)
  exact ⟨k, h1, by linarith⟩

lemma oddLin_pick_of_ne {f : Point N → ℝ} (hf : OddLin f) (a T : ℝ) (hT : T ≠ 0) :
    OddLin (fun x => a * pick T (f x) (relu (f x))) := by
  rcases lt_or_gt_of_ne hT with h | h
  · have : ∀ x : Point N, (0 : ℝ) = a * pick T (f x) (relu (f x)) := fun x => by
      simp [pick, h, not_lt.2 h.le]
    exact oddLin_zero.congr this
  · simp only [pick, if_pos h]
    exact hf.const_mul a

/-- **Theorem 1.** For `N ≥ 3`, no bias-free network with at most two second-layer neurons
computes the maximum. -/
theorem ZNet.second_width_ge_three [NeZero N] (hN : 3 ≤ N) (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : 3 ≤ h₂ := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hsl, hrest⟩ := net.max_plus h
  obtain ⟨hsl', hrest'⟩ := net.max_minus h
  obtain ⟨n, hTn, hdn⟩ := exists_pos_term net.d net.Tp (by
    unfold ZNet.slope at hsl; rw [hsl]; norm_num)
  obtain ⟨m, hTm', hdm⟩ := exists_neg_term net.d net.negIn.Tp (by
    unfold ZNet.slope at hsl'; simp only [ZNet.negIn] at hsl' ⊢; rw [hsl']; norm_num)
  have hnm : n ≠ m := fun e => by rw [e] at hdn; linarith
  have huniv : (Finset.univ : Finset (Fin h₂)) = {n, m} := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have h0 : n.val ≠ m.val := fun e => hnm (Fin.ext e)
    have := k.isLt; have := n.isLt; have := m.isLt
    by_contra hk
    push_neg at hk
    have h1 : k.val ≠ n.val := fun e => hk.1 (Fin.ext e)
    have h2 : k.val ≠ m.val := fun e => hk.2 (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne h0 with a | a <;> rcases Nat.lt_or_gt_of_ne h1 with b | b <;>
      rcases Nat.lt_or_gt_of_ne h2 with c | c <;> omega
  -- the two identities as sums over `{n, m}`
  have Ep : ∀ x, Maximum N x = net.d n * net.Gp n x +
      net.d m * pick (net.Tp m) (net.Gp m x) (relu (net.Gp m x)) := by
    intro x
    rw [hrest x, ZNet.rest, huniv, Finset.sum_pair hnm]
    simp only [pick, if_pos hTn]
  have hdneg : net.negIn.d = net.d := rfl
  have Em : ∀ x, Maximum N x =
      net.d n * pick (net.negIn.Tp n) (net.negIn.Gp n (-x)) (relu (net.negIn.Gp n (-x))) +
      net.d m * net.negIn.Gp m (-x) := by
    intro x
    rw [hrest' x, ZNet.rest, huniv, Finset.sum_pair hnm, hdneg]
    simp only [pick, if_pos hTm']
  -- `T⁺ₘ = 0`
  have hTm0 : net.Tp m = 0 := by
    by_contra hne
    refine not_oddLin_max hN (OddLin.congr (((net.oddLin_Gp n).const_mul (net.d n)).add
      (oddLin_pick_of_ne (net.oddLin_Gp m) (net.d m) _ hne)) fun x => (Ep x).symm)
  -- `T⁻ₙ = 0`
  have hTn0 : net.negIn.Tp n = 0 := by
    by_contra hne
    refine not_oddLin_max hN (OddLin.congr
      ((oddLin_pick_of_ne (net.negIn.oddLin_Gp n).comp_neg (net.d n) _ hne).add
        ((net.negIn.oddLin_Gp m).comp_neg.const_mul (net.d m))) fun x => (Em x).symm)
  have Ep' : ∀ x, Maximum N x = net.d n * net.Gp n x + net.d m * relu (net.Gp m x) := by
    intro x; rw [Ep x, hTm0]; simp [pick]
  have Em' : ∀ x, Maximum N x =
      net.d n * relu (net.negIn.Gp n (-x)) + net.d m * net.negIn.Gp m (-x) := by
    intro x; rw [Em x, hTn0]; simp [pick]
  obtain ⟨cn, hcn⟩ := net.Gp_sub_negIn n
  obtain ⟨cm, hcm⟩ := net.Gp_sub_negIn m
  -- a nonnegative function equal to a linear form
  have hL : ∀ x, net.d n * relu (-net.negIn.Gp n (-x)) - net.d m * relu (-net.Gp m x) =
      lin (net.d n • cn + net.d m • cm) x := by
    intro x
    have r1 := relu_sub_relu_neg (net.negIn.Gp n (-x))
    have r2 := relu_sub_relu_neg (net.Gp m x)
    have Ln := hcn x
    have Lm := hcm x
    have A := Ep' x
    have B := Em' x
    rw [lin_add_left, lin_smul_left, lin_smul_left]
    linear_combination (-net.d n) * r1 + net.d m * r2 + net.d n * Ln + net.d m * Lm + A - B
  have hpos : ∀ x, 0 ≤ net.d n * relu (-net.negIn.Gp n (-x)) - net.d m * relu (-net.Gp m x) :=
    fun x => by
      have := mul_nonneg hdn.le (relu_nonneg (-net.negIn.Gp n (-x)))
      have := mul_nonneg (neg_nonneg.2 hdm.le) (relu_nonneg (-net.Gp m x))
      linarith
  have hzero : ∀ x, relu (-net.Gp m x) = 0 := by
    intro x
    have e1 := hL x
    have e2 := hL (-x)
    rw [lin_neg_right] at e2
    have h2 := hpos (-x)
    have a1 := mul_nonneg hdn.le (relu_nonneg (-net.negIn.Gp n (-x)))
    have a2 : 0 ≤ -net.d m * relu (-net.Gp m x) :=
      mul_nonneg (neg_nonneg.2 hdm.le) (relu_nonneg _)
    have a3 : -net.d m * relu (-net.Gp m x) = 0 := by linarith
    rcases mul_eq_zero.1 a3 with h | h
    · linarith
    · exact h
  have Efinal : ∀ x, net.d n * net.Gp n x + net.d m * net.Gp m x = Maximum N x := by
    intro x
    have := relu_sub_relu_neg (net.Gp m x)
    rw [hzero x, sub_zero] at this
    rw [Ep' x, this]
  exact not_oddLin_max hN (OddLin.congr (((net.oddLin_Gp n).const_mul (net.d n)).add
    ((net.oddLin_Gp m).const_mul (net.d m))) Efinal)

end Frontier
end MaxCaterpillar
