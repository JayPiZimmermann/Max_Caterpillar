import MaxCaterpillar.Frontier.SecondWidthN
import MaxCaterpillar.Frontier.FirstWidthN
import MaxCaterpillar.Frontier.FirstWidth

/-! # Free neurons, and `h₂ ≥ ⌈N/2⌉ + 1` near the minimal first width

* `free_bound`: if `max x - max(-x) = c·x + Σ_{k∈K} dₖ (σ(Gₖ x) - σ(Gₖ(-x)))` with every `Gₖ` of
  linear odd part (for instance a one-hidden-layer function), then `N ≤ 2|K| + 2`. In particular
  `max_N = (one-hidden-layer function) + Σ_{k∈K} dₖ σ(Gₖ)` with one-hidden-layer `Gₖ` needs
  `|K| ≥ ⌈N/2⌉ - 1` free neurons, whatever the first layer (`free_neurons`).
* `ZNet.second_width_half_succ`: if exactly one first-layer row has positive and exactly one has
  negative coordinate sum, then `N + 2 ≤ 2h₂` (`h₂ ≥ ⌈N/2⌉ + 1`). Either the asymptotic
  identities at `±∞` leave two neurons outside the free set, or (as in Theorem 1) subtracting
  them turns one free neuron into a linear term, leaving `h₂ - 2` free neurons.
* `ZNet.second_width_joint`: `6h₁ + 11N < 3N² + 18` forces that shape (Theorem Q's covering
  count), hence `N + 2 ≤ 2h₂`: a joint bound, larger second width when the first width is
  near its lower bound.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators FiniteDimensional

variable {N h₁ h₂ : ℕ}

/-- **Free-neuron bound.** -/
theorem free_bound [NeZero N] {κ : Type*} (K : Finset κ) (G : κ → Point N → ℝ)
    (hG : ∀ k, OddLin (G k)) (c₀ : Point N) (d : κ → ℝ)
    (h : ∀ x, Maximum N x - Maximum N (-x) =
      lin c₀ x + ∑ k in K, d k * (relu (G k x) - relu (G k (-x)))) :
    N ≤ 2 * K.card + 2 := by
  classical
  choose c hc using hG
  let Φ : Point N →ₗ[ℝ] (K → ℝ) :=
    { toFun := fun x k => lin (c k) x
      map_add' := fun x y => funext fun k => lin_add_right _ _ _
      map_smul' := fun a x => funext fun k => by
        simp only [lin_smul_right, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }
  have hL : ∀ x ∈ LinearMap.ker Φ, Finset.univ.sup' Finset.univ_nonempty x +
      Finset.univ.inf' Finset.univ_nonempty x = linMap c₀ x := by
    intro x hx
    have hz : ∀ k ∈ K, G k x = G k (-x) := fun k hk => by
      have h1 := hc k x
      have h2 : lin (c k) x = 0 := congr_fun (LinearMap.mem_ker.1 hx) ⟨k, hk⟩
      linarith
    have hs : ∑ k in K, d k * (relu (G k x) - relu (G k (-x))) = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hz k hk, sub_self, mul_zero]
    have e := h x
    rw [hs, add_zero] at e
    have hM : Maximum N x = Finset.univ.sup' Finset.univ_nonempty x := rfl
    rw [Maximum_neg, hM] at e
    show _ = lin c₀ x
    linarith
  have hdim := finrank_le_of_maxmin_univ (LinearMap.ker Φ) (linMap c₀) hL
  rw [Fintype.card_fin] at hdim
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank ℝ (LinearMap.range Φ) ≤ K.card := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  rw [finrank_fin_fun] at hrn
  have hdiv := Nat.mul_div_le N 2
  linarith

/-- **Free neurons (skip connections allowed).** If
`max_N x = c·x + Σⱼ aⱼ σ(Bⱼ·x) + Σ_{k<K} dₖ σ(cₖ·x + Σⱼ Wₖⱼ σ(Bⱼ·x))` on `ℝ^N`, then
`N ≤ 2K + 2`, i.e. at least `⌈N/2⌉ - 1` second-layer neurons. -/
theorem free_neurons [NeZero N] (m K : ℕ) (c : Point N) (a : Fin m → ℝ) (B : Fin m → Point N)
    (d : Fin K → ℝ) (C : Fin K → Point N) (W : Fin K → Fin m → ℝ)
    (h : ∀ x, Maximum N x = lin c x + ∑ j, a j * relu (lin (B j) x) +
      ∑ k, d k * relu (lin (C k) x + ∑ j, W k j * relu (lin (B j) x))) :
    N ≤ 2 * K + 2 := by
  have hodd : ∀ k, OddLin (fun x => lin (C k) x + ∑ j, W k j * relu (lin (B j) x)) := fun k =>
    (oddLin_lin _).add (OddLin.sum _ fun j _ => (oddLin_relu_lin _).const_mul _)
  have hL : OddLin (fun x => lin c x + ∑ j, a j * relu (lin (B j) x)) :=
    (oddLin_lin _).add (OddLin.sum _ fun j _ => (oddLin_relu_lin _).const_mul _)
  obtain ⟨c₀, hc₀⟩ := hL
  have key := free_bound Finset.univ (fun k x => lin (C k) x + ∑ j, W k j * relu (lin (B j) x))
    hodd c₀ d fun x => by
      have e : (lin c x + ∑ j, a j * relu (lin (B j) x)) -
          (lin c (-x) + ∑ j, a j * relu (lin (B j) (-x))) = lin c₀ x := hc₀ x
      have hs : ∑ k, d k * (relu (lin (C k) x + ∑ j, W k j * relu (lin (B j) x)) -
          relu (lin (C k) (-x) + ∑ j, W k j * relu (lin (B j) (-x)))) =
          ∑ k, d k * relu (lin (C k) x + ∑ j, W k j * relu (lin (B j) x)) -
          ∑ k, d k * relu (lin (C k) (-x) + ∑ j, W k j * relu (lin (B j) (-x))) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      show _ = lin c₀ x + ∑ k, d k * (relu (lin (C k) x + ∑ j, W k j * relu (lin (B j) x)) -
          relu (lin (C k) (-x) + ∑ j, W k j * relu (lin (B j) (-x))))
      rw [h x, h (-x), hs]
      linarith
  simpa using key

/-! ## The network case -/

lemma ZNet.rest_odd (net : ZNet N h₁ h₂) : ∃ c₀ : Point N, ∀ x,
    net.rest x - net.rest (-x) = lin c₀ x + ∑ k in Finset.univ.filter (fun k => net.Tp k = 0),
      net.d k * (relu (net.Gp k x) - relu (net.Gp k (-x))) := by
  classical
  choose c hc using fun k => net.oddLin_Gp k
  refine ⟨∑ k, (if 0 < net.Tp k then net.d k else 0) • c k, fun x => ?_⟩
  rw [ZNet.rest, ZNet.rest, ← Finset.sum_sub_distrib, lin_sum_left, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lin_smul_left, ← hc k x]
  unfold pick
  rcases lt_trichotomy (net.Tp k) 0 with hT | hT | hT
  · simp only [if_neg (not_lt.2 hT.le), if_pos hT, if_neg hT.ne]; ring
  · simp only [hT, lt_irrefl, if_false, if_true, eq_self_iff_true]; ring
  · simp only [if_pos hT, if_neg hT.ne']; ring

/-- Theorem H in counting form: at least `⌈N/2⌉ - 1` neurons with `T⁺ = 0`. -/
theorem ZNet.card_Zp [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    N ≤ 2 * (Finset.univ.filter fun k => net.Tp k = 0).card + 2 := by
  obtain ⟨c₀, hc₀⟩ := net.rest_odd
  have hr := (net.max_plus h).2
  exact free_bound _ (fun k => net.Gp k) (fun k => net.oddLin_Gp k) c₀ net.d fun x => by
    rw [hr x, hr (-x)]; exact hc₀ x

/-- The same at `-∞`: at least `⌈N/2⌉ - 1` neurons with `T⁻ = 0`. -/
theorem ZNet.card_Zm [NeZero N] (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) :
    N ≤ 2 * (Finset.univ.filter fun k => net.negIn.Tp k = 0).card + 2 := by
  obtain ⟨c₀, hc₀⟩ := net.negIn.rest_odd
  have hr := (net.max_minus h).2
  refine free_bound _ (fun k x => net.negIn.Gp k (-x)) (fun k => (net.negIn.oddLin_Gp k).comp_neg)
    (-c₀) (fun k => net.negIn.d k) fun x => ?_
  rw [hr x, hr (-x), neg_neg]
  have e := hc₀ x
  have e2 : net.negIn.rest (-x) - net.negIn.rest x = -(net.negIn.rest x - net.negIn.rest (-x)) :=
    by ring
  rw [e2, e, lin_neg_left, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [neg_neg]
  ring

lemma ZNet.oddLin_rhoSum (net : ZNet N h₁ h₂) (k : Fin h₂) :
    OddLin (fun x => ∑ j, net.W k j * net.rho x j) := by
  refine OddLin.sum _ fun j _ => ?_
  by_cases hj : net.s j = 0
  · exact ((oddLin_relu_lin (net.A j)).const_mul (net.W k j)).congr fun x => by
      simp [ZNet.rho, hj]
  · exact (oddLin_zero (N := N)).congr fun x => by simp [ZNet.rho, hj]

/-- **Theorem H⁺.** If exactly one first-layer row has positive coordinate sum and exactly one
has negative coordinate sum, then `N + 2 ≤ 2h₂`. -/
theorem ZNet.second_width_half_succ [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x)
    (hp1 : (Finset.univ.filter fun j => 0 < net.s j).card = 1)
    (hq1 : (Finset.univ.filter fun j => net.s j < 0).card = 1) : N + 2 ≤ 2 * h₂ := by
  classical
  obtain ⟨p, hpset⟩ := Finset.card_eq_one.1 hp1
  have hsp : 0 < net.s p := by
    have : p ∈ Finset.univ.filter fun j => 0 < net.s j := by rw [hpset]; simp
    simpa using this
  have hp : ∀ j, 0 < net.s j → j = p := fun j hj => by
    have : j ∈ Finset.univ.filter fun j => 0 < net.s j := by simp [hj]
    rw [hpset] at this; simpa using this
  obtain ⟨q, hqset⟩ := Finset.card_eq_one.1 hq1
  have hsq : net.s q < 0 := by
    have : q ∈ Finset.univ.filter fun j => net.s j < 0 := by rw [hqset]; simp
    simpa using this
  have hq : ∀ j, net.s j < 0 → j = q := fun j hj => by
    have : j ∈ Finset.univ.filter fun j => net.s j < 0 := by simp [hj]
    rw [hqset] at this; simpa using this
  -- slopes
  have hTp : ∀ k, net.Tp k = net.W k p * net.s p := by
    intro k
    rw [ZNet.Tp, Finset.sum_eq_single p (fun j _ hj => by
      have hj' : ¬ 0 < net.s j := fun h' => hj (hp j h')
      simp [pick, hj']) (by simp)]
    simp [pick, hsp]
  have hTm : ∀ k, net.negIn.Tp k = net.W k q * (-net.s q) := by
    intro k
    rw [ZNet.Tp, Finset.sum_eq_single q (fun j _ hj => by
      have hj' : ¬ 0 < net.negIn.s j := fun h' => by
        rw [net.negIn_s] at h'; exact hj (hq j (by linarith))
      simp [pick, hj']) (by simp)]
    rw [net.negIn_s]
    simp only [pick, if_pos (neg_pos.2 hsq)]
    rfl
  -- the second-layer inputs at `±∞`
  let A : Fin h₂ → Point N → ℝ := fun k x => ∑ j, net.W k j * net.rho x j
  have hGp : ∀ k x, net.Gp k x = net.W k p * lin (net.A p) x + A k x := by
    intro k x
    have : ∀ j, net.W k j * pick (net.s j) (lin (net.A j) x) (relu (lin (net.A j) x)) =
        (if p = j then net.W k p * lin (net.A p) x else 0) + net.W k j * net.rho x j := by
      intro j
      by_cases hj : p = j
      · subst hj; simp [pick, ZNet.rho, hsp, hsp.ne']
      · have hj' : ¬ 0 < net.s j := fun h' => hj (hp j h').symm
        rw [if_neg hj]
        unfold pick ZNet.rho
        rw [if_neg hj']
        by_cases hs : net.s j < 0
        · rw [if_pos hs, if_neg (ne_of_lt hs)]; ring
        · have : net.s j = 0 := le_antisymm (not_lt.1 hj') (not_lt.1 hs)
          rw [if_neg hs, if_pos this]; ring
    rw [ZNet.Gp, Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
      Finset.sum_ite_eq]
    simp
  have hGm : ∀ k x, net.negIn.Gp k (-x) = net.W k q * lin (net.A q) x + A k x := by
    intro k x
    have : ∀ j, net.negIn.W k j * pick (net.negIn.s j) (lin (net.negIn.A j) (-x))
        (relu (lin (net.negIn.A j) (-x))) =
        (if q = j then net.W k q * lin (net.A q) x else 0) + net.W k j * net.rho x j := by
      intro j
      have hl : lin (net.negIn.A j) (-x) = lin (net.A j) x := by
        simp [ZNet.negIn, lin_neg_left, lin_neg_right]
      have hW : net.negIn.W k j = net.W k j := rfl
      rw [hl, hW, net.negIn_s]
      by_cases hj : q = j
      · subst hj
        unfold pick ZNet.rho
        rw [if_pos (neg_pos.2 hsq), if_neg hsq.ne, if_pos rfl]
        ring
      · have hj' : ¬ net.s j < 0 := fun h' => hj (hq j h').symm
        rw [if_neg hj]
        unfold pick ZNet.rho
        rw [if_neg (by intro h'; exact hj' (by linarith))]
        by_cases hs : 0 < net.s j
        · rw [if_pos (by linarith : -net.s j < 0), if_neg (ne_of_gt hs)]; ring
        · have : net.s j = 0 := le_antisymm (not_lt.1 hs) (not_lt.1 hj')
          rw [if_neg (by rw [this]; norm_num), if_pos this]; ring
    rw [ZNet.Gp, Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
      Finset.sum_ite_eq]
    simp
  -- counting
  set Zp := Finset.univ.filter fun k => net.Tp k = 0 with hZp
  set Zm := Finset.univ.filter fun k => net.negIn.Tp k = 0 with hZm
  have b1 := net.card_Zp h
  have b2 := net.card_Zm h
  obtain ⟨hsl, hrest⟩ := net.max_plus h
  obtain ⟨hsl', hrest'⟩ := net.max_minus h
  obtain ⟨n, hTn, hdn⟩ := exists_pos_term net.d net.Tp (by
    unfold ZNet.slope at hsl; rw [hsl]; norm_num)
  obtain ⟨m, hTm', hdm⟩ := exists_neg_term net.d net.negIn.Tp (by
    unfold ZNet.slope at hsl'; simp only [ZNet.negIn] at hsl' ⊢; rw [hsl']; norm_num)
  have hnm : n ≠ m := fun e => by rw [e] at hdn; linarith
  have two : ∀ (Z : Finset (Fin h₂)) (a b : Fin h₂), a ∉ Z → b ∉ Z → a ≠ b →
      Z.card + 2 ≤ h₂ := by
    intro Z a b ha hb hab
    have h1 := Finset.card_le_univ (insert a (insert b Z))
    rw [Finset.card_insert_of_not_mem (by simp [hab, ha]), Finset.card_insert_of_not_mem hb,
      Fintype.card_fin] at h1
    exact h1
  by_cases c1 : ∃ k, k ≠ n ∧ net.Tp k ≠ 0
  · obtain ⟨k, hkn, hk⟩ := c1
    have := two Zp n k (by simp [hZp, hTn.ne']) (by simp [hZp, hk]) (Ne.symm hkn)
    linarith
  by_cases c2 : ∃ k, k ≠ m ∧ net.negIn.Tp k ≠ 0
  · obtain ⟨k, hkm, hk⟩ := c2
    have := two Zm m k (by simp [hZm, hTm'.ne']) (by simp [hZm, hk]) (Ne.symm hkm)
    linarith
  push_neg at c1 c2
  have hWp : ∀ k, k ≠ n → net.W k p = 0 := fun k hk => by
    have := c1 k hk; rw [hTp] at this
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' hsp.ne'
  have hWq : ∀ k, k ≠ m → net.W k q = 0 := fun k hk => by
    have := c2 k hk; rw [hTm] at this
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' (by linarith)
  have hTn' : net.Tp m = 0 := c1 m (Ne.symm hnm)
  have hTnm : net.negIn.Tp n = 0 := c2 n hnm
  -- the two identities, split into `n`, `m` and the rest
  set K := (Finset.univ.erase n).erase m with hK
  have hmK : m ∈ Finset.univ.erase n := Finset.mem_erase.2 ⟨Ne.symm hnm, Finset.mem_univ m⟩
  have split : ∀ f : Fin h₂ → ℝ, ∑ k, f k = f n + f m + ∑ k in K, f k := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n), ← Finset.add_sum_erase _ _ hmK]
    ring
  have hKn : ∀ k ∈ K, k ≠ n ∧ k ≠ m := fun k hk => by
    rw [hK, Finset.mem_erase, Finset.mem_erase] at hk; exact ⟨hk.2.1, hk.1⟩
  have Ep : ∀ x, Maximum N x = net.d n * (net.W n p * lin (net.A p) x + A n x) +
      net.d m * relu (A m x) + ∑ k in K, net.d k * relu (A k x) := by
    intro x
    rw [hrest x, ZNet.rest, split]
    have e1 : pick (net.Tp n) (net.Gp n x) (relu (net.Gp n x)) =
        net.W n p * lin (net.A p) x + A n x := by
      rw [hGp]; simp [pick, hTn]
    have e2 : pick (net.Tp m) (net.Gp m x) (relu (net.Gp m x)) = relu (A m x) := by
      rw [hGp, hWp m (Ne.symm hnm), hTn']; simp [pick]
    rw [e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hGp, hWp k (hKn k hk).1, c1 k (hKn k hk).1]; simp [pick]
  have Em : ∀ x, Maximum N x = net.d n * relu (A n x) +
      net.d m * (net.W m q * lin (net.A q) x + A m x) + ∑ k in K, net.d k * relu (A k x) := by
    intro x
    rw [hrest' x, ZNet.rest, split]
    have hd : ∀ k, net.negIn.d k = net.d k := fun k => rfl
    simp only [hd]
    have e1 : pick (net.negIn.Tp n) (net.negIn.Gp n (-x)) (relu (net.negIn.Gp n (-x))) =
        relu (A n x) := by
      rw [hGm, hWq n hnm, hTnm]; simp [pick]
    have e2 : pick (net.negIn.Tp m) (net.negIn.Gp m (-x)) (relu (net.negIn.Gp m (-x))) =
        net.W m q * lin (net.A q) x + A m x := by
      rw [hGm]; simp [pick, hTm']
    rw [e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hGm, hWq k (hKn k hk).2, c2 k (hKn k hk).2]; simp [pick]
  -- subtracting: a nonnegative function equals a linear form
  have hL : ∀ x, net.d n * relu (-A n x) - net.d m * relu (-A m x) =
      lin (net.d n • (net.W n p • net.A p) + (-net.d m) • (net.W m q • net.A q)) x := by
    intro x
    have r1 := relu_sub_relu_neg (A n x)
    have r2 := relu_sub_relu_neg (A m x)
    have a1 := Ep x
    have a2 := Em x
    simp only [lin_add_left, lin_smul_left]
    linear_combination a1 - a2 - net.d n * r1 + net.d m * r2
  have hzero : ∀ x, relu (-A m x) = 0 := by
    intro x
    have e1 := hL x
    have e2 := hL (-x)
    rw [lin_neg_right] at e2
    have a1 := mul_nonneg hdn.le (relu_nonneg (-A n x))
    have a2 : 0 ≤ -net.d m * relu (-A m x) := mul_nonneg (neg_nonneg.2 hdm.le) (relu_nonneg _)
    have a3 := mul_nonneg hdn.le (relu_nonneg (-A n (-x)))
    have a4 : 0 ≤ -net.d m * relu (-A m (-x)) := mul_nonneg (neg_nonneg.2 hdm.le) (relu_nonneg _)
    have a5 : -net.d m * relu (-A m x) = 0 := by linarith
    rcases mul_eq_zero.1 a5 with h' | h'
    · linarith
    · exact h'
  -- a representation with `|K|` free neurons
  obtain ⟨cn, hcn⟩ := net.oddLin_rhoSum n
  obtain ⟨cm, hcm⟩ := net.oddLin_rhoSum m
  have hfree := free_bound K A (fun k => net.oddLin_rhoSum k)
    (net.d n • ((2 : ℝ) • (net.W n p • net.A p) + cn) + net.d m • cm) net.d fun x => by
      have hm1 : relu (A m x) = A m x := by
        have := relu_sub_relu_neg (A m x); rw [hzero x, sub_zero] at this; exact this
      have hm2 : relu (A m (-x)) = A m (-x) := by
        have := relu_sub_relu_neg (A m (-x)); rw [hzero (-x), sub_zero] at this; exact this
      have en : A n x - A n (-x) = lin cn x := hcn x
      have em : A m x - A m (-x) = lin cm x := hcm x
      have hlp : lin (net.A p) (-x) = -lin (net.A p) x := lin_neg_right _ _
      have hsum : ∑ k in K, net.d k * (relu (A k x) - relu (A k (-x))) =
          ∑ k in K, net.d k * relu (A k x) - ∑ k in K, net.d k * relu (A k (-x)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [Ep x, Ep (-x), hsum, hlp]
      simp only [lin_add_left, lin_smul_left]
      linear_combination net.d n * en + net.d m * em + net.d m * hm1 - net.d m * hm2
  have hKc : K.card = h₂ - 2 := by
    rw [hK, Finset.card_erase_of_mem hmK, Finset.card_erase_of_mem (Finset.mem_univ n),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hh2 : 2 ≤ h₂ := by
    have h1 := Finset.card_le_univ ({n, m} : Finset (Fin h₂))
    rw [Finset.card_doubleton hnm, Fintype.card_fin] at h1
    exact h1
  have hK2 : K.card + 2 = h₂ := by rw [hKc]; exact Nat.sub_add_cancel hh2
  linarith

/-- The rows split into `s > 0`, `s < 0` and `s = 0`. -/
lemma ZNet.card_three (net : ZNet N h₁ h₂) :
    (Finset.univ.filter fun j => 0 < net.s j).card +
      (Finset.univ.filter fun j => net.s j < 0).card +
      (Finset.univ.filter fun j => net.s j = 0).card = h₁ := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  have : ∀ j, ((if 0 < net.s j then 1 else 0) + (if net.s j < 0 then 1 else 0) +
      (if net.s j = 0 then 1 else 0) : ℕ) = 1 := by
    intro j
    rcases lt_trichotomy (net.s j) 0 with h' | h' | h'
    · simp [h', not_lt.2 h'.le, h'.ne]
    · simp [h']
    · simp [h', not_lt.2 h'.le, h'.ne']
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- **Joint bound.** If `6h₁ + 11N < 3N² + 18` (first width within two of the lower bound of
Theorem Q), then `N + 2 ≤ 2h₂`. -/
theorem ZNet.second_width_joint [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) (hh : 6 * h₁ + 11 * N < 3 * N * N + 18) :
    N + 2 ≤ 2 * h₂ := by
  classical
  have hcov := cover_count (Finset.univ.filter fun j => net.s j = 0) net.supp
    fun I hI a haI => net.cover4 h I hI a haI
  have h3 := net.card_three
  obtain ⟨p, hp⟩ := net.exists_pos h
  obtain ⟨q, hq⟩ := net.exists_neg h
  have a1 : 1 ≤ (Finset.univ.filter fun j => 0 < net.s j).card :=
    Finset.card_pos.2 ⟨p, by simp [hp]⟩
  have a2 : 1 ≤ (Finset.univ.filter fun j => net.s j < 0).card :=
    Finset.card_pos.2 ⟨q, by simp [hq]⟩
  have e1 : (Finset.univ.filter fun j => 0 < net.s j).card = 1 := by
    by_contra hne
    have : 2 ≤ (Finset.univ.filter fun j => 0 < net.s j).card := by omega
    linarith
  have e2 : (Finset.univ.filter fun j => net.s j < 0).card = 1 := by
    by_contra hne
    have : 2 ≤ (Finset.univ.filter fun j => net.s j < 0).card := by omega
    linarith
  exact net.second_width_half_succ h e1 e2

end Frontier
end MaxCaterpillar
