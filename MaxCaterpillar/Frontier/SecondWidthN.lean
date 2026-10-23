import MaxCaterpillar.Frontier.SecondWidth
import MaxCaterpillar.Frontier.MaxMinSubspace

/-! # A linear lower bound on the second width: `2 h₂ ≥ N`

Let a bias-free network compute `max_N`. By `ZNet.max_plus`,
`max = Σₖ dₖ pick(T⁺ₖ, Gₖ, σ(Gₖ))`, where every `Gₖ` has a linear odd part
`Gₖ(x) - Gₖ(-x) = cₖ·x`. Let `Z` be the neurons with `T⁺ₖ = 0` and `V = {x : cₖ·x = 0, k ∈ Z}`,
so `dim V ≥ N - |Z|`. For `x ∈ V` every neuron in `Z` takes the same value at `x` and `-x`, hence
`max x + min x = max x - max(-x)` is a linear function of `x ∈ V`. By `finrank_le_of_maxmin_univ`,
`dim V ≤ ⌊N/2⌋ + 1`, so `|Z| ≥ ⌈N/2⌉ - 1`. One more neuron has `T⁺ > 0`. Hence `h₂ ≥ ⌈N/2⌉`.
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators FiniteDimensional

variable {N h₁ h₂ : ℕ}

/-- `x ↦ c·x` as a linear map. -/
def linMap (c : Point N) : Point N →ₗ[ℝ] ℝ where
  toFun := lin c
  map_add' := lin_add_right c
  map_smul' a x := by
    show lin c (a • x) = a • lin c x
    rw [lin_smul_right, smul_eq_mul]

lemma Maximum_neg [NeZero N] (x : Point N) :
    Maximum N (-x) = -(Finset.univ.inf' Finset.univ_nonempty x) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin N)) x
  rw [hi]
  refine Maximum_eq_of _ _ i (by simp) fun k => ?_
  simp only [Pi.neg_apply, neg_le_neg_iff]
  rw [← hi]
  exact Finset.inf'_le x (Finset.mem_univ k)

/-- **Theorem H (second width, every `N`).** A bias-free network computing `max_N` has at least
`⌈N/2⌉` neurons in its second hidden layer. -/
theorem ZNet.second_width_half [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N ≤ 2 * h₂ := by
  classical
  choose c hc using fun k => net.oddLin_Gp k
  let Z := Finset.univ.filter fun k => net.Tp k = 0
  let Φ : Point N →ₗ[ℝ] (Z → ℝ) :=
    { toFun := fun x k => lin (c k) x
      map_add' := fun x y => funext fun k => lin_add_right _ _ _
      map_smul' := fun a x => funext fun k => by
        simp only [lin_smul_right, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }
  have hmemV : ∀ x ∈ LinearMap.ker Φ, ∀ k, net.Tp k = 0 → lin (c k) x = 0 := by
    intro x hx k hk
    have := congr_fun (LinearMap.mem_ker.1 hx) ⟨k, by simp [Z, hk]⟩
    exact this
  -- the odd part of the maximum is linear on `ker Φ`
  let L := linMap (∑ k, (if 0 < net.Tp k then net.d k else 0) • c k)
  have hL : ∀ x ∈ LinearMap.ker Φ, Finset.univ.sup' Finset.univ_nonempty x +
      Finset.univ.inf' Finset.univ_nonempty x = L x := by
    intro x hx
    have hrest := (net.max_plus h).2
    have hM : Maximum N x = Finset.univ.sup' Finset.univ_nonempty x := rfl
    have hodd : Maximum N x - Maximum N (-x) = L x := by
      rw [hrest x, hrest (-x), ZNet.rest, ZNet.rest, ← Finset.sum_sub_distrib]
      show _ = lin _ x
      rw [lin_sum_left]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lin_smul_left, ← hc k x]
      unfold pick
      rcases lt_trichotomy (net.Tp k) 0 with hT | hT | hT
      · simp only [if_neg (not_lt.2 hT.le), if_pos hT]
        ring
      · have hG : net.Gp k x = net.Gp k (-x) := by
          have := hc k x
          rw [hmemV x hx k hT] at this
          linarith
        simp only [hT, lt_irrefl, if_false]
        rw [hG]
        ring
      · simp only [if_pos hT]
        ring
    rw [Maximum_neg, hM] at hodd
    linarith
  -- dimension count
  have hdim := finrank_le_of_maxmin_univ (LinearMap.ker Φ) L hL
  rw [Fintype.card_fin] at hdim
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank ℝ (LinearMap.range Φ) ≤ Z.card := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  rw [finrank_fin_fun] at hrn
  -- one neuron with `T⁺ > 0`
  obtain ⟨hsl, _⟩ := net.max_plus h
  obtain ⟨n, hTn, _⟩ := exists_pos_term net.d net.Tp (by
    unfold ZNet.slope at hsl; rw [hsl]; norm_num)
  have hnZ : n ∉ Z := by simp [Z, hTn.ne']
  have hZ : Z.card + 1 ≤ h₂ := by
    have h1 := Finset.card_le_univ (insert n Z)
    rw [Finset.card_insert_of_not_mem hnZ, Fintype.card_fin] at h1
    exact h1
  have hdiv := Nat.mul_div_le N 2
  linarith

end Frontier
end MaxCaterpillar
