import MaxCaterpillar.Frontier.SecondWidthPlus

/-! Scratch leaf for the new transverse positivity argument. No public imports. -/

namespace MaxCaterpillar.Frontier.OvernightGeneral

open Filter Topology BigOperators FiniteDimensional

lemma slope_zero_of_local_nonneg (c : ℝ)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * c) : c = 0 := by
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ (-t) * c := by
    have ht : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using continuous_neg.continuousAt.tendsto (x := (0 : ℝ))
    exact ht.eventually h
  have hr : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ t*c ∧ 0 ≤ (-t)*c :=
    (h.and hn).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 ≤ t*c ∧ 0 ≤ (-t)*c) ∧ 0 < t :=
    hr.and self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, hnt⟩, hp⟩ := hall.exists
  nlinarith

lemma slope_at_positive (w : ℝ → ℝ) (hw : ContinuousAt w 0)
    (h0 : 0 < w 0) (c s : ℝ)
    (h : ∀ t, 0 ≤ t * c + s * (relu (w t + t) - relu (w t))) : c = -s := by
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w t := hw.eventually (lt_mem_nhds h0)
  have hw' : ContinuousAt (fun t => w t + t) 0 := hw.add continuousAt_id
  have hp' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w t + t :=
    hw'.eventually (lt_mem_nhds (by simpa using h0))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t * (c + s) := by
    filter_upwards [hp, hp'] with t ht ht'
    have h1 := h t
    rw [relu_of_nonneg ht'.le, relu_of_nonneg ht.le] at h1
    nlinarith
  have hz := slope_zero_of_local_nonneg (c+s) he
  linarith

lemma slope_at_negative (w : ℝ → ℝ) (hw : ContinuousAt w 0)
    (h0 : w 0 < 0) (c s : ℝ)
    (h : ∀ t, 0 ≤ t * c + s * (relu (w t + t) - relu (w t))) : c = 0 := by
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), w t < 0 := hw.eventually (gt_mem_nhds h0)
  have hw' : ContinuousAt (fun t => w t + t) 0 := hw.add continuousAt_id
  have hp' : ∀ᶠ t in 𝓝 (0 : ℝ), w t + t < 0 :=
    hw'.eventually (gt_mem_nhds (by simpa using h0))
  apply slope_zero_of_local_nonneg c
  filter_upwards [hp, hp'] with t ht ht'
  have h1 := h t
  simpa only [relu_of_nonpos ht'.le, relu_of_nonpos ht.le, sub_self,
    mul_zero, add_zero] using h1

variable {N : ℕ}

/-- Global positivity across a hyperplane forces the preactivation to have a
uniform weak sign on that hyperplane. This is the new proof step. -/
theorem transverse_sign (w : Point N → ℝ) (hw : Continuous w)
    (L delta : Point N) (s : ℝ) (hs : s ≠ 0)
    (h : ∀ x, 0 ≤ lin L x + s * (relu (w x + lin delta x) - relu (w x)))
    (hker : ∀ x, lin delta x = 0 → lin L x = 0)
    (y : Point N) (hy : lin delta y = 1) :
    (∀ x, lin delta x = 0 → 0 ≤ w x) ∨ (∀ x, lin delta x = 0 → w x ≤ 0) := by
  classical
  have key (z : Point N) (hz : lin delta z = 0) :
      ∀ t, 0 ≤ t * lin L y + s *
        (relu (w (z + t • y) + t) - relu (w (z + t • y))) := by
    intro t
    have h1 := h (z + t • y)
    simpa only [lin_add_right, lin_smul_right, hz, hker z hz,
      hy, mul_one, zero_add] using h1
  have hc (z : Point N) : ContinuousAt (fun t : ℝ => w (z + t • y)) 0 :=
    (hw.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
  by_cases hp : ∃ z, lin delta z = 0 ∧ 0 < w z
  · obtain ⟨z, hz, hzp⟩ := hp
    have hplus : lin L y = -s := slope_at_positive (fun t => w (z + t • y))
      (hc z) (by simpa using hzp) _ _ (key z hz)
    left
    intro x hx
    by_contra hxn
    have hxneg : w x < 0 := lt_of_not_ge hxn
    have hminus : lin L y = 0 := slope_at_negative (fun t => w (x + t • y))
      (hc x) (by simpa using hxneg) _ _ (key x hx)
    exact hs (by linarith)
  · right
    intro x hx
    exact le_of_not_gt fun hxpos => hp ⟨x, hx, hxpos⟩

#print axioms transverse_sign

/-- A linear odd part on a hyperplane already forces at most four inputs. -/
theorem odd_on_kernel_bound [NeZero N] (delta c : Point N)
    (h : ∀ x, lin delta x = 0 → Maximum N x - Maximum N (-x) = lin c x) :
    N ≤ 4 := by
  have hL : ∀ x ∈ LinearMap.ker (linMap delta),
      Finset.univ.sup' Finset.univ_nonempty x +
        Finset.univ.inf' Finset.univ_nonempty x = linMap c x := by
    intro x hx
    have he := h x (LinearMap.mem_ker.1 hx)
    rw [Maximum_neg] at he
    change _ = lin c x
    change Maximum N x + _ = _
    linarith
  have hd := finrank_le_of_maxmin_univ (LinearMap.ker (linMap delta)) (linMap c) hL
  rw [Fintype.card_fin] at hd
  have hr := LinearMap.finrank_range_add_finrank_ker (linMap delta)
  have hrange : finrank ℝ (LinearMap.range (linMap delta)) ≤ 1 := by
    have he := Submodule.finrank_le (LinearMap.range (linMap delta))
    rwa [finrank_self] at he
  rw [finrank_fin_fun] at hr
  have hdiv := Nat.mul_div_le N 2
  linarith

/-- The two normalized asymptotic identities of a three-neuron network are
incompatible with five or more input coordinates. All model-sensitive
assumptions are explicit; the preactivations need only have linear odd parts,
and only the common preactivation needs continuity. -/
theorem normalized_three_bound [NeZero N]
    (u v w : Point N → ℝ) (hu : OddLin u) (hv : OddLin v) (hw : OddLin w)
    (hwc : Continuous w) (alpha beta delta : Point N) (s : ℝ) (hs : s ≠ 0)
    (hplus : ∀ x, Maximum N x = u x + lin alpha x - relu (v x) +
      s * relu (w x + lin delta x))
    (hminus : ∀ x, Maximum N x = -v x - lin beta x + relu (u x) +
      s * relu (w x)) : N ≤ 4 := by
  classical
  let L := alpha + beta
  have hkey : ∀ x, relu (-u x) + relu (-v x) = lin L x +
      s * (relu (w x + lin delta x) - relu (w x)) := by
    intro x
    have hp := hplus x
    have hm := hminus x
    have he1 := relu_sub_relu_neg (u x)
    have he2 := relu_sub_relu_neg (v x)
    dsimp [L]
    rw [lin_add_left]
    linarith
  have hpos : ∀ x, 0 ≤ lin L x +
      s * (relu (w x + lin delta x) - relu (w x)) := by
    intro x
    rw [← hkey x]
    exact add_nonneg (relu_nonneg _) (relu_nonneg _)
  have hker : ∀ x, lin delta x = 0 → lin L x = 0 := by
    intro x hx
    have hp := hpos x
    have hm := hpos (-x)
    rw [hx, add_zero, sub_self, mul_zero, add_zero] at hp
    rw [lin_neg_right, lin_neg_right, hx, neg_zero, add_zero,
      sub_self, mul_zero, add_zero] at hm
    linarith
  have hvker : ∀ x, lin delta x = 0 → 0 ≤ v x := by
    intro x hx
    have he := hkey x
    rw [hker x hx, hx, add_zero, sub_self, mul_zero, add_zero] at he
    have hn := relu_nonneg (-u x)
    have hv' : -v x ≤ relu (-v x) := le_max_right _ _
    linarith
  let b : Point N → ℝ := fun x => u x + lin alpha x - v x
  have hb : OddLin b :=
    ((hu.add (oddLin_lin alpha)).add (hv.const_mul (-1))).congr fun x => by
      dsimp [b]; ring
  have hrep : ∀ x, lin delta x = 0 →
      Maximum N x = b x + s * relu (w x) := by
    intro x hx
    have he := hplus x
    rw [relu_of_nonneg (hvker x hx), hx, add_zero] at he
    exact he
  by_cases hd : ∀ x, lin delta x = 0
  · obtain ⟨c, hc⟩ := hb
    have he := free_bound ({0} : Finset ℕ) (fun _ => w) (fun _ => hw) c (fun _ => s)
      (fun x => by
        simp only [Finset.sum_singleton]
        rw [hrep x (hd x), hrep (-x) (hd (-x))]
        have hbc := hc x
        linarith)
    simpa using he
  · obtain ⟨z, hz⟩ := not_forall.1 hd
    let y := (lin delta z)⁻¹ • z
    have hy : lin delta y = 1 := by
      dsimp [y]
      rw [lin_smul_right, inv_mul_cancel hz]
    have hsign := transverse_sign w hwc L delta s hs hpos hker y hy
    rcases hsign with hnonneg | hnonpos
    · have hbw := hb.add (hw.const_mul s)
      obtain ⟨c, hc⟩ := hbw
      apply odd_on_kernel_bound delta c
      intro x hx
      have hnx : lin delta (-x) = 0 := by rw [lin_neg_right, hx, neg_zero]
      rw [hrep x hx, hrep (-x) hnx, relu_of_nonneg (hnonneg x hx),
        relu_of_nonneg (hnonneg (-x) hnx)]
      exact hc x
    · obtain ⟨c, hc⟩ := hb
      apply odd_on_kernel_bound delta c
      intro x hx
      have hnx : lin delta (-x) = 0 := by rw [lin_neg_right, hx, neg_zero]
      rw [hrep x hx, hrep (-x) hnx, relu_of_nonpos (hnonpos x hx),
        relu_of_nonpos (hnonpos (-x) hnx)]
      simpa using hc x

#print axioms normalized_three_bound

lemma continuous_Gp {h₁ h₂ : ℕ} (net : ZNet N h₁ h₂) (k : Fin h₂) :
    Continuous (net.Gp k) := by
  have hlin (a : Point N) : Continuous (lin a) :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
  unfold ZNet.Gp
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  unfold pick
  split_ifs
  · exact hlin _
  · exact continuous_const
  · exact continuous_relu.comp (hlin _)

lemma signed_relu (d t : ℝ) :
    (if d < 0 then (-1 : ℝ) else 1) * relu (|d| * t) = d * relu t := by
  have hr : relu (|d| * t) = |d| * relu t := by
    unfold relu
    rw [mul_max_of_nonneg _ _ (abs_nonneg d), mul_zero]
  rw [hr]
  split_ifs with hd
  · rw [abs_of_neg hd]; ring
  · rw [abs_of_nonneg (not_lt.1 hd)]; ring

/-- The complete bias-free network theorem: the second hidden layer has at
least four neurons for every input arity at least five. -/
theorem second_width_four [NeZero N] {h₁ h₂ : ℕ} (hN : 5 ≤ N)
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) : 4 ≤ h₂ := by
  classical
  by_contra hlt
  have hb := net.second_width_ge_three (by omega : 3 ≤ N) h
  have h3 : h₂ = 3 := by omega
  subst h₂
  have b1 := net.card_Zp h
  have b2 := net.card_Zm h
  obtain ⟨hsl, hrest⟩ := net.max_plus h
  obtain ⟨hsl', hrest'⟩ := net.max_minus h
  obtain ⟨n, hTn, hdn⟩ := exists_pos_term net.d net.Tp (by
    unfold ZNet.slope at hsl; rw [hsl]; norm_num)
  obtain ⟨m, hTm, hdm⟩ := exists_neg_term net.d net.negIn.Tp (by
    unfold ZNet.slope at hsl'; simp only [ZNet.negIn] at hsl' ⊢; rw [hsl']; norm_num)
  have hnm : n ≠ m := fun e => by rw [e] at hdn; linarith
  have two : ∀ (Z : Finset (Fin 3)) (a b : Fin 3), a ∉ Z → b ∉ Z → a ≠ b →
      Z.card + 2 ≤ 3 := by
    intro Z a b ha hb hab
    have he := Finset.card_le_univ (insert a (insert b Z))
    rw [Finset.card_insert_of_not_mem (by simp [hab, ha]),
      Finset.card_insert_of_not_mem hb, Fintype.card_fin] at he
    exact he
  by_cases c1 : ∃ k, k ≠ n ∧ net.Tp k ≠ 0
  · obtain ⟨k, hkn, hk⟩ := c1
    have he := two (Finset.univ.filter fun k => net.Tp k = 0) n k
      (by simp [hTn.ne']) (by simp [hk]) hkn.symm
    omega
  by_cases c2 : ∃ k, k ≠ m ∧ net.negIn.Tp k ≠ 0
  · obtain ⟨k, hkm, hk⟩ := c2
    have he := two (Finset.univ.filter fun k => net.negIn.Tp k = 0) m k
      (by simp [hTm.ne']) (by simp [hk]) hkm.symm
    omega
  push_neg at c1 c2
  let K := (Finset.univ.erase n).erase m
  have hm : m ∈ Finset.univ.erase n := Finset.mem_erase.2 ⟨hnm.symm, Finset.mem_univ m⟩
  have hK : K.card = 1 := by
    simp only [K, Finset.card_erase_of_mem hm, Finset.card_erase_of_mem (Finset.mem_univ n),
      Finset.card_univ, Fintype.card_fin]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hK
  have hrK : r ∈ K := by rw [hr]; simp
  have hrn : r ≠ n := (Finset.mem_erase.1 (Finset.mem_erase.1 hrK).2).1
  have hrm : r ≠ m := (Finset.mem_erase.1 hrK).1
  have split : ∀ f : Fin 3 → ℝ, ∑ k, f k = f n + f m + f r := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n), ← Finset.add_sum_erase _ _ hm]
    change f n + (f m + ∑ k in K, f k) = _
    rw [hr, Finset.sum_singleton]
    ring
  have Ep : ∀ x, Maximum N x = net.d n * net.Gp n x +
      net.d m * relu (net.Gp m x) + net.d r * relu (net.Gp r x) := by
    intro x
    rw [hrest x, ZNet.rest, split]
    simp only [pick, if_pos hTn, c1 m hnm.symm, c1 r hrn, lt_self_iff_false, if_false]
  have Em : ∀ x, Maximum N x = net.d n * relu (net.negIn.Gp n (-x)) +
      net.d m * net.negIn.Gp m (-x) + net.d r * relu (net.negIn.Gp r (-x)) := by
    intro x
    rw [hrest' x, ZNet.rest, split]
    have hd : net.negIn.d = net.d := rfl
    rw [hd]
    simp only [pick, if_pos hTm, c2 n hnm, c2 r hrm, lt_self_iff_false, if_false]
  obtain ⟨cn, hcn⟩ := net.Gp_sub_negIn n
  obtain ⟨cm, hcm⟩ := net.Gp_sub_negIn m
  obtain ⟨cr, hcr⟩ := net.Gp_sub_negIn r
  let s : ℝ := if net.d r < 0 then -1 else 1
  have hs : s ≠ 0 := by dsimp [s]; split_ifs <;> norm_num
  have hwr : ∀ x, |net.d r| * net.negIn.Gp r (-x) + lin (|net.d r| • cr) x =
      |net.d r| * net.Gp r x := by
    intro x
    rw [lin_smul_left]
    linear_combination -|net.d r| * hcr x
  have result := normalized_three_bound
    (fun x => net.d n * net.negIn.Gp n (-x))
    (fun x => (-net.d m) * net.Gp m x)
    (fun x => |net.d r| * net.negIn.Gp r (-x))
    ((net.negIn.oddLin_Gp n).comp_neg.const_mul _)
    ((net.oddLin_Gp m).const_mul _)
    ((net.negIn.oddLin_Gp r).comp_neg.const_mul _)
    (continuous_const.mul ((continuous_Gp net.negIn r).comp continuous_neg))
    (net.d n • cn) (net.d m • cm) (|net.d r| • cr) s hs
    (fun x => by
      rw [hwr x, relu_mul_pos (neg_pos.2 hdm), lin_smul_left]
      change Maximum N x = _ - _ + (if net.d r < 0 then -1 else 1) * _
      rw [signed_relu, Ep x]
      linear_combination net.d n * hcn x)
    (fun x => by
      rw [relu_mul_pos hdn, lin_smul_left]
      change Maximum N x = _ - _ + _ + (if net.d r < 0 then -1 else 1) * _
      rw [signed_relu, Em x]
      linear_combination -net.d m * hcm x)
  omega

/-- Biases are allowed in the actual network model. -/
theorem network_second_width_four [NeZero N] {h₁ h₂ : ℕ} (hN : 5 ≤ N)
    (net : Network N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) : 4 ≤ h₂ :=
  second_width_four hN net.toZ (net.toZ_eval_of_max h)

#print axioms second_width_four
#print axioms network_second_width_four

end MaxCaterpillar.Frontier.OvernightGeneral
