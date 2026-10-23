import MaxCaterpillar.Frontier.Asymptotics

/-! # The first hidden layer: `h₁ ≥ N + 1`, and `h₁ ≥ 6` for `N = 4`

* Lemma S (`ZNet.card_nonneg`) and `J- ≠ ∅` give `h₁ ≥ N + 1`; for `N = 3` this is `h₁ ≥ 4`.
* For `N = 4`, `h₁ = 5` forces `|J+| = 1` and `|J+ ∪ J0| = 4`. Lemma M excludes this
  (for every `N ≥ 4`): by `(+∞)`, `max x - ℓ(x)` depends on `x` only through the numbers
  `σ(Aⱼ·x)`, `j ∈ J0`, with `ℓ` linear. Dual vectors `uⱼ` (`Aⱼ'·uⱼ = δⱼⱼ'`) and the matrix
  `Dᵢⱼ = uⱼ(i) - ℓ(uⱼ)` show that there is a coordinate `i₀` with `Aⱼ(i₀) ≠ 0` for every
  `j ∈ J0` (`lemmaM_core`). At `q = -e_{i₀}` every `J0` row is then nonzero, so the network
  is locally a one-hidden-layer function around `q` and has locally linear odd part there;
  but three coordinates of `q` tie at the top of the maximum (`not_locOddLin_max`).
-/

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

lemma card_filter_split {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    (Finset.univ.filter fun j => 0 ≤ s j).card + (Finset.univ.filter fun j => s j < 0).card =
      Fintype.card ι := by
  have := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun j => 0 ≤ s j)
  rw [Finset.card_univ] at this
  rw [← this]
  congr 2
  ext j; simp

lemma card_filter_split' {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    (Finset.univ.filter fun j => 0 < s j).card + (Finset.univ.filter fun j => s j ≤ 0).card =
      Fintype.card ι := by
  have := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun j => 0 < s j)
  rw [Finset.card_univ] at this
  rw [← this]
  congr 2
  ext j; simp

/-- `h₁ ≥ N + 1` for every bias-free network computing the maximum. -/
theorem ZNet.first_width_ge_succ [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) : N + 1 ≤ h₁ := by
  have h1 := net.card_nonneg h
  obtain ⟨j, hj⟩ := net.exists_neg h
  have h2 : 1 ≤ (Finset.univ.filter fun j => net.s j < 0).card :=
    Finset.card_pos.2 ⟨j, by simp [hj]⟩
  have := card_filter_split net.s
  rw [Fintype.card_fin] at this
  generalize (Finset.univ.filter fun j => 0 ≤ net.s j).card = a at *
  generalize (Finset.univ.filter fun j => net.s j < 0).card = b at *
  linarith

/-! ## Lemma M -/

/-- The linear-algebra core of Lemma M. -/
theorem lemmaM_core [NeZero N] {ι : Type*} [DecidableEq ι] (A : ι → Point N) (J0 : Finset ι)
    (c : Point N) (hs0 : ∀ j ∈ J0, ∑ i, A j i = 0)
    (hu : ∀ j ∈ J0, ∃ u : Point N, ∀ j' ∈ J0, lin (A j') u = if j' = j then 1 else 0)
    (hker : ∀ w, (∀ j ∈ J0, lin (A j) w = 0) → ∃ t, w = diag t)
    (hH : ∀ x x', (∀ j ∈ J0, relu (lin (A j) x) = relu (lin (A j) x')) →
      Maximum N x - lin c x = Maximum N x' - lin c x') :
    ∃ i0, ∀ j ∈ J0, A j i0 ≠ 0 := by
  choose! u hu using hu
  obtain ⟨X, hXdef⟩ : ∃ X : (ι → ℝ) → Point N, ∀ y, X y = ∑ j in J0, y j • u j :=
    ⟨_, fun _ => rfl⟩
  have hlinX : ∀ y, ∀ j' ∈ J0, lin (A j') (X y) = y j' := by
    intro y j' hj'
    rw [hXdef]
    simp only [lin_sum_right, lin_smul_right]
    rw [Finset.sum_eq_single_of_mem j' hj' (fun k hk hkj => by
      rw [hu k hk j' hj', if_neg (Ne.symm hkj), mul_zero])]
    rw [hu j' hj' j' hj', if_pos rfl, mul_one]
  obtain ⟨D, hD⟩ : ∃ D : Fin N → ι → ℝ, ∀ i j, D i j = u j i - lin c (u j) :=
    ⟨_, fun _ _ => rfl⟩
  have hX : ∀ y, Maximum N (X y) - lin c (X y) =
      Maximum N (fun i => ∑ j in J0, y j * D i j) := by
    intro y
    rw [← Maximum_sub_const]
    congr 1
    funext i
    simp only [hXdef, hD, lin_sum_right, lin_smul_right, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hrel : ∀ y y' : ι → ℝ, (∀ j ∈ J0, relu (y j) = relu (y' j)) →
      Maximum N (fun i => ∑ j in J0, y j * D i j) =
        Maximum N (fun i => ∑ j in J0, y' j * D i j) := by
    intro y y' hyy
    rw [← hX, ← hX]
    exact hH _ _ fun j hj => by rw [hlinX y j hj, hlinX y' j hj]; exact hyy j hj
  have hM0 : Maximum N (fun i => ∑ j in J0, (0 : ι → ℝ) j * D i j) = 0 := by
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact Maximum_zero
  have relu_neg_one : relu (-1) = relu 0 := by
    rw [relu_of_nonpos (by norm_num), relu_of_nonpos le_rfl]
  -- Step a: `D ≥ 0` on the columns in `J0`
  have hDnn : ∀ j ∈ J0, ∀ i, 0 ≤ D i j := by
    intro j hj i
    have e := hrel (fun k => if k = j then -1 else 0) 0 (fun k _ => by
      by_cases hk : k = j
      · simp only [hk, if_true, Pi.zero_apply]; exact relu_neg_one
      · simp only [hk, if_false, Pi.zero_apply])
    rw [hM0] at e
    have := le_Maximum (fun i => ∑ k in J0, (if k = j then (-1 : ℝ) else 0) * D i k) i
    rw [e] at this
    simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', if_pos hj] at this
    linarith
  -- Step b: a row `i0` of `D` vanishes on `J0`
  obtain ⟨i0, hi0⟩ : ∃ i0, ∀ k ∈ J0, D i0 k = 0 := by
    have e := hrel (fun _ => -1) 0 (fun k _ => by simp only [Pi.zero_apply]; exact relu_neg_one)
    rw [hM0] at e
    obtain ⟨i0, hi0⟩ := exists_eq_Maximum (fun i => ∑ k in J0, (-1 : ℝ) * D i k)
    rw [e] at hi0
    refine ⟨i0, (Finset.sum_eq_zero_iff_of_nonneg fun k hk => hDnn k hk i0).1 ?_⟩
    simp only [neg_one_mul, Finset.sum_neg_distrib] at hi0
    linarith
  refine ⟨i0, fun j hj => ?_⟩
  -- Step c: a row `i` of `D` equal to `m eⱼ` on `J0`
  set m := Maximum N (fun i => D i j) with hm
  have ec := hrel (fun k => if k = j then 1 else -1) (fun k => if k = j then 1 else 0)
    (fun k _ => by
      by_cases hk : k = j
      · simp only [hk, if_true]
      · simp only [hk, if_false]; exact relu_neg_one)
  have hsum1 : ∀ i, ∑ k in J0, (if k = j then (1 : ℝ) else -1) * D i k =
      D i j - ∑ k in J0.erase j, D i k := by
    intro i
    rw [← Finset.add_sum_erase J0 _ hj, if_pos rfl, one_mul,
      Finset.sum_congr rfl (fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)])]
    simp only [neg_one_mul, Finset.sum_neg_distrib]; ring
  have hsum2 : ∀ i, ∑ k in J0, (if k = j then (1 : ℝ) else 0) * D i k = D i j := by
    intro i
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos hj]
  simp only [hsum1, hsum2] at ec
  obtain ⟨i, hi⟩ := exists_eq_Maximum (fun i => D i j - ∑ k in J0.erase j, D i k)
  rw [ec] at hi
  have hle := le_Maximum (fun i => D i j) i
  rw [← hm] at hle
  simp only at hi hle
  have hnn : 0 ≤ ∑ k in J0.erase j, D i k :=
    Finset.sum_nonneg fun k hk => hDnn k (Finset.mem_of_mem_erase hk) i
  have hz : ∑ k in J0.erase j, D i k = 0 := by linarith
  have hDz : ∀ k ∈ J0, k ≠ j → D i k = 0 := fun k hk hkj =>
    (Finset.sum_eq_zero_iff_of_nonneg fun k hk => hDnn k (Finset.mem_of_mem_erase hk) i).1
      hz k (Finset.mem_erase.2 ⟨hkj, hk⟩)
  have hDij : D i j = m := by linarith
  -- Step d: `m > 0`
  have hmpos : 0 < m := by
    by_contra hmle
    push_neg at hmle
    have hcol : ∀ i', u j i' = lin c (u j) := fun i' => by
      have a := le_Maximum (fun i => D i j) i'
      rw [← hm] at a
      have b := hDnn j hj i'
      rw [hD] at a b
      linarith
    have := hu j hj j hj
    rw [if_pos rfl] at this
    have e : lin (A j) (u j) = lin c (u j) * ∑ i, A j i := by
      generalize lin c (u j) = L at hcol ⊢
      simp only [lin, hcol]
      rw [mul_comm, Finset.sum_mul]
    rw [e, hs0 j hj, mul_zero] at this
    norm_num at this
  have hii0 : i ≠ i0 := fun e => by
    rw [e, hi0 j hj] at hDij; linarith
  -- Step e: decompose `e_{i0}` and read off `Aⱼ(i0) m = -1`
  let β : ι → ℝ := fun k => lin (A k) (unitVec i0)
  obtain ⟨t, ht⟩ := hker (unitVec i0 - X β) (fun j' hj' => by
    rw [lin_sub_right, hlinX β j' hj', sub_self])
  have c1 : (unitVec i0 - X β) i = diag t i := congr_fun ht i
  have c2 : (unitVec i0 - X β) i0 = diag t i0 := congr_fun ht i0
  rw [Pi.sub_apply, unitVec_apply, if_neg hii0] at c1
  rw [Pi.sub_apply, unitVec_apply, if_pos rfl] at c2
  have c3 : diag t i = diag t i0 := rfl
  have hXdiff : X β i - X β i0 = ∑ k in J0, β k * D i k := by
    simp only [hXdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := hi0 k hk
    rw [hD] at this
    rw [hD]
    linear_combination (-β k) * this
  rw [Finset.sum_eq_single_of_mem j hj (fun k hk hkj => by rw [hDz k hk hkj, mul_zero]),
    hDij] at hXdiff
  have hβ : β j * m = -1 := by linarith
  have hβj : β j = A j i0 := lin_unitVec _ _
  intro hA
  rw [hβj, hA, zero_mul] at hβ
  norm_num at hβ

/-- `ρⱼ(x) = σ(Aⱼ·x)` for `j ∈ J0` and `0` otherwise. -/
noncomputable def ZNet.rho (net : ZNet N h₁ h₂) (x : Point N) (j : Fin h₁) : ℝ :=
  if net.s j = 0 then relu (lin (net.A j) x) else 0

/-- `Ψ(σ) = Σₖ dₖ pick(T⁺ₖ, Wₖ·σ, σ(Wₖ·σ))`. -/
noncomputable def ZNet.Psi (net : ZNet N h₁ h₂) (σ : Fin h₁ → ℝ) : ℝ :=
  ∑ k, net.d k * pick (net.Tp k) (∑ j, net.W k j * σ j) (relu (∑ j, net.W k j * σ j))

/-- With a single row `p` in `J+`, `(+∞)` reads `max x = κ (Aₚ·x) + Ψ(ρ(x))`. -/
lemma ZNet.max_eq_of_single (net : ZNet N h₁ h₂) [NeZero N]
    (h : ∀ x, net.eval x = Maximum N x) (p : Fin h₁) (hsp : 0 < net.s p)
    (hp : ∀ j, 0 < net.s j → j = p) :
    ∀ x, Maximum N x = (∑ k, net.d k * pick (net.Tp k) (net.W k p) 0) * lin (net.A p) x +
      net.Psi (net.rho x) := by
  have hG : ∀ k x, net.Gp k x = net.W k p * lin (net.A p) x + ∑ j, net.W k j * net.rho x j := by
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
  have hT : ∀ k, net.Tp k = net.W k p * net.s p := by
    intro k
    rw [ZNet.Tp, Finset.sum_eq_single p (fun j _ hj => by
      have hj' : ¬ 0 < net.s j := fun h' => hj (hp j h')
      simp [pick, hj']) (by simp)]
    simp [pick, hsp]
  intro x
  rw [(net.max_plus h).2 x, ZNet.rest, ZNet.Psi, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hG]
  unfold pick
  split_ifs with h1 h2
  · ring
  · ring
  · have hW : net.W k p = 0 := by
      have : net.W k p * net.s p = 0 := by rw [← hT]; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · exact absurd h' hsp.ne'
    rw [hW]; ring

/-- **Lemma M.** For `N ≥ 4` no bias-free network computing the maximum has exactly one
first-layer row with `s > 0` and exactly `N` rows with `s ≥ 0`. -/
theorem ZNet.lemmaM [NeZero N] (hN : 4 ≤ N) (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x)
    (hp1 : (Finset.univ.filter fun j => 0 < net.s j).card = 1)
    (hge : (Finset.univ.filter fun j => 0 ≤ net.s j).card = N) : False := by
  obtain ⟨p, hpset⟩ := Finset.card_eq_one.1 hp1
  have hsp : 0 < net.s p := by
    have : p ∈ Finset.univ.filter fun j => 0 < net.s j := by rw [hpset]; simp
    simpa using this
  have hp : ∀ j, 0 < net.s j → j = p := fun j hj => by
    have : j ∈ Finset.univ.filter fun j => 0 < net.s j := by simp [hj]
    rw [hpset] at this; simpa using this
  set Jge := Finset.univ.filter fun j => 0 ≤ net.s j with hJge
  set J0 := Finset.univ.filter fun j => net.s j = 0 with hJ0
  have hJ0ge : ∀ j ∈ J0, j ∈ Jge := fun j hj => by
    simp only [hJ0, hJge, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; linarith
  have hinj : Function.Injective (net.rowMap Jge) :=
    (net.rowMap_injective_iff _).2 fun w hw =>
      net.ker_plus h w fun j hj => hw j (by simp [hJge, hj])
  have hsurj : Function.Surjective (net.rowMap Jge) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
    rw [FiniteDimensional.finrank_fin_fun, FiniteDimensional.finrank_fintype_fun_eq_card,
      Fintype.card_coe, hge]
  set κ := ∑ k, net.d k * pick (net.Tp k) (net.W k p) 0
  have hmax := net.max_eq_of_single h p hsp hp
  -- hypotheses of the core lemma
  have hs0 : ∀ j ∈ J0, ∑ i, net.A j i = 0 := fun j hj => by
    simp only [hJ0, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj
  have hu : ∀ j ∈ J0, ∃ u : Point N, ∀ j' ∈ J0, lin (net.A j') u = if j' = j then 1 else 0 := by
    intro j _
    obtain ⟨u, hu⟩ := hsurj (fun j' => if (j' : Fin h₁) = j then 1 else 0)
    exact ⟨u, fun j' hj' => congr_fun hu ⟨j', hJ0ge j' hj'⟩⟩
  have hker : ∀ w, (∀ j ∈ J0, lin (net.A j) w = 0) → ∃ t, w = diag t := by
    intro w hw
    refine ⟨lin (net.A p) w / net.s p, ?_⟩
    have := net.ker_plus h (w - diag (lin (net.A p) w / net.s p)) (fun j hj => by
      rw [lin_sub_right, lin_diag]
      rcases hj.lt_or_eq with hj | hj
      · rw [hp j hj]
        show lin (net.A p) w - lin (net.A p) w / net.s p * net.s p = 0
        rw [div_mul_cancel _ hsp.ne', sub_self]
      · have : j ∈ J0 := by simp [hJ0, hj.symm]
        rw [hw j this]; unfold ZNet.s at hj; rw [← hj]; ring)
    exact sub_eq_zero.1 this
  have hH : ∀ x x', (∀ j ∈ J0, relu (lin (net.A j) x) = relu (lin (net.A j) x')) →
      Maximum N x - lin (κ • net.A p) x = Maximum N x' - lin (κ • net.A p) x' := by
    intro x x' hxx
    have hρ : net.rho x = net.rho x' := by
      funext j
      unfold ZNet.rho
      split_ifs with hj
      · exact hxx j (by simp [hJ0, hj])
      · rfl
    rw [hmax x, hmax x', lin_smul_left, lin_smul_left, hρ]; ring
  obtain ⟨i0, hi0⟩ := lemmaM_core net.A J0 (κ • net.A p) hs0 hu hker hH
  -- the germ at `q = -e_{i0}`
  let q : Point N := -unitVec i0
  have hq : ∀ j ∈ J0, lin (net.A j) q ≠ 0 := fun j hj => by
    simp only [q, lin_neg_right, lin_unitVec, neg_ne_zero]; exact hi0 j hj
  have hρloc : ∀ j, LocAff (fun x => net.rho x j) q := by
    intro j
    by_cases hj : net.s j = 0
    · have := (locAff_lin (net.A j) q).reluComp (hq j (by simp [hJ0, hj]))
      exact this.congr fun x => by simp [ZNet.rho, hj]
    · exact (locAff_const 0 q).congr fun x => by simp [ZNet.rho, hj]
  have hS : ∀ k, LocAff (fun x => ∑ j, net.W k j * net.rho x j) q := fun k =>
    LocAff.sum _ fun j _ => (hρloc j).const_mul _
  have hPsi : LocOddLin (fun x => net.Psi (net.rho x)) q := by
    refine LocOddLin.sum _ fun k _ => ?_
    rcases lt_trichotomy (net.Tp k) 0 with hT | hT | hT
    · exact (locOddLin_const 0 q).congr fun x => by simp [pick, hT, not_lt.2 hT.le]
    · simp only [pick, hT, lt_irrefl, if_false]
      exact (hS k).relu_locOddLin.const_mul _
    · simp only [pick, if_pos hT]
      exact (hS k).locOddLin.const_mul _
  have hloc : LocOddLin (Maximum N) q :=
    ((((locAff_lin (net.A p) q).locOddLin).const_mul κ).add hPsi).congr fun x => (hmax x).symm
  refine not_locOddLin_max q (Finset.univ.erase i0) ?_ ?_ ?_ hloc
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · intro i hi
    simp [q, unitVec, Finset.ne_of_mem_erase hi]
  · intro i hi
    have : i = i0 := by
      by_contra hne; exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
    simp [q, unitVec, this]

/-- **First width for `N = 3`**: `h₁ ≥ 4`. -/
theorem ZNet.first_width_ge_four_max3 (net : ZNet 3 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 3 x) : 4 ≤ h₁ :=
  net.first_width_ge_succ h

/-- **First width for `N = 4`**: `h₁ ≥ 6`. -/
theorem ZNet.first_width_ge_six_max4 (net : ZNet 4 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) : 6 ≤ h₁ := by
  by_contra hlt
  push_neg at hlt
  have a1 := net.card_nonneg h
  have a2 := net.card_nonpos h
  obtain ⟨j, hj⟩ := net.exists_neg h
  obtain ⟨j', hj'⟩ := net.exists_pos h
  have a3 : 1 ≤ (Finset.univ.filter fun j => net.s j < 0).card :=
    Finset.card_pos.2 ⟨j, by simp [hj]⟩
  have a4 : 1 ≤ (Finset.univ.filter fun j => 0 < net.s j).card :=
    Finset.card_pos.2 ⟨j', by simp [hj']⟩
  have b1 := card_filter_split net.s
  have b2 := card_filter_split' net.s
  rw [Fintype.card_fin] at b1 b2
  have h5 : h₁ ≤ 5 := Nat.lt_succ_iff.mp hlt
  exact net.lemmaM le_rfl h (le_antisymm (by linarith) a4) (le_antisymm (by linarith) a1)

end Frontier
end MaxCaterpillar
