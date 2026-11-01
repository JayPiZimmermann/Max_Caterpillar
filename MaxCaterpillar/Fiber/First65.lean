import MaxCaterpillar.Frontier.Main
import MaxCaterpillar.Fiber.First65.Irredundancy
import MaxCaterpillar.Fiber.First65.TwoRootGeometry
import MaxCaterpillar.Fiber.First65.CarrierPair

/-! # The first diagonal-slope reduction for width-six Max4 fibers

Every exact Max4 network with six first-hidden-layer neurons has either two
positive, two negative and two zero diagonal slopes, or one positive, one
negative and four zero slopes. This is a necessary reduction for the full
first-layer classification; no component count is asserted in this module.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Frontier

open BigOperators

variable {N h₁ h₂ : ℕ}

/-- The singleton-positive-row decomposition is an algebraic property of the
diagonal limit, independently of which target the network computes. -/
lemma ZNet.rest_eq_of_single (net : ZNet N h₁ h₂) (p : Fin h₁)
    (hsp : 0 < net.s p) (hp : ∀ j, 0 < net.s j → j = p) :
    ∀ x, net.rest x =
      (∑ k, net.d k * pick (net.Tp k) (net.W k p) 0) * lin (net.A p) x +
        net.Psi (net.rho x) := by
  have hG : ∀ k x, net.Gp k x = net.W k p * lin (net.A p) x +
      ∑ j, net.W k j * net.rho x j := by
    intro k x
    have hterm : ∀ j, net.W k j *
        pick (net.s j) (lin (net.A j) x) (relu (lin (net.A j) x)) =
        (if p = j then net.W k p * lin (net.A p) x else 0) +
          net.W k j * net.rho x j := by
      intro j
      by_cases hj : p = j
      · subst hj
        simp [pick, ZNet.rho, hsp, hsp.ne']
      · have hj' : ¬ 0 < net.s j := fun h' => hj (hp j h').symm
        rw [if_neg hj]
        unfold pick ZNet.rho
        rw [if_neg hj']
        by_cases hs : net.s j < 0
        · rw [if_pos hs, if_neg (ne_of_lt hs)]
          ring
        · have hs0 : net.s j = 0 := le_antisymm (not_lt.1 hj') (not_lt.1 hs)
          rw [if_neg hs, if_pos hs0]
          ring
    rw [ZNet.Gp, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
      Finset.sum_ite_eq]
    simp
  have hT : ∀ k, net.Tp k = net.W k p * net.s p := by
    intro k
    rw [ZNet.Tp, Finset.sum_eq_single p (fun j _ hj => by
      have hj' : ¬ 0 < net.s j := fun h' => hj (hp j h')
      simp [pick, hj']) (by simp)]
    simp [pick, hsp]
  intro x
  rw [ZNet.rest, ZNet.Psi, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hG]
  unfold pick
  split_ifs with h1 h2
  · ring
  · ring
  · have hW : net.W k p = 0 := by
      have hz : net.W k p * net.s p = 0 := by rw [← hT]; linarith
      rcases mul_eq_zero.1 hz with hw | hs
      · exact hw
      · exact absurd hs hsp.ne'
    rw [hW]
    ring

lemma ZNet.rho_negIn_neg (net : ZNet N h₁ h₂) (x : Point N) :
    net.negIn.rho (-x) = net.rho x := by
  funext j
  simp only [ZNet.rho, ZNet.negIn_s, neg_eq_zero]
  simp only [ZNet.negIn, lin_neg_left, lin_neg_right, neg_neg]

/-- The negative-diagonal version of the singleton-carrier decomposition. -/
lemma ZNet.max_eq_of_single_neg [NeZero N] (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x) (p : Fin h₁) (hsp : net.s p < 0)
    (hp : ∀ j, net.s j < 0 → j = p) :
    ∀ x, Maximum N x =
      (∑ k, net.d k * pick (net.negIn.Tp k) (net.W k p) 0) * lin (net.A p) x +
        net.negIn.Psi (net.rho x) := by
  intro x
  rw [(net.max_minus h).2 x]
  have hsp' : 0 < net.negIn.s p := by rw [net.negIn_s]; linarith
  have hp' : ∀ j, 0 < net.negIn.s j → j = p := by
    intro j hj
    apply hp j
    rw [net.negIn_s] at hj
    linarith
  rw [net.negIn.rest_eq_of_single p hsp' hp', net.rho_negIn_neg]
  simp only [ZNet.negIn, lin_neg_left, lin_neg_right, neg_neg]

/-- The negative-diagonal counterpart of Lemma M. -/
theorem ZNet.lemmaM_neg [NeZero N] (hN : 4 ≤ N) (net : ZNet N h₁ h₂)
    (h : ∀ x, net.eval x = Maximum N x)
    (hm1 : (Finset.univ.filter fun j => net.s j < 0).card = 1)
    (hle : (Finset.univ.filter fun j => net.s j ≤ 0).card = N) : False := by
  obtain ⟨p, hpset⟩ := Finset.card_eq_one.1 hm1
  have hsp : net.s p < 0 := by
    have hp : p ∈ Finset.univ.filter fun j => net.s j < 0 := by rw [hpset]; simp
    simpa using hp
  have hp : ∀ j, net.s j < 0 → j = p := fun j hj => by
    have hj' : j ∈ Finset.univ.filter fun j => net.s j < 0 := by simp [hj]
    rw [hpset] at hj'
    simpa using hj'
  set Jle := Finset.univ.filter fun j => net.s j ≤ 0 with hJle
  set J0 := Finset.univ.filter fun j => net.s j = 0 with hJ0
  have hJ0le : ∀ j ∈ J0, j ∈ Jle := fun j hj => by
    simp only [hJ0, hJle, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith
  have hinj : Function.Injective (net.rowMap Jle) :=
    (net.rowMap_injective_iff _).2 fun w hw =>
      net.ker_minus h w fun j hj => hw j (by simp [hJle, hj])
  have hsurj : Function.Surjective (net.rowMap Jle) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
    rw [FiniteDimensional.finrank_fin_fun, FiniteDimensional.finrank_fintype_fun_eq_card,
      Fintype.card_coe, hle]
  set κ := ∑ k, net.d k * pick (net.negIn.Tp k) (net.W k p) 0
  have hmax := net.max_eq_of_single_neg h p hsp hp
  have hs0 : ∀ j ∈ J0, ∑ i, net.A j i = 0 := fun j hj => by
    simp only [hJ0, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj
  have hu : ∀ j ∈ J0, ∃ u : Point N, ∀ j' ∈ J0,
      lin (net.A j') u = if j' = j then 1 else 0 := by
    intro j _
    obtain ⟨u, hu⟩ := hsurj (fun j' => if (j' : Fin h₁) = j then 1 else 0)
    exact ⟨u, fun j' hj' => congr_fun hu ⟨j', hJ0le j' hj'⟩⟩
  have hker : ∀ w, (∀ j ∈ J0, lin (net.A j) w = 0) → ∃ t, w = diag t := by
    intro w hw
    refine ⟨lin (net.A p) w / net.s p, ?_⟩
    have hz := net.ker_minus h (w - diag (lin (net.A p) w / net.s p)) (fun j hj => by
      rw [lin_sub_right, lin_diag]
      rcases hj.lt_or_eq with hj | hj
      · rw [hp j hj]
        show lin (net.A p) w - lin (net.A p) w / net.s p * net.s p = 0
        rw [div_mul_cancel _ hsp.ne, sub_self]
      · have hj0 : j ∈ J0 := by simp [hJ0, hj]
        rw [hw j hj0]
        unfold ZNet.s at hj
        rw [hj]
        ring)
    exact sub_eq_zero.1 hz
  have hH : ∀ x x', (∀ j ∈ J0, relu (lin (net.A j) x) = relu (lin (net.A j) x')) →
      Maximum N x - lin (κ • net.A p) x = Maximum N x' - lin (κ • net.A p) x' := by
    intro x x' hxx
    have hρ : net.rho x = net.rho x' := by
      funext j
      unfold ZNet.rho
      split_ifs with hj
      · exact hxx j (by simp [hJ0, hj])
      · rfl
    rw [hmax x, hmax x', lin_smul_left, lin_smul_left, hρ]
    ring
  obtain ⟨i0, hi0⟩ := lemmaM_core net.A J0 (κ • net.A p) hs0 hu hker hH
  let q : Point N := -unitVec i0
  have hq : ∀ j ∈ J0, lin (net.A j) q ≠ 0 := fun j hj => by
    simp only [q, lin_neg_right, lin_unitVec, neg_ne_zero]
    exact hi0 j hj
  have hρloc : ∀ j, LocAff (fun x => net.rho x j) q := by
    intro j
    by_cases hj : net.s j = 0
    · have ha := (locAff_lin (net.A j) q).reluComp (hq j (by simp [hJ0, hj]))
      exact ha.congr fun x => by simp [ZNet.rho, hj]
    · exact (locAff_const 0 q).congr fun x => by simp [ZNet.rho, hj]
  have hS : ∀ k, LocAff (fun x => ∑ j, net.W k j * net.rho x j) q := fun k =>
    LocAff.sum _ fun j _ => (hρloc j).const_mul _
  have hPsi : LocOddLin (fun x => net.negIn.Psi (net.rho x)) q := by
    refine LocOddLin.sum _ fun k _ => ?_
    rcases lt_trichotomy (net.negIn.Tp k) 0 with hT | hT | hT
    · exact (locOddLin_const 0 q).congr fun x => by simp [pick, hT, not_lt.2 hT.le]
    · simp only [pick, hT, lt_irrefl, if_false]
      exact (hS k).relu_locOddLin.const_mul _
    · simp only [pick, if_pos hT]
      exact (hS k).locOddLin.const_mul _
  have hloc : LocOddLin (Maximum N) q :=
    ((((locAff_lin (net.A p) q).locOddLin).const_mul κ).add hPsi).congr
      fun x => (hmax x).symm
  refine not_locOddLin_max q (Finset.univ.erase i0) ?_ ?_ ?_ hloc
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · intro i hi
    simp [q, unitVec, Finset.ne_of_mem_erase hi]
  · intro i hi
    have hii : i = i0 := by
      by_contra hne
      exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
    simp [q, unitVec, hii]

/-- The nonpositive slopes split into the negative and zero slopes. -/
lemma card_negative_add_zero {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    (Finset.univ.filter fun j => s j < 0).card +
      (Finset.univ.filter fun j => s j = 0).card =
        (Finset.univ.filter fun j => s j ≤ 0).card := by
  classical
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter fun j => s j ≤ 0) (fun j => s j < 0)
  have hm : (Finset.univ.filter fun j => s j ≤ 0).filter (fun j => s j < 0) =
      Finset.univ.filter (fun j => s j < 0) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hz : (Finset.univ.filter fun j => s j ≤ 0).filter (fun j => ¬ s j < 0) =
      Finset.univ.filter (fun j => s j = 0) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hle, hlt⟩
      exact le_antisymm hle (not_lt.1 hlt)
    · intro h
      simp [h]
  rw [hm, hz] at hp
  exact hp

/-- At a top tie with one lowered coordinate, some invariant first row
vanishes. At `-eᵢ` that condition is exactly `Aⱼ i = 0`. -/
theorem ZNet.invariant_row_at_top_tie [NeZero N] (hN : 4 ≤ N)
    (net : ZNet N h₁ h₂) (h : ∀ x, net.eval x = Maximum N x) (i0 : Fin N) :
    ∃ j, net.s j = 0 ∧ net.A j i0 = 0 := by
  by_contra hn
  push_neg at hn
  let q : Point N := -unitVec i0
  have hrow : ∀ j, LocAff (fun x =>
      pick (net.s j) (lin (net.A j) x) (relu (lin (net.A j) x))) q := by
    intro j
    rcases lt_trichotomy (net.s j) 0 with hs | hs | hs
    · exact (locAff_const 0 q).congr fun x => by simp [pick, hs, not_lt.2 hs.le]
    · have hne : lin (net.A j) q ≠ 0 := by
        simp only [q, lin_neg_right, lin_unitVec, neg_ne_zero]
        exact hn j hs
      exact ((locAff_lin (net.A j) q).reluComp hne).congr fun x => by
        simp [pick, hs]
    · exact (locAff_lin (net.A j) q).congr fun x => by simp [pick, hs]
  have hG : ∀ k, LocAff (net.Gp k) q := fun k =>
    LocAff.sum _ fun j _ => (hrow j).const_mul _
  have hrest : LocOddLin net.rest q := by
    refine LocOddLin.sum _ fun k _ => ?_
    rcases lt_trichotomy (net.Tp k) 0 with hs | hs | hs
    · exact (locOddLin_const 0 q).congr fun x => by simp [pick, hs, not_lt.2 hs.le]
    · simp only [pick, hs, lt_irrefl, if_false]
      exact (hG k).relu_locOddLin.const_mul _
    · simp only [pick, if_pos hs]
      exact (hG k).locOddLin.const_mul _
  have hloc : LocOddLin (Maximum N) q :=
    hrest.congr fun x => ((net.max_plus h).2 x).symm
  refine not_locOddLin_max q (Finset.univ.erase i0) ?_ ?_ ?_ hloc
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · intro i hi
    simp [q, unitVec, Finset.ne_of_mem_erase hi]
  · intro i hi
    have hii : i = i0 := by
      by_contra hne
      exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
    simp [q, unitVec, hii]

/-- With six first-hidden-layer neurons, the diagonal slope counts are exactly
`(positive, negative, zero) = (2,2,2)` or `(1,1,4)`, at every second width. -/
theorem ZNet.max4_six_slope_counts (net : ZNet 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) :
    ((Finset.univ.filter fun j => 0 < net.s j).card = 2 ∧
      (Finset.univ.filter fun j => net.s j < 0).card = 2 ∧
      (Finset.univ.filter fun j => net.s j = 0).card = 2) ∨
    ((Finset.univ.filter fun j => 0 < net.s j).card = 1 ∧
      (Finset.univ.filter fun j => net.s j < 0).card = 1 ∧
      (Finset.univ.filter fun j => net.s j = 0).card = 4) := by
  have hn := net.card_nonneg h
  have hp := net.card_nonpos h
  obtain ⟨j, hj⟩ := net.exists_neg h
  obtain ⟨k, hk⟩ := net.exists_pos h
  have hm1 : 1 ≤ (Finset.univ.filter fun j => net.s j < 0).card :=
    Finset.card_pos.2 ⟨j, by simp [hj]⟩
  have hp1 : 1 ≤ (Finset.univ.filter fun j => 0 < net.s j).card :=
    Finset.card_pos.2 ⟨k, by simp [hk]⟩
  have hsplit := card_filter_split net.s
  have hsplit' := card_filter_split' net.s
  rw [Fintype.card_fin] at hsplit hsplit'
  have hz := card_negative_add_zero net.s
  have hp12 : (Finset.univ.filter fun j => 0 < net.s j).card = 1 ∨
      (Finset.univ.filter fun j => 0 < net.s j).card = 2 := by omega
  have hm12 : (Finset.univ.filter fun j => net.s j < 0).card = 1 ∨
      (Finset.univ.filter fun j => net.s j < 0).card = 2 := by omega
  rcases hp12 with hpv | hpv <;> rcases hm12 with hmv | hmv
  · right
    exact ⟨hpv, hmv, by omega⟩
  · exact False.elim (net.lemmaM le_rfl h hpv (by omega))
  · exact False.elim (net.lemmaM_neg le_rfl h hmv (by omega))
  · left
    exact ⟨hpv, hmv, by omega⟩

end Frontier

namespace Fiber

open BigOperators Frontier

variable {h₂ : ℕ}

/-- The full biased network inherits the exact six-row slope dichotomy by
homogeneous recession; its biases are unrestricted. -/
theorem max4_six_slope_counts (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) :
    ((Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 2 ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0).card = 2 ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2) ∨
    ((Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1 ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0).card = 1 ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4) :=
  net.toZ.max4_six_slope_counts (net.toZ_eval_of_max h)

/-- Every exact width-six first hidden layer has exactly two or four
translation-invariant rows. -/
theorem max4_six_invariant_row_count (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) :
    (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2 ∨
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4 := by
  rcases max4_six_slope_counts net h with hp | hp
  · exact Or.inl hp.2.2
  · exact Or.inr hp.2.2

/-- Triple-tie coverage for the weights of a full biased Max4 network. -/
theorem max4_invariant_row_at_top_tie {h₁ : ℕ} (net : Network 4 h₁ h₂)
    (h : ∀ x, net.eval x = Maximum 4 x) (i : Fin 4) :
    ∃ j, (∑ k, net.W₁ j k) = 0 ∧ net.W₁ j i = 0 :=
  net.toZ.invariant_row_at_top_tie le_rfl (net.toZ_eval_of_max h) i

/-- In the two-invariant-row stratum, those two rows are positive multiples
of the coordinate differences of a perfect matching. This classifies the
invariant rows, not yet the four carrier rows or the second hidden layer. -/
theorem max4_two_invariant_rows_are_complementary_roots (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 2) :
    ∃ j k : Fin 6, ∃ p q r s : Fin 4, ∃ ca cb : ℝ,
      j ≠ k ∧
      (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0) = {j, k} ∧
      p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      0 < ca ∧ 0 < cb ∧
      (∀ i, net.W₁ j i = ca * (if i = p then 1 else 0) -
        ca * (if i = q then 1 else 0)) ∧
      (∀ i, net.W₁ k i = cb * (if i = r then 1 else 0) -
        cb * (if i = s then 1 else 0)) := by
  classical
  obtain ⟨j, k, hjk, hset⟩ := Finset.card_eq_two.1 hcard
  have hj : ∑ i, net.W₁ j i = 0 := by
    have hm : j ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      rw [hset]
      simp
    simpa using hm
  have hk : ∑ i, net.W₁ k i = 0 := by
    have hm : k ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      rw [hset]
      simp
    simpa using hm
  have hj0 : net.W₁ j ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six h j
    exact hi (congr_fun he i)
  have hk0 : net.W₁ k ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := net.first_row_ne_zero_of_max4_six h k
    exact hi (congr_fun he i)
  have hdisj : ∀ i, net.W₁ j i = 0 ∨ net.W₁ k i = 0 := by
    intro i
    obtain ⟨a, ha, hai⟩ := max4_invariant_row_at_top_tie net h i
    have ham : a ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0 := by
      simp [ha]
    rw [hset] at ham
    simp only [Finset.mem_insert, Finset.mem_singleton] at ham
    rcases ham with haj | hak
    · exact Or.inl (haj ▸ hai)
    · exact Or.inr (hak ▸ hai)
  obtain ⟨p, q, r, s, ca, cb, hforms⟩ :=
    complementary_positive_coordinate_differences (net.W₁ j) (net.W₁ k)
      hj hk hj0 hk0 hdisj
  exact ⟨j, k, p, q, r, s, ca, cb, hjk, hset, hforms⟩

/-- In the four-invariant-row stratum, the remaining two first rows form one
oppositely oriented carrier pair. This conclusion allows arbitrary biases. -/
theorem max4_four_invariant_rows_have_opposite_carriers (net : Network 4 6 h₂)
    (h : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4) :
    ∃ p q : Fin 6, ∃ c : ℝ,
      p ≠ q ∧ 0 < c ∧ 0 < ∑ i, net.W₁ p i ∧ (∑ i, net.W₁ q i) < 0 ∧
      net.W₁ q = (-c) • net.W₁ p ∧
      ∀ j, j ≠ p → j ≠ q → (∑ i, net.W₁ j i) = 0 := by
  classical
  have hp1 : (Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i).card = 1 := by
    rcases max4_six_slope_counts net h with hd | hd
    · omega
    · exact hd.1
  have hm1 : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0).card = 1 := by
    rcases max4_six_slope_counts net h with hd | hd
    · omega
    · exact hd.2.1
  obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hp1
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hm1
  have hsp : 0 < ∑ i, net.W₁ p i := by
    have hm : p ∈ Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i := by rw [hp]; simp
    simpa using hm
  have hsq : (∑ i, net.W₁ q i) < 0 := by
    have hm : q ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0 := by rw [hq]; simp
    simpa using hm
  have hpq : p ≠ q := by intro he; subst q; linarith
  have hother : ∀ j, j ≠ p → j ≠ q → (∑ i, net.W₁ j i) = 0 := by
    intro j hjp hjq
    have hpos : ¬ 0 < ∑ i, net.W₁ j i := by
      intro hj
      have hm : j ∈ Finset.univ.filter fun j => 0 < ∑ i, net.W₁ j i := by simp [hj]
      rw [hp] at hm
      exact hjp (Finset.mem_singleton.1 hm)
    have hneg : ¬ (∑ i, net.W₁ j i) < 0 := by
      intro hj
      have hm : j ∈ Finset.univ.filter fun j => (∑ i, net.W₁ j i) < 0 := by simp [hj]
      rw [hq] at hm
      exact hjq (Finset.mem_singleton.1 hm)
    exact le_antisymm (not_lt.1 hpos) (not_lt.1 hneg)
  have he := Frontier.single_carrier_rows_proportional net h p q hsp hsq hother
  refine ⟨p, q, -((∑ i, net.W₁ q i) / ∑ i, net.W₁ p i), hpq,
    neg_pos.2 (div_neg_of_neg_of_pos hsq hsp), hsp, hsq, ?_, hother⟩
  simpa only [neg_neg] using he

/-- The exact coefficient restriction imposed by nonnegativity of the fourth
path row on the open target facet. This is an algebraic lemma: the separate
network-to-facet implication is not assumed here. -/
theorem path_facet_nonneg_iff (μ ν : ℝ) :
    (∀ a b : ℝ, 0 < a → b < 0 → 0 ≤ μ * a + (ν - μ) * b) ↔
      0 ≤ μ ∧ ν ≤ μ := by
  constructor
  · intro h
    have hμ : 0 ≤ μ := by
      by_contra hn
      have hμn : μ < 0 := lt_of_not_ge hn
      have ha : 0 < (ν - μ) ^ 2 + 1 := by nlinarith [sq_nonneg (ν - μ)]
      have hp : 0 < (ν - μ) ^ 2 + (ν - μ) + 1 := by
        nlinarith [sq_nonneg ((ν - μ) + 1 / 2)]
      have hv := h ((ν - μ) ^ 2 + 1) μ ha hμn
      have hn' := mul_neg_of_neg_of_pos hμn hp
      nlinarith only [hv, hn']
    refine ⟨hμ, ?_⟩
    by_contra hn
    have hd : 0 < ν - μ := by linarith
    have hb : -(μ ^ 2 + 1) < 0 := by nlinarith [sq_nonneg μ]
    have hp : 0 < μ ^ 2 - μ + 1 := by nlinarith [sq_nonneg (μ - 1 / 2)]
    have hv := h (ν - μ) (-(μ ^ 2 + 1)) hd hb
    have hn' := mul_pos hd hp
    nlinarith only [hv, hn']
  · rintro ⟨hμ, hν⟩ a b ha hb
    exact add_nonneg (mul_nonneg hμ ha.le)
      (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hν) hb.le)

end Fiber
end MaxCaterpillar
