import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.Reindex
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.CarrierPatternCounts
import MaxCaterpillar.Fiber.Count65.Star.PhysicalSigns
import MaxCaterpillar.Fiber.Count65.Star.Profile

/-! # An actual star completion uses exactly two translation carriers

All hypotheses concern the original physical network and its all-real-input
function. Arbitrary biases are permitted; the proved recession identity removes
them before the analytic tail argument. Positive output normalization and an
actual hidden permutation supply the finite roles, rather than assuming them.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.Star
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Star65
open MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open MaxCaterpillar.Fiber.Mixed65 (exists_positive_passing_of_slope exists_negative_passing_of_slope)

private theorem tail_positive_count (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (a : Fin 5 → ℝ) (hcard : (stationary a).card = 3)
    (h : ∀ x : InvariantState, invariantTarget x =
      (∑ j in Finset.univ.filter (fun j => 0 < a j),
        net.w₃ j * physicalInvariantPart net t j x) +
      ∑ j in stationary a, net.w₃ j * relu (physicalInvariantPart net t j x)) :
    ((stationary a).filter fun j => 0 < net.w₃ j).card = 2 := by
  classical
  let S := stationary a
  let d := physicalResidualSystem net S (fun j => if 0 < a j then net.w₃ j else 0)
  have hd : RepresentsStar d t := by
    apply physicalResidualSystem_represents
    intro x
    convert h x using 1
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hh <;> simp [hh]
  obtain ⟨i,j,hij,hi,hj,_,_⟩ := two_positive_carriers d t ht ht1 hd
  obtain ⟨k,hk⟩ := exists_negative_gate d t ht ht1 hd
  let P := S.filter fun j => 0 < net.w₃ j
  have hiP : i.val ∈ P := Finset.mem_filter.mpr ⟨i.property,hi⟩
  have hjP : j.val ∈ P := Finset.mem_filter.mpr ⟨j.property,hj⟩
  have hlow : 2 ≤ P.card := by
    have hsub : ({i.val,j.val} : Finset (Fin 5)) ⊆ P := by
      intro u hu
      rcases Finset.mem_insert.mp hu with hu | hu
      · simpa only [hu] using hiP
      · simpa only [Finset.mem_singleton.mp hu] using hjP
    have hne : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hpair : ({i.val,j.val} : Finset (Fin 5)).card = 2 := by simp [hne]
    simpa only [hpair] using Finset.card_le_of_subset hsub
  have hkP : k.val ∉ P := by
    intro hh
    have hpos := (Finset.mem_filter.mp hh).2
    change net.w₃ k.val < 0 at hk
    linarith only [hk,hpos]
  have hsub : insert k.val P ⊆ S := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · simpa only [hu] using k.property
    · exact (Finset.mem_filter.mp hu).1
  have hup := Finset.card_le_of_subset hsub
  rw [Finset.card_insert_of_not_mem hkP] at hup
  change P.card + 1 ≤ (stationary a).card at hup
  linarith only [hlow,hup,hcard]

private theorem stationary_card_of_pair (a : Fin 5 → ℝ)
    (h : (moving a).card = 2) : (stationary a).card = 3 := by
  classical
  have hh := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin 5))) (fun j => a j = 0)
  have hh' : (stationary a).card + (moving a).card = 5 := by
    simpa only [stationary,moving,Finset.card_univ,Fintype.card_fin] using hh
  linarith only [hh',h]

/-- The normalized finite three-carrier pattern contradicts the actual star
three-gate tail classification, for either possible shared output sign. -/
theorem canonical_roles_impossible (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x)
    (r : CanonicalCarrierRoles net 4 5) : False := by
  have h := physical_signed_carrier_identity_any_bias net t hW hmax
  have ha : net.W₂ 0 4 ≠ 0 := (r.first_nonzero_iff 0).mpr (Or.inl rfl)
  have hc : net.W₂ 1 4 ≠ 0 := (r.first_nonzero_iff 1).mpr (Or.inr rfl)
  have hd : net.W₂ 2 5 ≠ 0 := (r.second_nonzero_iff 2).mpr (Or.inr rfl)
  have hz15 := r.second_zero 1 (by decide) (by decide)
  have hz24 := r.first_zero 2 (by decide) (by decide)
  have hz34 := r.first_zero 3 (by decide) (by decide)
  have hz35 := r.second_zero 3 (by decide) (by decide)
  have hz44 := r.first_zero 4 (by decide) (by decide)
  have hz45 := r.second_zero 4 (by decide) (by decide)
  have hQ := physicalInvariantPart_mem net t 0
  have hC := physicalInvariantPart_mem net t 1
  have hD := physicalInvariantPart_mem net t 2
  have hI := physicalInvariantPart_mem net t 3
  have hJ := physicalInvariantPart_mem net t 4
  rcases r.shared_unit with hs | hs
  · have h1 : net.w₃ 1 = -1 := by rw [r.first_exclusive,hs]
    have h2 : net.w₃ 2 = -1 := by rw [r.second_exclusive,hs]
    have h4 : net.w₃ 4 = 1 := by rw [r.second_invariant,hs]
    apply no_three_moving_shared_positive (featureSpace t)
      (net.W₂ 0 4) (net.W₂ 0 5) (net.W₂ 1 4) (net.W₂ 2 5)
      (physicalInvariantPart net t 0) (physicalInvariantPart net t 1)
      (physicalInvariantPart net t 2)
      (fun x => relu (physicalInvariantPart net t 3 x) +
        relu (physicalInvariantPart net t 4 x)) invariantTarget ha hc hQ hC hD
    · simpa only [one_mul] using star_tail_profile ht ht1
        (physicalInvariantPart net t 2) (physicalInvariantPart net t 3)
        (physicalInvariantPart net t 4) (-1) 1 1 hD hI hJ
    · intro x z
      have hh := h x z
      rw [Fin.sum_univ_five] at hh
      simp only [hs,h1,h2,r.first_invariant,h4,hz15,hz24,hz34,hz35,hz44,hz45,
        zero_mul,zero_add,add_zero,one_mul,neg_one_mul] at hh
      linarith only [hh]
  · have h1 : net.w₃ 1 = 1 := by rw [r.first_exclusive,hs]; norm_num
    have h2 : net.w₃ 2 = 1 := by rw [r.second_exclusive,hs]; norm_num
    have h4 : net.w₃ 4 = -1 := by rw [r.second_invariant,hs]
    apply no_three_moving_shared_negative (featureSpace t)
      (net.W₂ 0 4) (net.W₂ 0 5) (net.W₂ 1 4) (net.W₂ 2 5)
      (physicalInvariantPart net t 0) (physicalInvariantPart net t 1)
      (physicalInvariantPart net t 2)
      (fun x => relu (physicalInvariantPart net t 3 x) -
        relu (physicalInvariantPart net t 4 x)) invariantTarget ha hc hd hQ hC hD
    · simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using star_tail_profile ht ht1
        (physicalInvariantPart net t 2) (physicalInvariantPart net t 3)
        (physicalInvariantPart net t 4) 1 1 (-1) hD hI hJ
    · intro x z
      have hh := h x z
      rw [Fin.sum_univ_five] at hh
      simp only [hs,h1,h2,r.first_invariant,h4,hz15,hz24,hz34,hz35,hz44,hz45,
        zero_mul,zero_add,add_zero,one_mul,neg_one_mul] at hh
      linarith only [hh]

/-- Every actual five-neuron star completion, including arbitrary biases, has
exactly two physical neurons receiving either translation feature. -/
theorem moving_union_card_eq_two (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    (moving (fun k => net.W₂ k 4) ∪ moving (fun k => net.W₂ k 5)).card = 2 := by
  classical
  let a : Fin 5 → ℝ := fun k => net.W₂ k 4
  let b : Fin 5 → ℝ := fun k => net.W₂ k 5
  have hid := physical_signed_carrier_identity_any_bias net t hW hmax
  have hf : ResidualFloorThree net.w₃ (physicalInvariantPart net t) invariantTarget := by
    intro S l hh
    exact physical_residual_card_ge_three net t ht ht1 S l hh
  obtain ⟨hlo,hhi⟩ := moving_union_card_two_or_three net.w₃ a b
    (physicalInvariantPart net t) invariantTarget hid hf
  by_contra hn
  have hu : (moving a ∪ moving b).card = 3 := by
    change (moving a ∪ moving b).card ≠ 2 at hn
    have hgt : 2 < (moving a ∪ moving b).card := lt_of_le_of_ne hlo (Ne.symm hn)
    linarith only [hgt,hhi]
  obtain ⟨ha,hb⟩ := union_three_forces_both_pairs net.w₃ a b
    (physicalInvariantPart net t) invariantTarget hid hf hu
  obtain ⟨hP,_,hout⟩ := physical_output_sign_counts net t ht ht1 hW hmax
  obtain ⟨_,_,htail⟩ := physical_recession_diagonal_extraction net t hW hmax
  have hPa := tail_positive_count net t ht ht1 a (stationary_card_of_pair a ha)
    (fun x => (htail x).1)
  have hPb := tail_positive_count net t ht ht1 b (stationary_card_of_pair b hb)
    (fun x => (htail x).2)
  have hcompl (v : Fin 5 → ℝ) : (moving v)ᶜ = stationary v := by
    ext k
    simp [moving,stationary]
  have hma : ((moving a).filter fun k => 0 < net.w₃ k).card = 1 := by
    have hh := one_positive_of_stationary_two (moving a) (outputSign net)
      (by simpa only [outputSign_true_iff] using hP)
      (by simpa only [hcompl,outputSign_true_iff] using hPa)
    simpa only [outputSign_true_iff] using hh
  have hmb : ((moving b).filter fun k => 0 < net.w₃ k).card = 1 := by
    have hh := one_positive_of_stationary_two (moving b) (outputSign net)
      (by simpa only [outputSign_true_iff] using hP)
      (by simpa only [hcompl,outputSign_true_iff] using hPb)
    simpa only [outputSign_true_iff] using hh
  obtain ⟨e,he⟩ := exists_canonicalSecond_roles net 4 5 hout ha hb hu hP hma hmb
  apply canonical_roles_impossible (canonicalSecond net e) t ht ht1
  · rw [(canonicalSecond_first net e).1,hW]
  · intro x
    rw [canonicalSecond_eval net e hout,hmax]
  · exact he

/-- The two actual carriers have opposite output signs. Every other original
physical neuron is stationary on both translation half-lines. -/
theorem exists_two_signed_physical_carriers (net : Network 4 6 5) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hW : net.W₁ = firstRows t) (hmax : ∀ x, net.eval x = Maximum 4 x) :
    ∃ p n : Fin 5, p ≠ n ∧ 0 < net.w₃ p ∧ net.w₃ n < 0 ∧
      ∀ k, k ≠ p → k ≠ n → net.W₂ k 4 = 0 ∧ net.W₂ k 5 = 0 := by
  classical
  obtain ⟨hplus,hminus,_⟩ := physical_recession_diagonal_extraction net t hW hmax
  obtain ⟨p,hpa,hp⟩ := exists_positive_passing_of_slope net.w₃ (fun j => net.W₂ j 4)
    (by rw [hplus]; norm_num)
  obtain ⟨n,hnb,hn⟩ := exists_negative_passing_of_slope net.w₃ (fun j => net.W₂ j 5)
    (by rw [hminus]; norm_num)
  have hpn : p ≠ n := by
    intro he
    rw [he] at hp
    linarith only [hp,hn]
  let U := moving (fun k => net.W₂ k 4) ∪ moving (fun k => net.W₂ k 5)
  have hsub : ({p,n} : Finset (Fin 5)) ⊆ U := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpa.ne'⟩)
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnb.ne'⟩)
  have hU : U = {p,n} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    have hpair : ({p,n} : Finset (Fin 5)).card = 2 := by simp [hpn]
    change U.card ≤ ({p,n} : Finset (Fin 5)).card
    rw [hpair]
    exact le_of_eq (moving_union_card_eq_two net t ht ht1 hW hmax)
  refine ⟨p,n,hpn,hp,hn,?_⟩
  intro k hkp hkn
  have hk : k ∉ U := by rw [hU]; simpa only [Finset.mem_insert,Finset.mem_singleton,
    not_or] using And.intro hkp hkn
  constructor
  · by_contra hh
    exact hk (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
  · by_contra hh
    exact hk (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))

#print axioms canonical_roles_impossible
#print axioms moving_union_card_eq_two
#print axioms exists_two_signed_physical_carriers
end MaxCaterpillar.Fiber.Count65.Star
