import MaxCaterpillar.Fiber.Mixed65.MinimalExtraction

/-! # Two or three moving physical gates before the geometric role-swap step

A residual floor of three is used only as a genuine lower bound for arbitrary
feature-linear remainders. The signed-carrier identity itself supplies all
carrier supports and their feature-linear contribution at translation zero.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.PhysicalExtraction
open BigOperators MaxCaterpillar.Frontier
open MaxCaterpillar.Fiber.Mixed65

noncomputable def moving (a : Fin 5 → ℝ) : Finset (Fin 5) :=
  Finset.univ.filter fun i => a i ≠ 0

noncomputable def stationary (a : Fin 5 → ℝ) : Finset (Fin 5) :=
  Finset.univ.filter fun i => a i = 0

/-- The residual lower-bound interface, with arbitrary coefficient remainder. -/
def ResidualFloorThree {α : Type*} (d : Fin 5 → ℝ)
    (C : Fin 5 → α → ℝ) (H : α → ℝ) : Prop :=
  ∀ (S : Finset (Fin 5)) (l : Fin 5 → ℝ),
    (∀ x, H x = (∑ i, l i * C i x) + ∑ i in S, d i * relu (C i x)) →
      3 ≤ S.card

private lemma stationary_add_moving (a : Fin 5 → ℝ) :
    (stationary a).card + (moving a).card = 5 := by
  classical
  simpa only [stationary, moving, Finset.card_univ, Fintype.card_fin] using
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 5))) (fun i => a i = 0)

private lemma moving_sum_linear {α : Type*} (d a : Fin 5 → ℝ)
    (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (hz : ∀ x, (∑ i, d i * relu (C i x)) = H x)
    (htail : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in stationary a, d i * relu (C i x)) :
    ∀ x, (∑ i in moving a, d i * relu (C i x)) =
      ∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x := by
  classical
  intro x
  have he := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 5)) (fun i => a i = 0)
    (fun i => d i * relu (C i x))
  change (∑ i in stationary a, d i * relu (C i x)) +
    (∑ i in moving a, d i * relu (C i x)) = ∑ i, d i * relu (C i x) at he
  linarith only [he, hz x, htail x]

private theorem disjoint_two_moving_impossible {α : Type*}
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (hz : ∀ x, (∑ i, d i * relu (C i x)) = H x)
    (hta : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in stationary a, d i * relu (C i x))
    (htb : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * C i x) +
        ∑ i in stationary b, d i * relu (C i x))
    (hfloor : ResidualFloorThree d C H)
    (ha : (moving a).card = 2) (hb : (moving b).Nonempty)
    (hab : Disjoint (moving a) (moving b)) : False := by
  classical
  have hsub : moving a ⊆ stationary b := by
    intro i hi
    have hbzero : b i = 0 := by
      by_contra hne
      exact Finset.disjoint_left.mp hab hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbzero⟩
  let S := stationary b \ moving a
  have hlin := moving_sum_linear d a C H hz hta
  have hrepr : ∀ x, H x =
      (∑ i, ((if 0 < a i then d i else 0) +
        (if 0 < b i then d i else 0)) * C i x) +
        ∑ i in S, d i * relu (C i x) := by
    intro x
    have hsum := Finset.sum_sdiff (f := fun i => d i * relu (C i x)) hsub
    have hc : (∑ i : Fin 5, ((if 0 < a i then d i else 0) +
          (if 0 < b i then d i else 0)) * C i x) =
        (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
          (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * C i x) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_filter]
    rw [hc]
    change (∑ i in S, d i * relu (C i x)) +
      (∑ i in moving a, d i * relu (C i x)) =
      ∑ i in stationary b, d i * relu (C i x) at hsum
    linarith only [htb x, hsum, hlin x]
  have hS := hfloor S _ hrepr
  have hcS := Finset.card_sdiff_add_card_eq_card hsub
  have hcb := stationary_add_moving b
  have hBpos : 1 ≤ (moving b).card := Finset.card_pos.mpr hb
  change S.card + (moving a).card = (stationary b).card at hcS
  rw [ha] at hcS
  linarith only [hS, hcS, hcb, hBpos]

/-- Before any geometric classification, at most three physical gates can
carry either translation half-line. At least two do carry it. -/
theorem moving_union_card_two_or_three {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) =
      z + H x) (hfloor : ResidualFloorThree d C H) :
    2 ≤ (moving a ∪ moving b).card ∧ (moving a ∪ moving b).card ≤ 3 := by
  classical
  obtain ⟨hsa, hsb, htail⟩ := finite_signed_carrier_extraction d a b C H h
  have hz : ∀ x, (∑ i, d i * relu (C i x)) = H x := by
    intro x
    simpa only [show relu (0 : ℝ) = 0 from max_self 0,
      neg_zero, mul_zero, zero_add] using h x 0
  have hta : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in stationary a, d i * relu (C i x) := fun x => (htail x).1
  have htb : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * C i x) +
        ∑ i in stationary b, d i * relu (C i x) := fun x => (htail x).2
  have hZa : 3 ≤ (stationary a).card := by
    apply hfloor (stationary a) (fun i => if 0 < a i then d i else 0)
    intro x
    convert hta x using 1
    congr 1
    simp only [Finset.sum_filter, ite_mul, zero_mul]
  have hZb : 3 ≤ (stationary b).card := by
    apply hfloor (stationary b) (fun i => if 0 < b i then d i else 0)
    intro x
    convert htb x using 1
    congr 1
    simp only [Finset.sum_filter, ite_mul, zero_mul]
  have hCa := stationary_add_moving a
  have hCb := stationary_add_moving b
  have hA : (moving a).card ≤ 2 := by linarith only [hZa, hCa]
  have hB : (moving b).card ≤ 2 := by linarith only [hZb, hCb]
  obtain ⟨i, hai, hdi⟩ := exists_positive_passing_of_slope d a
    (by rw [hsa]; norm_num)
  obtain ⟨j, hbj, hdj⟩ := exists_negative_passing_of_slope d b
    (by rw [hsb]; norm_num)
  have hi : i ∈ moving a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai.ne'⟩
  have hj : j ∈ moving b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbj.ne'⟩
  have hij : i ≠ j := by intro he; subst j; linarith only [hdi, hdj]
  constructor
  · apply Finset.one_lt_card.mpr
    exact ⟨i, Finset.mem_union_left _ hi, j, Finset.mem_union_right _ hj, hij⟩
  · by_cases hd : Disjoint (moving a) (moving b)
    · have haNot : (moving a).card ≠ 2 := by
        intro he
        exact disjoint_two_moving_impossible d a b C H hz hta htb hfloor
          he ⟨j, hj⟩ hd
      have hbNot : (moving b).card ≠ 2 := by
        intro he
        exact disjoint_two_moving_impossible d b a C H hz htb hta hfloor
          he ⟨i, hi⟩ hd.symm
      have ha1 : (moving a).card ≤ 1 := Nat.le_of_lt_succ (lt_of_le_of_ne hA haNot)
      have hb1 : (moving b).card ≤ 1 := Nat.le_of_lt_succ (lt_of_le_of_ne hB hbNot)
      rw [Finset.card_union_eq hd]
      linarith only [ha1, hb1]
    · have hI : 1 ≤ (moving a ∩ moving b).card := by
        apply Finset.card_pos.mpr
        exact Finset.not_disjoint_iff_nonempty_inter.mp hd
      have hc := Finset.card_union_add_card_inter (moving a) (moving b)
      linarith only [hc, hA, hB, hI]

/-- The two tail floors, before any finite reindexing. -/
theorem stationary_cards_of_floor {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) =
      z + H x) (hfloor : ResidualFloorThree d C H) :
    3 ≤ (stationary a).card ∧ 3 ≤ (stationary b).card := by
  classical
  obtain ⟨_,_,htail⟩ := finite_signed_carrier_extraction d a b C H h
  constructor
  · apply hfloor (stationary a) (fun i => if 0 < a i then d i else 0)
    intro x
    convert (htail x).1 using 1
    congr 1
    simp only [Finset.sum_filter, ite_mul, zero_mul]
  · apply hfloor (stationary b) (fun i => if 0 < b i then d i else 0)
    intro x
    convert (htail x).2 using 1
    congr 1
    simp only [Finset.sum_filter, ite_mul, zero_mul]

/-- A three-neuron carrier union necessarily consists of two overlapping
pairs. This supplies the premises of the finite carrier-role classifier. -/
theorem union_three_forces_both_pairs {α : Type*} [Nonempty α]
    (d a b : Fin 5 → ℝ) (C : Fin 5 → α → ℝ) (H : α → ℝ)
    (h : ∀ x z, (∑ i, d i * relu (a i * relu z + b i * relu (-z) + C i x)) =
      z + H x) (hfloor : ResidualFloorThree d C H)
    (hthree : (moving a ∪ moving b).card = 3) :
    (moving a).card = 2 ∧ (moving b).card = 2 := by
  classical
  obtain ⟨hza,hzb⟩ := stationary_cards_of_floor d a b C H h hfloor
  have hca := stationary_add_moving a
  have hcb := stationary_add_moving b
  have hA : (moving a).card ≤ 2 := by linarith only [hza,hca]
  have hB : (moving b).card ≤ 2 := by linarith only [hzb,hcb]
  obtain ⟨hsa,hsb,htail⟩ := finite_signed_carrier_extraction d a b C H h
  obtain ⟨i,hai,_⟩ := exists_positive_passing_of_slope d a
    (by rw [hsa]; norm_num)
  obtain ⟨j,hbj,_⟩ := exists_negative_passing_of_slope d b
    (by rw [hsb]; norm_num)
  have hi : i ∈ moving a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hai.ne'⟩
  have hj : j ∈ moving b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbj.ne'⟩
  have hz : ∀ x, (∑ i, d i * relu (C i x)) = H x := by
    intro x
    simpa only [neg_zero, show relu (0 : ℝ) = 0 from max_self 0,
      mul_zero, zero_add] using h x 0
  have hta : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < a i), d i * C i x) +
        ∑ i in stationary a, d i * relu (C i x) := fun x => (htail x).1
  have htb : ∀ x, H x =
      (∑ i in Finset.univ.filter (fun i => 0 < b i), d i * C i x) +
        ∑ i in stationary b, d i * relu (C i x) := fun x => (htail x).2
  have hn : ¬ Disjoint (moving a) (moving b) := by
    intro hd
    have haNot : (moving a).card ≠ 2 := by
      intro he
      exact disjoint_two_moving_impossible d a b C H hz hta htb hfloor
        he ⟨j,hj⟩ hd
    have hbNot : (moving b).card ≠ 2 := by
      intro he
      exact disjoint_two_moving_impossible d b a C H hz htb hta hfloor
        he ⟨i,hi⟩ hd.symm
    have ha1 : (moving a).card ≤ 1 := Nat.le_of_lt_succ (lt_of_le_of_ne hA haNot)
    have hb1 : (moving b).card ≤ 1 := Nat.le_of_lt_succ (lt_of_le_of_ne hB hbNot)
    rw [Finset.card_union_eq hd] at hthree
    linarith only [ha1,hb1,hthree]
  have hI : 1 ≤ (moving a ∩ moving b).card :=
    Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hn)
  have hc := Finset.card_union_add_card_inter (moving a) (moving b)
  constructor <;> linarith only [hA,hB,hI,hc,hthree]

#check @union_three_forces_both_pairs
#print axioms union_three_forces_both_pairs
end MaxCaterpillar.Fiber.Count65.PhysicalExtraction
