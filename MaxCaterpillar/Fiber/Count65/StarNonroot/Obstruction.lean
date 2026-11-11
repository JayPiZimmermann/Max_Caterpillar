import MaxCaterpillar.Fiber.Count65.StarNonroot.Spurious

/-! # Four residual gates are necessary for a genuine star nonroot

Three different positive carriers and one negative carrier are forced directly
from the all-input residual identity. The gates are not assumed to have a
particular output sign or normal form.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.StarNonroot
open BigOperators MaxCaterpillar.Frontier

private theorem card_ge_four_of_three_positive_and_negative {ι : Type*} [Fintype ι]
    (out : ι → ℝ)
    (hp : ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ 0 < out i ∧ 0 < out j ∧ 0 < out k)
    (hn : ∃ l, out l < 0) : 4 ≤ Fintype.card ι := by
  classical
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := hp
  obtain ⟨l,hl⟩ := hn
  have hil : i ≠ l := by intro he; subst l; linarith only [hi,hl]
  have hjl : j ≠ l := by intro he; subst l; linarith only [hj,hl]
  have hkl : k ≠ l := by intro he; subst l; linarith only [hk,hl]
  have hc : ({i,j,k,l} : Finset ι).card = 4 := by simp [hij,hik,hjk,hil,hjl,hkl]
  have hle := Finset.card_le_of_subset (Finset.subset_univ ({i,j,k,l} : Finset ι))
  simpa only [hc,Finset.card_univ] using hle

/-- With one negative nonroot coefficient, the three target facets have distinct carriers. -/
theorem ResidualSystem.three_positive_one_negative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0)
    (ha : 0<a) (hb : 0<b) (hc : c<0) (h : d.Represents a b c) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < d.out i ∧ 0 < d.out j ∧ 0 < d.out k := by
  obtain ⟨i,hi,hui,hvi,_⟩ := d.external_carrier12 a b c habc hc h
  obtain ⟨j,hj,huj,hwj,hvj⟩ := d.swap23.interior_carrier12_inactive a c b
    (by linarith only [habc]) hb (d.represents_swap23 a b c h)
  obtain ⟨k,hk,hwk,hvk,huk⟩ := d.swap13.interior_carrier12_inactive c b a
    (by linarith only [habc]) ha (d.represents_swap13 a b c h)
  dsimp only [ResidualSystem.swap23] at hj huj hwj hvj
  dsimp only [ResidualSystem.swap13] at hk hwk hvk huk
  refine ⟨i,j,k,?_,?_,?_,hi,hj,hk⟩
  · intro he
    subst j
    apply hui
    linarith only [hvi,hvj]
  · intro he
    subst k
    exact hui huk
  · intro he
    subst k
    exact huj huk

/-- With two negative coefficients, either the exterior carriers differ, or
that common carrier leaves two different positive-cell facets uncovered. -/
theorem ResidualSystem.three_positive_two_negative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0)
    (ha : 0<a) (hb : b<0) (hc : c<0) (h : d.Represents a b c) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < d.out i ∧ 0 < d.out j ∧ 0 < d.out k := by
  classical
  obtain ⟨i,hi,hui,hvi,hti⟩ := d.external_carrier12 a b c habc hc h
  obtain ⟨j,hj,huj,hwi,htj⟩ := d.swap23.external_carrier12 a c b
    (by linarith only [habc]) hb (d.represents_swap23 a b c h)
  dsimp only [ResidualSystem.swap23] at hj huj hwi htj
  by_cases hij : i=j
  · subst j
    obtain ⟨j,hj,huj,hvj,hwj⟩ := d.interior_carrier12_active a b c habc hc h
    obtain ⟨k,hk,huk,hwk,hvk⟩ := d.swap23.interior_carrier12_active a c b
      (by linarith only [habc]) hb (d.represents_swap23 a b c h)
    dsimp only [ResidualSystem.swap23] at hk huk hwk hvk
    refine ⟨i,j,k,?_,?_,?_,hi,hj,hk⟩
    · intro he
      subst j
      rw [hti,zero_mul,add_zero] at hwj
      apply hui
      linarith only [hwj,hwi]
    · intro he
      subst k
      rw [hti,zero_mul,add_zero] at hvk
      apply hui
      linarith only [hvk,hvi]
    · intro he
      subst k
      apply huj
      linarith only [hvj,hvk]
  · obtain ⟨k,hk,hwk,hvk,huk⟩ := d.swap13.interior_carrier12_inactive c b a
      (by linarith only [habc]) ha (d.represents_swap13 a b c h)
    dsimp only [ResidualSystem.swap13] at hk hwk hvk huk
    refine ⟨i,j,k,hij,?_,?_,hi,hj,hk⟩
    · intro he
      subst k
      exact hui huk
    · intro he
      subst k
      exact huj huk

theorem ResidualSystem.card_ge_four_one_negative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0)
    (ha : 0<a) (hb : 0<b) (hc : c<0) (h : d.Represents a b c) :
    4 ≤ Fintype.card ι :=
  card_ge_four_of_three_positive_and_negative d.out
    (d.three_positive_one_negative a b c habc ha hb hc h)
    (d.exists_negative_gate a b c habc hc h)

theorem ResidualSystem.card_ge_four_two_negative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0)
    (ha : 0<a) (hb : b<0) (hc : c<0) (h : d.Represents a b c) :
    4 ≤ Fintype.card ι :=
  card_ge_four_of_three_positive_and_negative d.out
    (d.three_positive_two_negative a b c habc ha hb hc h)
    (d.exists_negative_gate a b c habc hc h)

/-- The complete arbitrary-real residual obstruction, including all six
nondegenerate zero-sum sign patterns. -/
theorem ResidualSystem.card_ge_four {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) (a b c : ℝ) (habc : a+b+c=0)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (h : d.Represents a b c) :
    4 ≤ Fintype.card ι := by
  rcases lt_or_gt_of_ne ha with han | hap
  · rcases lt_or_gt_of_ne hb with hbn | hbp
    · have hcp : 0<c := by linarith only [habc,han,hbn]
      exact d.swap13.card_ge_four_two_negative c b a
        (by linarith only [habc]) hcp hbn han (d.represents_swap13 a b c h)
    · rcases lt_or_gt_of_ne hc with hcn | hcp
      · exact d.swap12.card_ge_four_two_negative b a c
          (by linarith only [habc]) hbp han hcn (d.represents_swap12 a b c h)
      · exact d.swap13.card_ge_four_one_negative c b a
          (by linarith only [habc]) hcp hbp han (d.represents_swap13 a b c h)
  · rcases lt_or_gt_of_ne hb with hbn | hbp
    · rcases lt_or_gt_of_ne hc with hcn | hcp
      · exact d.card_ge_four_two_negative a b c habc hap hbn hcn h
      · exact d.swap23.card_ge_four_one_negative a c b
          (by linarith only [habc]) hap hcp hbn (d.represents_swap23 a b c h)
    · have hcn : c<0 := by linarith only [habc,hap,hbp]
      exact d.card_ge_four_one_negative a b c habc hap hbp hcn h

end MaxCaterpillar.Fiber.Count65.StarNonroot
