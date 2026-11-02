import MaxCaterpillar.Fiber.Count65.ForkExclusion.Defs

/-! # Five facet roles force three positive gates

This is finite incidence algebra for actual coefficient vectors. A single
preactivation cannot carry two distinct planes in one strict feature cell.
-/
set_option autoImplicit false

namespace MaxCaterpillar.Fiber.Count65.ForkExclusion
open BigOperators

lemma InnerU.not_innerV {α β κ : ℝ} {d : Coeff} (hαβ : α+β=1)
    (hu : InnerU α β κ d) : ¬ InnerV α β κ d := by
  intro hv
  apply hu.2.2
  linear_combination hu.2.1 - hv.1 - d.r * hαβ

lemma OuterU.not_innerV {α β κ : ℝ} {d : Coeff}
    (ho : OuterU κ d) : ¬ InnerV α β κ d := by
  intro hi
  apply ho.2.2
  have hz := hi.1
  rw [ho.1, mul_zero, sub_zero] at hz
  exact hz

lemma OuterV.not_innerU {α β κ : ℝ} {d : Coeff}
    (ho : OuterV κ d) : ¬ InnerU α β κ d := by
  intro hi
  apply ho.2.2
  have hz := hi.1
  rw [ho.1, mul_zero, sub_zero] at hz
  exact hz

lemma OuterU.not_middle {κ : ℝ} {d : Coeff} (ho : OuterU κ d) : ¬ Middle d := by
  intro hm
  apply ho.2.2
  have hz := ho.2.1
  rw [hm.1, mul_zero, add_zero] at hz
  exact hz

lemma OuterV.not_middle {κ : ℝ} {d : Coeff} (ho : OuterV κ d) : ¬ Middle d := by
  intro hm
  apply ho.2.2
  have hz := ho.2.1
  rw [hm.1, mul_zero, add_zero] at hz
  exact hz

structure ForcedRoles {ι : Type*} (d : ResidualSystem ι) (α β κ : ℝ) : Prop where
  outerU : ∃ i, 0 < d.out i ∧ OuterU κ (d.gate i)
  outerV : ∃ i, 0 < d.out i ∧ OuterV κ (d.gate i)
  innerU : ∃ i, 0 < d.out i ∧ InnerU α β κ (d.gate i)
  innerV : ∃ i, 0 < d.out i ∧ InnerV α β κ (d.gate i)
  middle : ∃ i, 0 < d.out i ∧ Middle (d.gate i)

/-- Five target facets cannot be supplied by just two positive gates. -/
theorem three_positive_of_forced_roles {ι : Type*} (d : ResidualSystem ι)
    {α β κ : ℝ} (hαβ : α+β=1) (h : ForcedRoles d α β κ) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      0 < d.out i ∧ 0 < d.out j ∧ 0 < d.out k := by
  classical
  obtain ⟨i, hi, hIu⟩ := h.innerU
  obtain ⟨j, hj, hIv⟩ := h.innerV
  have hij : i ≠ j := by
    intro he
    subst j
    exact hIu.not_innerV hαβ hIv
  obtain ⟨e, he, hOu⟩ := h.outerU
  by_cases hei : e = i
  · subst e
    obtain ⟨f, hf, hOv⟩ := h.outerV
    by_cases hfj : f = j
    · subst f
      obtain ⟨k, hk, hM⟩ := h.middle
      refine ⟨i,j,k,hij,?_,?_,hi,hj,hk⟩
      · intro he
        subst k
        exact hOu.not_middle hM
      · intro he
        subst k
        exact hOv.not_middle hM
    · refine ⟨i,j,f,hij,?_,Ne.symm hfj,hi,hj,hf⟩
      intro he
      subst f
      exact hOv.not_innerU hIu
  · refine ⟨i,j,e,hij,Ne.symm hei,?_,hi,hj,he⟩
    intro heq
    subst e
    exact hOu.not_innerV hIv

/-- The additional negative crease makes four distinct physical residual gates. -/
theorem card_ge_four_of_roles_and_negative {ι : Type*} [Fintype ι]
    (d : ResidualSystem ι) {α β κ : ℝ} (hαβ : α+β=1)
    (h : ForcedRoles d α β κ) (hn : ∃ l, d.out l < 0) :
    4 ≤ Fintype.card ι := by
  classical
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := three_positive_of_forced_roles d hαβ h
  obtain ⟨l,hl⟩ := hn
  have hil : i ≠ l := by intro he; subst l; linarith only [hi,hl]
  have hjl : j ≠ l := by intro he; subst l; linarith only [hj,hl]
  have hkl : k ≠ l := by intro he; subst l; linarith only [hk,hl]
  have hc : ({i,j,k,l} : Finset ι).card = 4 := by
    simp [hij,hik,hjk,hil,hjl,hkl]
  have hle := Finset.card_le_of_subset (Finset.subset_univ ({i,j,k,l} : Finset ι))
  simpa only [hc,Finset.card_univ] using hle

#print axioms three_positive_of_forced_roles
#print axioms card_ge_four_of_roles_and_negative
end MaxCaterpillar.Fiber.Count65.ForkExclusion
