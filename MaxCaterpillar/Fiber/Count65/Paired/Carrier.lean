import MaxCaterpillar.Fiber.Count65.Paired.Recession

/-! # The actual unique recession carrier is globally nonnegative

This is extracted from an arbitrary domain representation, before introducing
any assumed carrier/comparison normal form. Four effective atoms at width five
leave exactly one positive-common-slope neuron, whose positive output sign and
nonnegative preactivation are forced by the full input identity.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MaxCaterpillar.Fiber.Count65.Paired
open BigOperators Frontier
variable {m : ℕ}

/-- The recession equality can be evaluated at every point of the closed
increment quadrant, including its boundary. -/
theorem recession_at_quadrant_point (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0≤q → 0≤r →
      max (a+q) (b+r)=∑ k, d k*relu (C k+α k*q+β k*r))
    (q r : ℝ) (hq : 0≤q) (hr : 0≤r) :
    max (a+q) (b+r)=∑ k, d k*pick (α k+β k)
      (C k+α k*q+β k*r) (relu (C k+α k*q+β k*r)) := by
  have hh : ∀ s t : ℝ, 0≤s → 0≤t →
      max ((a+q)+s) ((b+r)+t)=∑ k, d k*
        relu ((C k+α k*q+β k*r)+α k*s+β k*t) := by
    intro s t hs ht
    have hp := h (q+s) (r+t) (add_nonneg hq hs) (add_nonneg hr ht)
    calc
      max ((a+q)+s) ((b+r)+t) = max (a+(q+s)) (b+(r+t)) := by congr 1 <;> ring
      _ = ∑ k, d k*relu (C k+α k*(q+s)+β k*(r+t)) := hp
      _ = ∑ k, d k*relu ((C k+α k*q+β k*r)+α k*s+β k*t) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 2
        ring
  simpa only [zero_mul,add_zero] using
    two_increment_recession (a+q) (b+r) d
      (fun k => C k+α k*q+β k*r) α β hh 0

/-- With all other common slopes zero, the unique carrier has positive
output coefficient and nonnegative actual preactivation everywhere. -/
theorem unique_carrier_positive (a b : ℝ) (d C α β : Fin m → ℝ)
    (h : ∀ q r : ℝ, 0≤q → 0≤r →
      max (a+q) (b+r)=∑ k, d k*relu (C k+α k*q+β k*r))
    (k : Fin m) (hk : 0<α k+β k)
    (hrest : ∀ i, i≠k → α i+β i=0) :
    0<d k ∧ ∀ q r : ℝ, 0≤q → 0≤r → 0≤C k+α k*q+β k*r := by
  have hs := common_increment_slope a b d C α β h
  have hsum : (∑ i, d i*relu (α i+β i))=d k*(α k+β k) := by
    rw [Finset.sum_eq_single k]
    · rw [relu_of_nonneg hk.le]
    · intro i _ hik
      simp [hrest i hik,relu]
    · simp
  rw [hsum] at hs
  have hd : 0<d k := by nlinarith only [hs,hk]
  refine ⟨hd,?_⟩
  intro q r hq hr
  have hh := recession_at_quadrant_point a b d C α β h q r hq hr
  have hz : (∑ i, d i*pick (α i+β i) (C i+α i*q+β i*r)
      (relu (C i+α i*q+β i*r)))-
      (∑ i, d i*relu (C i+α i*q+β i*r))=0 := by
    rw [← hh,← h q r hq hr]
    ring
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k] at hz
  · simp only [pick,if_pos hk] at hz
    have he : C k+α k*q+β k*r=relu (C k+α k*q+β k*r) := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show d k*((C k+α k*q+β k*r)-
        relu (C k+α k*q+β k*r))=0 by nlinarith only [hz])).resolve_left
      exact ne_of_gt hd
    rw [he]
    exact relu_nonneg _
  · intro i _ hik
    simp [hrest i hik,pick]
  · simp

/-- Four effective atoms leave precisely one physical carrier slot. In
particular no initial deletion of zero-output neurons is needed. -/
theorem four_atoms_force_unique_carrier (a b : ℝ) (d C α β : Fin 5 → ℝ)
    (h : ∀ q r : ℝ, 0≤q → 0≤r →
      max (a+q) (b+r)=∑ k, d k*relu (C k+α k*q+β k*r))
    (hfour : (activeAtoms d α β).card=4) :
    ∃ k, 0<α k+β k ∧ 0<d k ∧
      (∀ i, i≠k → α i+β i=0 ∧ α i≠0 ∧ d i≠0) ∧
      (∀ q r : ℝ, 0≤q → 0≤r → 0≤C k+α k*q+β k*r) := by
  obtain ⟨k,hk⟩ := exists_positive_common_slope a b d C α β h
  have hsub : activeAtoms d α β ⊆ Finset.univ.erase k := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro hik
    subst i
    have hi0 := (Finset.mem_filter.mp hi).2.1
    linarith only [hi0,hk]
  have he : activeAtoms d α β=Finset.univ.erase k :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin,hfour])
  have hall : ∀ i, i≠k → α i+β i=0 ∧ α i≠0 ∧ d i≠0 := by
    intro i hik
    have hi : i∈activeAtoms d α β := by rw [he]; simp [hik]
    exact (Finset.mem_filter.mp hi).2
  have hpos := unique_carrier_positive a b d C α β h k hk
    (fun i hi => (hall i hi).1)
  exact ⟨k,hk,hpos.1,hall,hpos.2⟩

end MaxCaterpillar.Fiber.Count65.Paired
