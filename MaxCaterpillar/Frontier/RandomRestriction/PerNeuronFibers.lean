import Mathlib

/-! # Sum actual clean survival bounds over finite recording fibers

The recording map is a genuine function on a finite sample space. Its
fibers partition that sample space by an explicit equivalence. A clean
base point is chosen only in nonempty clean fibers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators

variable {Ω D : Type*} [Fintype Ω] [Fintype D] [DecidableEq D]

abbrev RecordedFiber (record : Ω → D) (u : D) := {ω : Ω // record ω = u}

def recordingEquiv (record : Ω → D) : Ω ≃ Σ u : D, RecordedFiber record u where
  toFun ω := ⟨record ω, ⟨ω, rfl⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨u, ω, hω⟩
    cases hω
    rfl

theorem sum_by_recording (record : Ω → D) (f : Ω → ℝ) :
    (∑ ω, f ω) = ∑ u : D, ∑ p : RecordedFiber record u, f p.val := by
  have hh := Equiv.sum_comp (recordingEquiv record)
    (fun p : Σ u : D, RecordedFiber record u => f p.2.val)
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma] at hh
  exact hh

noncomputable def cleanSurvivalSet (clean survive : Ω → Prop) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => clean ω ∧ survive ω

noncomputable def fiberSurvivalSet (record : Ω → D) (u : D) (survive : Ω → Prop) :
    Finset (RecordedFiber record u) := by
  classical
  exact Finset.univ.filter fun p => survive p.val

/-- Conditional bounds on every actual recording fiber imply a raw finite
sum bound after the clean event is discarded. The weight must genuinely
be constant on recording fibers, rather than assumed independent. -/
theorem clean_survival_card_le_sum (record : Ω → D) (clean survive : Ω → Prop)
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hconstant : ∀ p q, record p = record q → weight p = weight q)
    (hfiber : ∀ u : D, ∀ base : RecordedFiber record u, clean base.val →
      ((fiberSurvivalSet record u survive).card : ℝ) /
        (Fintype.card (RecordedFiber record u) : ℝ) ≤ weight base.val) :
    ((cleanSurvivalSet clean survive).card : ℝ) ≤ ∑ ω, weight ω := by
  classical
  have hlocal : ∀ u : D,
      (∑ p : RecordedFiber record u,
        if clean p.val ∧ survive p.val then (1 : ℝ) else 0) ≤
      ∑ p : RecordedFiber record u, weight p.val := by
    intro u
    by_cases hc : ∃ base : RecordedFiber record u, clean base.val
    · obtain ⟨base, hbase⟩ := hc
      have hcardpos : (0 : ℝ) < Fintype.card (RecordedFiber record u) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨base⟩
      have hh := (div_le_iff hcardpos).mp (hfiber u base hbase)
      have hsub : Finset.univ.filter (fun p : RecordedFiber record u => clean p.val ∧ survive p.val) ⊆
          fiberSurvivalSet record u survive := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.2⟩
      have hsum : (∑ p : RecordedFiber record u,
          if clean p.val ∧ survive p.val then (1 : ℝ) else 0) ≤
          ((fiberSurvivalSet record u survive).card : ℝ) := by
        rw [Finset.sum_boole]
        exact_mod_cast Finset.card_le_of_subset hsub
      have hsame : ∀ p : RecordedFiber record u, weight p.val = weight base.val := by
        intro p
        exact hconstant p.val base.val (p.property.trans base.property.symm)
      calc
        _ ≤ _ := hsum
        _ ≤ weight base.val * Fintype.card (RecordedFiber record u) := hh
        _ = _ := by simp only [hsame, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
    · have hn : ∀ p : RecordedFiber record u, ¬ clean p.val := by
        intro p hp
        exact hc ⟨p, hp⟩
      simp only [hn, false_and, if_false, Finset.sum_const_zero]
      exact Finset.sum_nonneg fun p _ => hweight p.val
  rw [cleanSurvivalSet, Finset.natCast_card_filter,
    sum_by_recording record (fun ω => if clean ω ∧ survive ω then (1 : ℝ) else 0),
    sum_by_recording record weight]
  exact Finset.sum_le_sum fun u _ => hlocal u

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
