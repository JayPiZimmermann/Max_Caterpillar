import MaxCaterpillar.Fiber.Basic
import MaxCaterpillar.Fiber.Minimal63
import Mathlib.Topology.Algebra.Order.IntermediateValue

/-! # Continuous exact families and separation in a fixed paired slice

The disconnection result here is explicitly about the slice with fixed first
layer, fixed outer-comparison row, and fixed output weights. It is not a
component count for the full network fiber or its symmetry quotient.
-/

set_option autoImplicit false

namespace MaxCaterpillar
namespace Fiber

abbrev PairedBaseParameters := (Fin 6 → ℝ) × (Fin 6 → ℝ)

def PairedBaseExactSet : Set PairedBaseParameters :=
  {p | ∀ x, (pairedNet p.1 p.2).eval x = Maximum 4 x}

theorem continuous_pairedNet :
    Continuous (fun p : PairedBaseParameters => pairedNet p.1 p.2) := by
  apply (continuous_network_iff _).mpr
  refine ⟨continuous_const, continuous_const, ?_, continuous_const,
    continuous_const, continuous_const⟩
  apply continuous_pi
  intro k
  fin_cases k
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem continuous_pairedNet_of {X : Type*} [TopologicalSpace X]
    {g h : X → Fin 6 → ℝ} (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => pairedNet (g x) (h x)) :=
  continuous_pairedNet.comp (hg.prod_mk hh)

theorem continuous_signedSlackNet : Continuous signedSlackNet := by
  unfold signedSlackNet
  apply continuous_pairedNet_of continuous_const
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id.sub continuous_const
  · exact continuous_const

theorem continuous_splitNet : Continuous splitNet := by
  unfold splitNet
  apply continuous_pairedNet_of
  · exact continuous_pi fun j => continuous_const.add (continuous_apply j)
  · exact continuous_pi fun j => continuous_const.add (continuous_apply j)

theorem continuous_hybridNet :
    Continuous (fun p : ℝ × ℝ => hybridNet p.1 p.2) := by
  unfold hybridNet
  apply continuous_pairedNet_of
  · apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_fst.sub continuous_const
  · apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_snd
    · exact continuous_fst

/-- Every signed slack parameter continuously contracts to the ordinary signed
network while preserving all-input exactness. -/
theorem signedSlack_contraction_exact (c : ℝ) (hc : c ≤ 1) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, (signedSlackNet ((1 - t) * c)).eval x = Maximum 4 x := by
  apply signedSlackNet_eval
  rcases ht with ⟨ht0, ht1⟩
  nlinarith

/-- Removing a nonnegative common mode continuously preserves the exact function. -/
theorem split_contraction_exact (z : Fin 6 → ℝ) (hz : ∀ j, 0 ≤ z j) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, (splitNet (fun j => (1 - t) * z j)).eval x = Maximum 4 x := by
  apply splitNet_eval
  intro j
  exact mul_nonneg (sub_nonneg.mpr ht.2) (hz j)

/-- The hybrid family reaches its split boundary without leaving the exact fiber. -/
theorem hybrid_to_split_exact (ell μ : ℝ) (hell : 1 ≤ ell) (hμ : μ ≤ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, (hybridNet ell ((1 - t) * μ)).eval x = Maximum 4 x := by
  apply hybridNet_eval ell _ hell
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hμ

/-- Any continuous path confined to the specified paired slice cannot move from
the signed negative-base coefficient to a nonnegative one. -/
theorem no_paired_base_path (p : ℝ → PairedBaseParameters)
    (hp : ContinuousOn p (Set.Icc (0 : ℝ) 1))
    (he : ∀ t ∈ Set.Icc (0 : ℝ) 1, p t ∈ PairedBaseExactSet)
    (h0 : (p 0).2 1 = -1) (h1 : 0 ≤ (p 1).2 1) : False := by
  have hc : ContinuousOn (fun t => (p t).2 1) (Set.Icc (0 : ℝ) 1) :=
    (continuous_apply 1).comp_continuousOn hp.snd
  have hm : -(1 / 2 : ℝ) ∈ Set.Icc ((p 0).2 1) ((p 1).2 1) := by
    rw [h0]
    constructor <;> linarith
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc hm
  rcases pairedNet_negative_base_coefficient_gap (p t).1 (p t).2 (he t ht) with h | h
  · linarith
  · linarith

/-- The fixed paired coefficient slice is disconnected. Its relationship to the
full fiber requires the separate exhaustive normal-form theorem. -/
theorem not_isPreconnected_pairedBaseExactSet : ¬ IsPreconnected PairedBaseExactSet := by
  let s : PairedBaseParameters := ⟨![0, 1, 0, 0, 1, -1], ![0, -1, 0, 0, -1, 1]⟩
  let t : PairedBaseParameters := ⟨![0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]⟩
  have hs : s ∈ PairedBaseExactSet := by
    change ∀ x, (pairedNet _ _).eval x = Maximum 4 x
    simpa only [signedSlackNet, zero_sub] using signedSlackNet_eval 0 (by norm_num)
  have ht : t ∈ PairedBaseExactSet := by
    change ∀ x, (pairedNet _ _).eval x = Maximum 4 x
    simpa only [splitNet, Pi.zero_apply, add_zero] using
      splitNet_eval (0 : Fin 6 → ℝ) (fun _ => le_rfl)
  intro hconn
  have hc : Continuous (fun p : PairedBaseParameters => p.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have hm : -(1 / 2 : ℝ) ∈ Set.Icc (s.2 1) (t.2 1) := by
    change -(1 / 2 : ℝ) ∈ Set.Icc (-1) 0
    constructor <;> norm_num
  obtain ⟨p, hp, heq⟩ := hconn.intermediate_value hs ht hc.continuousOn hm
  rcases pairedNet_negative_base_coefficient_gap p.1 p.2 hp with h | h
  · linarith
  · linarith

end Fiber
end MaxCaterpillar
