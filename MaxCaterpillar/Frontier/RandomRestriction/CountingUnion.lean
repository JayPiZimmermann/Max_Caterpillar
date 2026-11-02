import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Finite event counting after three bad-event exclusions

The assumptions are cardinal bounds for explicit finite events and an actual
cover of the entire sample space. No probability space, independence, or
network counting prerequisite is assumed. The neuron index may be empty.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.CountingUnion
open BigOperators

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype κ]

/-- A cover by three exceptional events and finitely many neuron events gives
an ordinary sum-of-cardinalities upper bound for the whole sample space. -/
theorem card_le_bad_add_event_sum (B₁ B₂ B₃ : Finset Ω) (E : κ → Finset Ω)
    (hcover : (Finset.univ : Finset Ω) ⊆
      B₁ ∪ B₂ ∪ B₃ ∪ Finset.univ.biUnion E) :
    Fintype.card Ω ≤ B₁.card + B₂.card + B₃.card + ∑ k, (E k).card := by
  calc
    Fintype.card Ω = (Finset.univ : Finset Ω).card := Finset.card_univ.symm
    _ ≤ (B₁ ∪ B₂ ∪ B₃ ∪ Finset.univ.biUnion E).card :=
      Finset.card_le_of_subset hcover
    _ ≤ (B₁ ∪ B₂ ∪ B₃).card + (Finset.univ.biUnion E).card :=
      Finset.card_union_le _ _
    _ ≤ ((B₁ ∪ B₂).card + B₃.card) + ∑ k, (E k).card :=
      add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
    _ ≤ B₁.card + B₂.card + B₃.card + ∑ k, (E k).card :=
      add_le_add_right (add_le_add_right (Finset.card_union_le _ _) _) _

/-- Three bad-event fractions at most 1/4, 2/25, and 1/4 leave at least
42/100 of the sample space covered by neuron events, counting overlaps. -/
theorem event_sum_ge_forty_two_percent (B₁ B₂ B₃ : Finset Ω) (E : κ → Finset Ω)
    (hcover : (Finset.univ : Finset Ω) ⊆
      B₁ ∪ B₂ ∪ B₃ ∪ Finset.univ.biUnion E)
    (hB₁ : 4 * (B₁.card : ℝ) ≤ (Fintype.card Ω : ℝ))
    (hB₂ : 25 * (B₂.card : ℝ) ≤ 2 * (Fintype.card Ω : ℝ))
    (hB₃ : 4 * (B₃.card : ℝ) ≤ (Fintype.card Ω : ℝ)) :
    (42 / 100 : ℝ) * (Fintype.card Ω : ℝ) ≤ ∑ k, ((E k).card : ℝ) := by
  have hc : (Fintype.card Ω : ℝ) ≤
      (B₁.card : ℝ) + (B₂.card : ℝ) + (B₃.card : ℝ) +
        ∑ k, ((E k).card : ℝ) := by
    exact_mod_cast card_le_bad_add_event_sum B₁ B₂ B₃ E hcover
  linarith only [hc,hB₁,hB₂,hB₃]

/-- Cardinal event bounds yield the final neuron count. Sign assumptions on
K and D are unnecessary: the squared scale is nonnegative automatically.
Nonemptiness of the actual sample space is the only cancellation hypothesis. -/
theorem counting_union_lower_bound [Nonempty Ω]
    (B₁ B₂ B₃ : Finset Ω) (E : κ → Finset Ω) (K D : ℝ)
    (hcover : (Finset.univ : Finset Ω) ⊆
      B₁ ∪ B₂ ∪ B₃ ∪ Finset.univ.biUnion E)
    (hB₁ : 4 * (B₁.card : ℝ) ≤ (Fintype.card Ω : ℝ))
    (hB₂ : 25 * (B₂.card : ℝ) ≤ 2 * (Fintype.card Ω : ℝ))
    (hB₃ : 4 * (B₃.card : ℝ) ≤ (Fintype.card Ω : ℝ))
    (hE : ∀ k, K ^ 2 * ((E k).card : ℝ) ≤ D * (Fintype.card Ω : ℝ)) :
    (42 / 100 : ℝ) * K ^ 2 ≤ D * (Fintype.card κ : ℝ) := by
  have hsurvive := event_sum_ge_forty_two_percent B₁ B₂ B₃ E hcover hB₁ hB₂ hB₃
  have hsum : K ^ 2 * (∑ k, ((E k).card : ℝ)) ≤
      (Fintype.card κ : ℝ) * (D * (Fintype.card Ω : ℝ)) := by
    calc
      _ = ∑ k, K ^ 2 * ((E k).card : ℝ) := Finset.mul_sum
      _ ≤ ∑ _k : κ, D * (Fintype.card Ω : ℝ) :=
        Finset.sum_le_sum (fun k _ => hE k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left hsurvive (sq_nonneg K)
  have hΩ : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card Ω)
  apply (mul_le_mul_right hΩ).mp
  calc
    (42 / 100 : ℝ) * K ^ 2 * (Fintype.card Ω : ℝ) =
        K ^ 2 * ((42 / 100 : ℝ) * (Fintype.card Ω : ℝ)) := by ring
    _ ≤ K ^ 2 * (∑ k, ((E k).card : ℝ)) := hmul
    _ ≤ (Fintype.card κ : ℝ) * (D * (Fintype.card Ω : ℝ)) := hsum
    _ = D * (Fintype.card κ : ℝ) * (Fintype.card Ω : ℝ) := by ring

end MaxCaterpillar.Frontier.RandomRestriction.CountingUnion
