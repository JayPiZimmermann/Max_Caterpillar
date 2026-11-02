import MaxCaterpillar.Frontier.RandomRestriction.Configurations
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.NetworkRealization

/-! # One actual gap scale for the complete three-permutation experiment -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators Configurations DominantGap

variable {m h₁ h₂ : ℕ}

/-- Genericity at the same actual point, for every fixed full-coordinate
enumeration and every independent tail/rank permutation. -/
def UniformGapScale (net : NormalizedNetwork (m + 5) h₁ h₂) (T : ℝ) : Prop :=
  ∀ σ : FullPerm m, ∀ τ : TailPerm m, ∀ ρ : RankPerm m,
    GenericNetworkPoint net (baseTail σ) (τ, ρ) T

/-- Simultaneous actual tail negativity already forces the common scale
to be positive: place exponent one at the very first gap. -/
theorem uniform_gap_scale_pos (net : NormalizedNetwork (m+5) h₁ h₂)
    (T : ℝ) (hm : 2≤m) (hscale : UniformGapScale net T) : 0<T := by
  classical
  let a : Fin m := ⟨0,lt_of_lt_of_le (by norm_num) hm⟩
  let b : Fin m := ⟨1,lt_of_lt_of_le (by norm_num) hm⟩
  let ρ : RankPerm m := Equiv.swap a b
  have hh := (hscale (Equiv.refl _) (Equiv.refl _) ρ).negative_tail a
  rw [actualGapPoint_selected] at hh
  change -(∑ g in Finset.univ.filter (fun g : Fin m => g.val≤a.val),
    T^((ρ g).val))<0 at hh
  have hf : Finset.univ.filter (fun g : Fin m => g.val≤a.val)={a} := by
    ext g
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    change g.val≤0 ↔ g=a
    constructor
    · intro hg
      exact Fin.ext (Nat.eq_zero_of_le_zero hg)
    · intro hg
      subst g
      exact le_rfl
  rw [hf,Finset.sum_singleton] at hh
  have hr : ρ a=b := Equiv.swap_apply_left a b
  rw [hr] at hh
  change -(T^1)<0 at hh
  rw [pow_one] at hh
  linarith only [hh]

/-- The threshold is derived from the arbitrary actual coefficient arrays.
No simultaneous genericity hypothesis is imposed on the network. -/
theorem exists_uniform_gap_scale_threshold (net : NormalizedNetwork (m + 5) h₁ h₂) :
    ∃ B : ℝ, 2 ≤ B ∧ ∀ T : ℝ, B ≤ T → UniformGapScale net T := by
  classical
  choose bound hbound hstable using fun σ : FullPerm m =>
    exists_network_gap_threshold net (baseTail σ)
  let B : ℝ := 2 + ∑ σ : FullPerm m, bound σ
  have hn : ∀ σ : FullPerm m, 0 ≤ bound σ :=
    fun σ => le_trans (by norm_num) (hbound σ)
  have hsum : 0 ≤ ∑ σ : FullPerm m, bound σ := Finset.sum_nonneg fun σ _ => hn σ
  refine ⟨B, by dsimp only [B]; linarith only [hsum], ?_⟩
  intro T hT σ τ ρ
  apply hstable σ T _ (τ, ρ)
  have hσ : bound σ ≤ ∑ σ : FullPerm m, bound σ :=
    Finset.single_le_sum (fun υ _ => hn υ) (Finset.mem_univ σ)
  dsimp only [B] at hT
  linarith only [hσ, hT]

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
