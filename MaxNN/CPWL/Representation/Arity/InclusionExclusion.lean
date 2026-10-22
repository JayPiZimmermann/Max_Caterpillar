import MaxNN.CPWL.Representation.Arity.MaxOn

/-!
# Inclusion–exclusion for maxima over subsets

The combinatorial core of the arity reduction.  Fix a finite index set `S`, a subset
`J ⊆ S`, and values `y : ι → ℝ`.  If some `j₀ ∈ J` is dominated by the maximum over
`S \ J`, then the alternating sum of the maxima over the sets `S \ T`, `T ⊆ J`, vanishes:

  `∑_{T ⊆ J} (-1)^|T| · maxOn (S \ T) y = 0`   (`sum_powerset_neg_one_pow_maxOn_sdiff`),

equivalently `maxOn S y` is the signed sum of the maxima over the strictly smaller sets
`S \ T`, `∅ ≠ T ⊆ J` (`maxOn_eq_sum_powerset_erase_empty`).

Proof: pair each `T ⊆ J \ {j₀}` with `insert j₀ T`.  Both sets `S \ T` and `S \ insert j₀ T`
contain `S \ J`, so `y j₀` is dominated in both, and removing `j₀` does not change the
maximum (`maxOn_erase_of_le`); the two terms of a pair have opposite signs and cancel.

This is the elementary special case of McMullen's full additivity of the support function
(Bakaev–Brunck–Hertrich–Stade–Yehudayoff 2025, Lemma 9) that the Wang–Sun arity bound
needs: the subdivision is the one induced by an affine dependence, so no Euler
characteristic is required.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- **Alternating sum over subsets of `J`.**  If some `j₀ ∈ J ⊆ S` satisfies
`y j₀ ≤ maxOn (S \ J) y`, then `∑_{T ⊆ J} (-1)^|T| · maxOn (S \ T) y = 0`. -/
theorem sum_powerset_neg_one_pow_maxOn_sdiff {ι : Type _} [DecidableEq ι] (y : ι → ℝ)
    (S J : Finset ι) (hJS : J ⊆ S) (hSJ : (S \ J).Nonempty)
    {j₀ : ι} (hj₀ : j₀ ∈ J) (hle : y j₀ ≤ maxOn (S \ J) y) :
    ∑ T in J.powerset, (-1 : ℝ) ^ T.card * maxOn (S \ T) y = 0 := by
  have hJ : J = insert j₀ (J.erase j₀) := (Finset.insert_erase hj₀).symm
  have hj₀' : j₀ ∉ J.erase j₀ := Finset.not_mem_erase j₀ J
  rw [hJ, Finset.sum_powerset_insert hj₀']
  have hterm : ∀ T ∈ (J.erase j₀).powerset,
      (-1 : ℝ) ^ (insert j₀ T).card * maxOn (S \ insert j₀ T) y
        = -((-1 : ℝ) ^ T.card * maxOn (S \ T) y) := by
    intro T hT
    have hTJ' : T ⊆ J.erase j₀ := Finset.mem_powerset.mp hT
    have hj₀T : j₀ ∉ T := fun h => hj₀' (hTJ' h)
    have hTJ : insert j₀ T ⊆ J := by
      intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · rw [h]
        exact hj₀
      · exact Finset.mem_of_mem_erase (hTJ' h)
    have hsub : S \ J ⊆ S \ insert j₀ T := Finset.sdiff_subset_sdiff (Finset.Subset.refl S) hTJ
    have hne : (S \ insert j₀ T).Nonempty := hSJ.mono hsub
    have hmem : j₀ ∈ S \ T := Finset.mem_sdiff.mpr ⟨hJS hj₀, hj₀T⟩
    have hle' : y j₀ ≤ maxOn ((S \ T).erase j₀) y := by
      rw [← Finset.sdiff_insert]
      exact le_trans hle (maxOn_mono hSJ hsub y)
    have hne' : ((S \ T).erase j₀).Nonempty := by
      rw [← Finset.sdiff_insert]
      exact hne
    have e1 : maxOn (S \ T) y = maxOn (S \ insert j₀ T) y := by
      rw [Finset.sdiff_insert]
      exact maxOn_erase_of_le hmem hne' hle'
    rw [Finset.card_insert_of_not_mem hj₀T, e1]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, add_neg_self]

/-- **`maxOn S` as a signed sum of maxima over strictly smaller sets.**  Under the same
hypothesis, `maxOn S y = ∑_{∅ ≠ T ⊆ J} (-1)^(|T|+1) · maxOn (S \ T) y`. -/
theorem maxOn_eq_sum_powerset_erase_empty {ι : Type _} [DecidableEq ι] (y : ι → ℝ)
    (S J : Finset ι) (hJS : J ⊆ S) (hSJ : (S \ J).Nonempty)
    {j₀ : ι} (hj₀ : j₀ ∈ J) (hle : y j₀ ≤ maxOn (S \ J) y) :
    maxOn S y
      = ∑ T in J.powerset.erase ∅, (-1 : ℝ) ^ (T.card + 1) * maxOn (S \ T) y := by
  have h := sum_powerset_neg_one_pow_maxOn_sdiff y S J hJS hSJ hj₀ hle
  rw [← Finset.add_sum_erase J.powerset (fun T => (-1 : ℝ) ^ T.card * maxOn (S \ T) y)
    (Finset.empty_mem_powerset J)] at h
  rw [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty] at h
  have e : ∀ T ∈ J.powerset.erase ∅, (-1 : ℝ) ^ (T.card + 1) * maxOn (S \ T) y
      = -((-1 : ℝ) ^ T.card * maxOn (S \ T) y) := fun T _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
  linarith

end MaxNN
