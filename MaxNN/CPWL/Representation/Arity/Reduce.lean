import MaxNN.CPWL.Representation.Arity.InclusionExclusion
import MaxNN.CPWL.Representation.Arity.Dependence

/-!
# Arity reduction: maxima of affine functions on `ℝ^d` lie in the span of arity `d+1`

`MaxOfAffineArityLE d k` is the set of maxima of at most `k` affine functions on `ℝ^d`.
`maxOn_mem_span_maxOfAffineArityLE`: for any family `g : Fin m → AffineFn d` and any
nonempty `S ⊆ Fin m`, the maximum of the `g j`, `j ∈ S`, lies in the `ℝ`-span of
`MaxOfAffineArityLE d (d+1)`.

Proof by strong induction on `|S|`.  If `|S| ≤ d+1` the maximum is itself a generator
(`isMaxOfAffineArity_card_of_maxOn`).  If `|S| ≥ d+2`, the dominating subset `J`
(`exists_dominating_subset`) turns the inclusion–exclusion identity
(`maxOn_eq_sum_powerset_erase_empty`) into a pointwise identity expressing the maximum over
`S` as a signed sum of maxima over the strictly smaller sets `S \ T`, `∅ ≠ T ⊆ J`; the span
is closed under these sums.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- The maxima of at most `k` (and at least one) affine functions on `ℝ^d`. -/
def MaxOfAffineArityLE (d k : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  { f | ∃ m : ℕ, ∃ _ : NeZero m, m ≤ k ∧ IsMaxOfAffineArity d m f }

/-- A maximum over at most `k` of the `g j` is a generator. -/
theorem maxOn_mem_span_of_card_le {d m k : ℕ} (g : Fin m → AffineFn d) {A : Finset (Fin m)}
    (hA : A.Nonempty) (hk : A.card ≤ k) :
    (fun x => maxOn A fun j => (g j).eval x) ∈ Submodule.span ℝ (MaxOfAffineArityLE d k) := by
  obtain ⟨inst, h⟩ := isMaxOfAffineArity_card_of_maxOn g hA
  exact Submodule.subset_span ⟨A.card, inst, hk, h⟩

/-- **Arity reduction.**  The maximum of any nonempty subfamily of affine functions on
`ℝ^d` lies in the span of the maxima of at most `d+1` affine functions. -/
theorem maxOn_mem_span_maxOfAffineArityLE {d m : ℕ} (g : Fin m → AffineFn d) (n : ℕ) :
    ∀ S : Finset (Fin m), S.card = n → S.Nonempty →
      (fun x => maxOn S fun j => (g j).eval x)
        ∈ Submodule.span ℝ (MaxOfAffineArityLE d (d + 1)) := by
  refine Nat.strong_induction_on n ?_
  intro n ih S hSn hS
  rcases le_or_lt S.card (d + 1) with hle | hlt
  · exact maxOn_mem_span_of_card_le g hS hle
  · obtain ⟨J, hJS, hSJ, hdom⟩ := exists_dominating_subset g S hlt
    have e : (fun x => maxOn S fun j => (g j).eval x)
        = ∑ T in J.powerset.erase ∅,
            ((-1 : ℝ) ^ (T.card + 1)) • (fun x => maxOn (S \ T) fun j => (g j).eval x) := by
      funext x
      rw [Finset.sum_apply]
      obtain ⟨j₀, hj₀, hle⟩ := hdom x
      rw [maxOn_eq_sum_powerset_erase_empty (fun j => (g j).eval x) S J hJS hSJ hj₀ hle]
      exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_eq_mul]
    rw [e]
    refine Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _ ?_
    have hT' := Finset.mem_erase.mp hT
    have hTJ : T ⊆ J := Finset.mem_powerset.mp hT'.2
    have hTne : T.Nonempty := Finset.nonempty_of_ne_empty hT'.1
    have hsub : S \ J ⊆ S \ T := Finset.sdiff_subset_sdiff (Finset.Subset.refl S) hTJ
    have hlt' : (S \ T).card < n := by
      rw [← hSn, Finset.card_sdiff (hTJ.trans hJS)]
      exact Nat.sub_lt (Finset.card_pos.mpr hS) (Finset.card_pos.mpr hTne)
    exact ih _ hlt' (S \ T) rfl (hSJ.mono hsub)

end MaxNN
