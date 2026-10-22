import MaxNN.Core.Max
import MaxNN.CPWL.Conditional.Finitary

/-!
# `maxOn A y` — the maximum of `y` over a finite index set, as a total function

The arity-reduction argument (`MaxNN/CPWL/Representation/Arity.lean`) manipulates maxima
over *subsets* `S \ T` of an index set inside alternating sums, where carrying a
nonemptiness proof per summand is unworkable.  `maxOn A y` is `A.sup' _ y` for nonempty `A`
and the junk value `0` for `A = ∅`; every lemma below carries an explicit nonemptiness
hypothesis where it matters.

Interface: `le_maxOn`, `maxOn_le`, `exists_maxOn_eq`, `maxOn_mono`, the one-point removal
lemma `maxOn_erase_of_le`, the bridge `maxOn_univ` to `MAX`, and
`isMaxOfAffineArity_card_of_maxOn` — the maximum of the affine functions indexed by a
nonempty `A ⊆ Fin m` is a maximum of exactly `A.card` affine functions.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- The maximum of `y` over the finite index set `A`: `A.sup' _ y` when `A` is nonempty, and
the junk value `0` when `A = ∅`.  Every lemma using it carries the nonemptiness hypothesis it
needs. -/
noncomputable def maxOn {ι : Type _} (A : Finset ι) (y : ι → ℝ) : ℝ :=
  if h : A.Nonempty then A.sup' h y else 0

theorem maxOn_eq_sup' {ι : Type _} {A : Finset ι} (h : A.Nonempty) (y : ι → ℝ) :
    maxOn A y = A.sup' h y :=
  dif_pos h

theorem le_maxOn {ι : Type _} {A : Finset ι} (y : ι → ℝ) {j : ι} (hj : j ∈ A) :
    y j ≤ maxOn A y := by
  rw [maxOn_eq_sup' ⟨j, hj⟩]
  exact Finset.le_sup' y hj

theorem maxOn_le {ι : Type _} {A : Finset ι} (h : A.Nonempty) {y : ι → ℝ} {c : ℝ}
    (hc : ∀ j ∈ A, y j ≤ c) : maxOn A y ≤ c := by
  rw [maxOn_eq_sup' h]
  exact Finset.sup'_le h y hc

theorem exists_maxOn_eq {ι : Type _} {A : Finset ι} (h : A.Nonempty) (y : ι → ℝ) :
    ∃ j ∈ A, maxOn A y = y j := by
  rw [maxOn_eq_sup' h]
  obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' h y
  exact ⟨j, hj, e⟩

theorem maxOn_mono {ι : Type _} {A B : Finset ι} (hA : A.Nonempty) (hAB : A ⊆ B)
    (y : ι → ℝ) : maxOn A y ≤ maxOn B y :=
  maxOn_le hA fun _ hj => le_maxOn y (hAB hj)

/-- Removing an index that is dominated by the maximum over the remaining indices does not
change the maximum. -/
theorem maxOn_erase_of_le {ι : Type _} [DecidableEq ι] {A : Finset ι} {y : ι → ℝ} {a : ι}
    (ha : a ∈ A) (hne : (A.erase a).Nonempty) (hle : y a ≤ maxOn (A.erase a) y) :
    maxOn A y = maxOn (A.erase a) y := by
  refine le_antisymm (maxOn_le ⟨a, ha⟩ fun j hj => ?_)
    (maxOn_mono hne (Finset.erase_subset a A) y)
  by_cases hja : j = a
  · rw [hja]
    exact hle
  · exact le_maxOn y (Finset.mem_erase.mpr ⟨hja, hj⟩)

/-- Over the full index set `Fin n`, `maxOn` is `MAX n`. -/
theorem maxOn_univ {n : ℕ} [NeZero n] (y : Fin n → ℝ) :
    maxOn Finset.univ y = MAX n y :=
  maxOn_eq_sup' Finset.univ_nonempty y

/-- The maximum of the affine functions `g j`, `j ∈ A`, for a nonempty `A ⊆ Fin m`, is a
maximum of exactly `A.card` affine functions. -/
theorem isMaxOfAffineArity_card_of_maxOn {d m : ℕ} (g : Fin m → AffineFn d)
    {A : Finset (Fin m)} (hA : A.Nonempty) :
    ∃ _ : NeZero A.card,
      IsMaxOfAffineArity d A.card (fun x => maxOn A fun j => (g j).eval x) := by
  haveI : NeZero A.card := ⟨(Finset.card_pos.mpr hA).ne'⟩
  refine ⟨inferInstance, fun t => g (A.equivFin.symm t), fun x => ?_⟩
  show maxOn A (fun j => (g j).eval x) = MAX A.card fun t => (g (A.equivFin.symm t)).eval x
  refine le_antisymm (maxOn_le hA fun j hj => ?_)
    (MAX_le fun t => le_maxOn (fun j => (g j).eval x) (A.equivFin.symm t).2)
  have e : (g j).eval x = (g (A.equivFin.symm (A.equivFin ⟨j, hj⟩))).eval x := by
    rw [Equiv.symm_apply_apply]
  rw [e]
  exact le_MAX A.card (fun t => (g (A.equivFin.symm t)).eval x) (A.equivFin ⟨j, hj⟩)

end MaxNN
