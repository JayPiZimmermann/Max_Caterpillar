import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card

/-!
# The `C(n,2)` unordered coordinate pairs, enumerated by `Fin (n.choose 2)`

The first hidden layer of every certificate network in the `MaxN` grammar carries one `relu`
unit per **unordered pair** of coordinates (`relu (x i - x j)` for `i < j`), and those units are
*shared by every atom of every orbit*.  To state a width bound we must therefore index the pairs
by an honest `Fin` type, which is what this file provides:

* `UPair n` — the ordered-increasing pairs `{p : Fin n × Fin n // p.1 < p.2}`;
* `card_upair : Fintype.card (UPair n) = n.choose 2` — the counting lemma;
* `upairEquiv n : UPair n ≃ Fin (n.choose 2)`, and the three projections `prFst`, `prSnd`,
  `prIdxOf` with their round-trip lemmas.

Nothing here mentions networks; it is pure combinatorics.

House style: no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

namespace Width

open Finset

/-- The unordered pairs of distinct coordinates of `ℝ^n`, presented as the ordered pairs
`(i, j)` with `i < j`.  There are `n.choose 2` of them (`card_upair`). -/
abbrev UPair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-! ## The counting lemma

`{p : Fin n × Fin n // p.1 < p.2}` and `{p // p.2 < p.1}` are disjoint, swapped into each other
by `Prod.swap`, and cover the off-diagonal; so each has half of `n*n - n` elements. -/

private theorem filter_lt_disjoint_filter_gt (n : ℕ) :
    Disjoint (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
  rw [Finset.disjoint_filter]
  rintro ⟨a, b⟩ - hab hba
  exact absurd hab (not_lt.2 hba.le)

private theorem image_swap_filter_lt (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).image Prod.swap
      = Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) := by
  ext p
  rw [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Finset.mem_filter] at hq
    exact ⟨Finset.mem_univ _, hq.2⟩
  · rintro ⟨-, hp⟩
    refine ⟨Prod.swap p, ?_, Prod.swap_swap p⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp⟩

private theorem card_filter_lt_eq_card_filter_gt (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
  rw [← image_swap_filter_lt n, Finset.card_image_of_injective _ Prod.swap_injective]

private theorem filter_lt_union_filter_gt (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
        ∪ (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1))
      = (Finset.univ : Finset (Fin n)).offDiag := by
  ext p
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro (⟨-, hab⟩ | ⟨-, hba⟩)
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, hab.ne⟩
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, hba.ne'⟩
  · rintro ⟨-, -, hne⟩
    rcases hne.lt_or_lt with h | h
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, h⟩

private theorem two_mul_card_filter_lt (n : ℕ) :
    2 * (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = (Finset.univ : Finset (Fin n)).offDiag.card := by
  rw [← filter_lt_union_filter_gt n,
    Finset.card_disjoint_union (filter_lt_disjoint_filter_gt n),
    ← card_filter_lt_eq_card_filter_gt n, two_mul]

/-- **There are exactly `n.choose 2` unordered pairs of distinct coordinates.**  This is the
number of `relu` units the first hidden layer spends on pairwise maxima. -/
theorem card_upair (n : ℕ) : Fintype.card (UPair n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  have hoff : (Finset.univ : Finset (Fin n)).offDiag.card = n * n - n := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have htwo : 2 * (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = n * n - n := by
    rw [two_mul_card_filter_lt n, hoff]
  rw [Nat.choose_two_right, mul_tsub, mul_one,
    Nat.div_eq_of_eq_mul_right zero_lt_two htwo.symm]

/-! ## The enumeration -/

/-- A concrete enumeration of the unordered pairs by `Fin (n.choose 2)`. -/
noncomputable def upairEquiv (n : ℕ) : UPair n ≃ Fin (n.choose 2) :=
  Fintype.equivFinOfCardEq (card_upair n)

/-- The smaller coordinate of the `q`-th unordered pair. -/
noncomputable def prFst {n : ℕ} (q : Fin (n.choose 2)) : Fin n :=
  (((upairEquiv n).symm q) : {p : Fin n × Fin n // p.1 < p.2}).1.1

/-- The larger coordinate of the `q`-th unordered pair. -/
noncomputable def prSnd {n : ℕ} (q : Fin (n.choose 2)) : Fin n :=
  (((upairEquiv n).symm q) : {p : Fin n × Fin n // p.1 < p.2}).1.2

theorem prFst_lt_prSnd {n : ℕ} (q : Fin (n.choose 2)) : prFst q < prSnd q :=
  (((upairEquiv n).symm q) : {p : Fin n × Fin n // p.1 < p.2}).2

/-- The index of the unordered pair `{i, j}`, given `i < j`. -/
noncomputable def prIdxOf {n : ℕ} (i j : Fin n) (h : i < j) : Fin (n.choose 2) :=
  upairEquiv n ⟨(i, j), h⟩

theorem prFst_prIdxOf {n : ℕ} (i j : Fin n) (h : i < j) : prFst (prIdxOf i j h) = i := by
  unfold prFst prIdxOf
  rw [Equiv.symm_apply_apply]

theorem prSnd_prIdxOf {n : ℕ} (i j : Fin n) (h : i < j) : prSnd (prIdxOf i j h) = j := by
  unfold prSnd prIdxOf
  rw [Equiv.symm_apply_apply]

end Width

end MaxNN
