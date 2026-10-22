import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import Std.Tactic.Omega

/-! # On a forest, an orientation is determined by its in-degree vector

Abstract combinatorics for the cubic lower bound on `s_N`
(`research/sN/NOTE.md`, "Cubic claim C", step 3).

A finite rooted forest on `V` is given by a parent function
`parent : V → Option V` together with a height function `μ : V → ℕ` that
strictly increases along parent edges (this is exactly acyclicity).  The
forest neighbours of `v` are its parent and its children.  A "total order"
is a rank function `r : V → β` into a linear order, required only to separate
the two ends of every forest edge (ties between non-adjacent vertices are
allowed, as for the vertices of `T` in the application).

`upCount parent r v` is the number of forest neighbours of `v` strictly above
`v`.  Main result (`orient_eq_of_upCount_eq`): if two rank functions have the
same `upCount` at every vertex of the subtree below `v`, then they orient the
edge from `v` to its parent in the same way.  Proof: strong induction on the
height: the children edges agree by induction, so the parent edge contributes
the same amount to both counts.
-/

open Finset Classical

namespace MaxCaterpillar.CountCubic

variable {V β : Type*} [Fintype V] [LinearOrder β]

/-- `v` and `w` are joined by an edge of the forest given by `parent`. -/
def ForestAdj (parent : V → Option V) (v w : V) : Prop :=
  parent v = some w ∨ parent w = some v

/-- Number of forest neighbours of `v` that lie strictly above `v` under `r`. -/
noncomputable def upCount (parent : V → Option V) (r : V → β) (v : V) : ℕ :=
  (univ.filter fun w => ForestAdj parent v w ∧ r v < r w).card

/-- Number of children of `v` that lie strictly above `v` under `r`. -/
noncomputable def childUpCount (parent : V → Option V) (r : V → β) (v : V) : ℕ :=
  (univ.filter fun w => parent w = some v ∧ r v < r w).card

/-- `d` lies in the subtree of `v` (follow parents from `d` to reach `v`). -/
def InSubtree (parent : V → Option V) (d v : V) : Prop :=
  Relation.ReflTransGen (fun a b => parent a = some b) d v

theorem upCount_eq_childUpCount_add (parent : V → Option V) (μ : V → ℕ)
    (hμ : ∀ v p, parent v = some p → μ v < μ p) (r : V → β) (v p : V)
    (hp : parent v = some p) :
    upCount parent r v = childUpCount parent r v + if r v < r p then 1 else 0 := by
  have hsplit : upCount parent r v = ((univ.filter fun w => parent w = some v ∧ r v < r w) ∪
        (univ.filter fun w => w = p ∧ r v < r w)).card := by
    unfold upCount ForestAdj
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_union, hp, Option.some.injEq]
    constructor
    · rintro ⟨h | h, hr⟩
      · exact Or.inr ⟨h.symm, hr⟩
      · exact Or.inl ⟨h, hr⟩
    · rintro (⟨h, hr⟩ | ⟨h, hr⟩)
      · exact ⟨Or.inr h, hr⟩
      · exact ⟨Or.inl h.symm, hr⟩
  have hdisj : Disjoint (univ.filter fun w => parent w = some v ∧ r v < r w)
      (univ.filter fun w => w = p ∧ r v < r w) := by
    rw [disjoint_filter]
    rintro w _ ⟨h, _⟩ ⟨rfl, _⟩
    have h1 := hμ _ _ hp
    have h2 := hμ _ _ h
    omega
  rw [hsplit, card_disjoint_union hdisj]
  unfold childUpCount
  congr 1
  by_cases hr : r v < r p
  · rw [if_pos hr, card_eq_one]
    refine ⟨p, ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, hr⟩
  · rw [if_neg hr, card_eq_zero, filter_eq_empty_iff]
    rintro w _ ⟨rfl, h⟩
    exact hr h

/-- **Forest orientations are determined by in-degrees (local form).**
Let `r₁`, `r₂` separate the ends of every forest edge and have the same number
of forest neighbours above `w` for every `w ∈ S`.  If the whole subtree of `v`
lies in `S` and `p` is the parent of `v`, then `r₁` and `r₂` orient the edge
`v p` the same way. -/
theorem orient_eq_of_upCount_eq (parent : V → Option V) (μ : V → ℕ)
    (hμ : ∀ v p, parent v = some p → μ v < μ p) (r₁ r₂ : V → β) (S : Set V)
    (hne₁ : ∀ v p, parent v = some p → r₁ v ≠ r₁ p)
    (hne₂ : ∀ v p, parent v = some p → r₂ v ≠ r₂ p)
    (hcount : ∀ w ∈ S, upCount parent r₁ w = upCount parent r₂ w) :
    ∀ v p, parent v = some p → (∀ d, InSubtree parent d v → d ∈ S) →
      (r₁ v < r₁ p ↔ r₂ v < r₂ p) := by
  intro v
  induction' hn : μ v using Nat.strong_induction_on with n ih generalizing v
  intro p hp hsub
  -- children edges agree
  have hchild : ∀ c, parent c = some v → (r₁ v < r₁ c ↔ r₂ v < r₂ c) := by
    intro c hc
    have hlt : μ c < n := hn ▸ hμ c v hc
    have hsubc : ∀ d, InSubtree parent d c → d ∈ S :=
      fun d hd => hsub d (Relation.ReflTransGen.tail hd hc)
    have h := ih (μ c) hlt c rfl v hc hsubc
    have n1 := hne₁ c v hc
    have n2 := hne₂ c v hc
    constructor
    · intro h1
      rcases lt_or_gt_of_ne n2 with h2 | h2
      · exact absurd (h.mpr h2) (not_lt.mpr h1.le)
      · exact h2
    · intro h2
      rcases lt_or_gt_of_ne n1 with h1 | h1
      · exact absurd (h.mp h1) (not_lt.mpr h2.le)
      · exact h1
  have hc : childUpCount parent r₁ v = childUpCount parent r₂ v := by
    unfold childUpCount
    congr 1
    refine filter_congr fun c _ => ?_
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, (hchild c h).mp h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, (hchild c h).mpr h'⟩
  have hv := hcount v (hsub v Relation.ReflTransGen.refl)
  rw [upCount_eq_childUpCount_add parent μ hμ r₁ v p hp,
    upCount_eq_childUpCount_add parent μ hμ r₂ v p hp, hc] at hv
  have hv' := Nat.add_left_cancel hv
  by_cases h1 : r₁ v < r₁ p <;> by_cases h2 : r₂ v < r₂ p
  · exact iff_of_true h1 h2
  · rw [if_pos h1, if_neg h2] at hv'; exact absurd hv' one_ne_zero
  · rw [if_neg h1, if_pos h2] at hv'; exact absurd hv' zero_ne_one
  · exact iff_of_false h1 h2

/-- **Forest orientations are determined by in-degrees.** Two rank functions
separating the ends of every forest edge, with the same number of forest
neighbours above every vertex, induce the same orientation on every edge. -/
theorem orient_eq_of_upCount_eq_all (parent : V → Option V) (μ : V → ℕ)
    (hμ : ∀ v p, parent v = some p → μ v < μ p) (r₁ r₂ : V → β)
    (hne₁ : ∀ v p, parent v = some p → r₁ v ≠ r₁ p)
    (hne₂ : ∀ v p, parent v = some p → r₂ v ≠ r₂ p)
    (hcount : ∀ w, upCount parent r₁ w = upCount parent r₂ w) :
    ∀ v p, parent v = some p → (r₁ v < r₁ p ↔ r₂ v < r₂ p) :=
  fun v p hp => orient_eq_of_upCount_eq parent μ hμ r₁ r₂ Set.univ hne₁ hne₂
    (fun w _ => hcount w) v p hp (fun _ _ => Set.mem_univ _)

end MaxCaterpillar.CountCubic
