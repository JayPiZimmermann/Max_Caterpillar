import MaxNN.Constructions.Paramid.Caterpillar.Corrections.Formula
import Mathlib.Data.Fintype.Perm

/-!
# Canonical data for labelled caterpillars

`SpineData N s` records an oriented caterpillar on `N - 1` base vertices.
There are `s + 2` ordered spine heads, one apex outside the tree, and every
remaining vertex is attached directly to one spine head.  The order of the
pendant leaves is deliberately absent: it is precisely the redundant data
removed by the full leaf quotient.
-/

namespace MaxNN.Caterpillar.Corrections

/-- Head sets of a prescribed cardinality. -/
abbrev SpineHeadSet (N m : ℕ) :=
  {H : Finset (Fin N) // H.card = m}

/-- Possible apex vertices outside a fixed set of spine heads. -/
abbrev SpineApex {N : ℕ} (H : Finset (Fin N)) :=
  {a : Fin N // a ∉ H}

/-- The pendant vertices after choosing the heads and the apex. -/
abbrev SpineLeaves {N : ℕ} (H : Finset (Fin N)) (a : SpineApex H) :=
  {v : Fin N // v ∉ H ∧ v ≠ a.1}

/-- An oriented labelled caterpillar with `s + 2` spine vertices.

The spine order distinguishes its two orientations.  A later quotient pairs
the two orientations; keeping them here makes both the semantics and the
cardinality calculation transparent.
-/
@[ext]
structure SpineData (N s : ℕ) where
  heads : Finset (Fin N)
  card_heads : heads.card = s + 2
  order : Fin (s + 2) ≃ ↑heads
  apex : SpineApex heads
  attach : SpineLeaves heads apex → ↑heads

/-- A nested-sigma presentation of `SpineData`, used to count its choices one
field at a time. -/
abbrev SpineDataSigma (N s : ℕ) :=
  Σ H : SpineHeadSet N (s + 2),
    (Fin (s + 2) ≃ ↑H.1) ×
      Σ a : SpineApex H.1, SpineLeaves H.1 a → ↑H.1

/-- `SpineData` is exactly the successive choice of a head set, a spine order,
an apex, and a parent for each remaining leaf. -/
def spineDataEquivSigma (N s : ℕ) : SpineData N s ≃ SpineDataSigma N s where
  toFun d := ⟨⟨d.heads, d.card_heads⟩, d.order, ⟨d.apex, d.attach⟩⟩
  invFun d :=
    { heads := d.1.1
      card_heads := d.1.2
      order := d.2.1
      apex := d.2.2.1
      attach := d.2.2.2 }
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨⟨H, hH⟩, o, a, f⟩; rfl

noncomputable instance spineDataFintype (N s : ℕ) : Fintype (SpineData N s) :=
  Fintype.ofEquiv (SpineDataSigma N s) (spineDataEquivSigma N s).symm

namespace SpineData

variable {N s : ℕ}

@[simp] theorem order_mem_heads (d : SpineData N s) (i : Fin (s + 2)) :
    (d.order i : Fin N) ∈ d.heads :=
  (d.order i).2

@[simp] theorem apex_not_mem_heads (d : SpineData N s) :
    d.apex.1 ∉ d.heads :=
  d.apex.2

@[simp] theorem leaf_not_mem_heads (d : SpineData N s) (v : SpineLeaves d.heads d.apex) :
    v.1 ∉ d.heads :=
  v.2.1

@[simp] theorem leaf_ne_apex (d : SpineData N s) (v : SpineLeaves d.heads d.apex) :
    v.1 ≠ d.apex.1 :=
  v.2.2

end SpineData

end MaxNN.Caterpillar.Corrections
