import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Model
import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Forcing
import Mathlib.Tactic

/-! # Forcing one selected pair changes at most three matching indicators

The selected pairs are actual disjoint pairs of permutation positions. A
vertex belongs to at most one pair. Two position swaps can therefore affect
only the selected pair and the owners of the two source positions. The bound
is derived from actual unchanged permutation values outside those positions.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias

variable {m K : ℕ}

noncomputable def pairOwners (P : Fin K × Fin 2 → Fin m) (r : Fin m) :
    Finset (Fin K) :=
  Finset.univ.filter fun j => P (j,0) = r ∨ P (j,1) = r

@[simp] theorem mem_pairOwners (P : Fin K × Fin 2 → Fin m) (r : Fin m) (j : Fin K) :
    j ∈ pairOwners P r ↔ P (j,0) = r ∨ P (j,1) = r := by
  classical
  simp only [pairOwners,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Disjointness of all selected endpoints gives each vertex at most one owner. -/
theorem pairOwners_card_le_one (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (r : Fin m) : (pairOwners P r).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [mem_pairOwners] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals exact congrArg Prod.fst (hP (ha.trans hb.symm))

lemma endpoint_ne_of_not_owner (P : Fin K × Fin 2 → Fin m)
    (j : Fin K) (r : Fin m) (hj : j ∉ pairOwners P r) (b : Fin 2) : P (j,b) ≠ r := by
  intro he
  apply hj
  rw [mem_pairOwners]
  fin_cases b
  · exact Or.inl he
  · exact Or.inr he

noncomputable def affectedPairs (P : Fin K × Fin 2 → Fin m)
    (i : Fin K) (r s : Fin m) : Finset (Fin K) :=
  insert i (pairOwners P r ∪ pairOwners P s)

/-- The chosen pair and the owners of two source positions are at most three. -/
theorem affectedPairs_card_le_three (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (i : Fin K) (r s : Fin m) :
    (affectedPairs P i r s).card ≤ 3 := by
  classical
  calc
    (affectedPairs P i r s).card ≤ (pairOwners P r ∪ pairOwners P s).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ ((pairOwners P r).card + (pairOwners P s).card) + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ (1+1)+1 := Nat.add_le_add_right
      (Nat.add_le_add (pairOwners_card_le_one P hP r) (pairOwners_card_le_one P hP s)) 1
    _ = 3 := rfl

/-- A genuine pointwise coupling that changes only four positions, two of
which are one selected pair, increases the graph matching count by at most3.
No bound on the count difference is a hypothesis. -/
theorem matchingCount_le_of_unchanged_away (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (τ σ : Equiv.Perm (Fin m)) (i : Fin K) (r s : Fin m)
    (haway : ∀ x, x ≠ P (i,0) → x ≠ P (i,1) → x ≠ r → x ≠ s → σ x = τ x) :
    matchingCount G P σ ≤ matchingCount G P τ + 3 := by
  classical
  let A : Finset (Fin K) := Finset.univ.filter fun j =>
    G.Adj (τ (P (j,0))) (τ (P (j,1)))
  let B : Finset (Fin K) := Finset.univ.filter fun j =>
    G.Adj (σ (P (j,0))) (σ (P (j,1)))
  let C : Finset (Fin K) := affectedPairs P i r s
  have hsub : B ⊆ A ∪ C := by
    intro j hj
    by_cases hjC : j ∈ C
    · exact Finset.mem_union.mpr (Or.inr hjC)
    · apply Finset.mem_union.mpr
      apply Or.inl
      have hji : j ≠ i := by
        intro he
        apply hjC
        simp only [C,affectedPairs,Finset.mem_insert]
        exact Or.inl he
      have hjr : j ∉ pairOwners P r := by
        intro hh
        apply hjC
        simp only [C,affectedPairs,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inl hh)
      have hjs : j ∉ pairOwners P s := by
        intro hh
        apply hjC
        simp only [C,affectedPairs,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inr hh)
      have heq (b : Fin 2) : σ (P (j,b)) = τ (P (j,b)) := by
        apply haway
        · intro he
          exact hji (congrArg Prod.fst (hP he))
        · intro he
          exact hji (congrArg Prod.fst (hP he))
        · exact endpoint_ne_of_not_owner P j r hjr b
        · exact endpoint_ne_of_not_owner P j s hjs b
      have hAdj := (Finset.mem_filter.mp hj).2
      rw [heq 0,heq 1] at hAdj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAdj⟩
  change B.card ≤ A.card + 3
  calc
    B.card ≤ (A ∪ C).card := Finset.card_le_of_subset hsub
    _ ≤ A.card + C.card := Finset.card_union_le _ _
    _ ≤ A.card + 3 := Nat.add_le_add_left (affectedPairs_card_le_three P hP i r s) _

/-- The actual two-swap edge-forcing permutation satisfies the bounded
damage estimate, unconditionally in the two target vertices. -/
theorem matchingCount_forcePair_le (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (τ : Equiv.Perm (Fin m)) (i : Fin K) (a b : Fin m) :
    matchingCount G P (forcePair τ (P (i,0)) (P (i,1)) a b) ≤
      matchingCount G P τ + 3 := by
  apply matchingCount_le_of_unchanged_away G P hP τ _ i
    (firstSource τ a) (secondSource τ (P (i,0)) a b)
  intro x hxp hxq hxr hxs
  exact forcePair_apply_away τ (P (i,0)) (P (i,1)) a b x hxp hxq hxr hxs

/-- The same actual bound in the real-valued form used by size-bias Laplace estimates. -/
theorem matchingCount_forcePair_le_real (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (τ : Equiv.Perm (Fin m)) (i : Fin K) (a b : Fin m) :
    (matchingCount G P (forcePair τ (P (i,0)) (P (i,1)) a b) : ℝ) ≤
      (matchingCount G P τ : ℝ) + 3 := by
  exact_mod_cast matchingCount_forcePair_le G P hP τ i a b

/-- The actual joint sample used by the size-bias construction has the
pointwise real bound required by the finite Laplace theorem. -/
theorem sampleCoupledCount_le (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P) (ω : CouplingSample G K) :
    sampleCoupledCount G P ω ≤ sampleCount G P ω + 3 := by
  exact matchingCount_forcePair_le_real G P hP ω.1 ω.2.1 ω.2.2.fst ω.2.2.snd

#print axioms pairOwners_card_le_one
#print axioms affectedPairs_card_le_three
#print axioms matchingCount_le_of_unchanged_away
#print axioms matchingCount_forcePair_le
#print axioms matchingCount_forcePair_le_real
#print axioms sampleCoupledCount_le
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
