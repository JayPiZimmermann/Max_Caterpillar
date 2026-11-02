import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.TwoEdges.Basic
import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.SelectedFour
import Mathlib.Data.Nat.Choose.Cast

/-! # Probability of two disjoint ordinary edges in five selected labels

The probability is the actual favorable-permutation cardinality divided by
the cardinality of all permutations. Unordered two-edge subsets give the
factor sixty; no independence or uniform-subset hypothesis is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
open BigOperators

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

theorem twoEdgesEvent_subset_union : twoEdgesEvent G ⊆
    (disjointEdgePairs G).biUnion fun B => selectedFourSetEvent (pairVertices B) := by
  classical
  intro τ hτ
  obtain ⟨B,hB,hsel⟩ := hasTwoDisjointSelectedEdges_cover G τ ((mem_twoEdgesEvent G τ).mp hτ)
  exact Finset.mem_biUnion.mpr ⟨B,hB,
    (mem_selectedFourSetEvent_iff_subset (pairVertices B) τ).mpr hsel⟩

/-- Exact combinatorial union bound before any real division. -/
theorem twoEdgesEvent_card_mul_le (hN : 5≤N) :
    (twoEdgesEvent G).card*N.descFactorial 4 ≤
      G.edgeFinset.card.choose 2 * (120*Fintype.card (Equiv.Perm (Fin N))) := by
  classical
  have hc : (twoEdgesEvent G).card ≤
      ∑ B in disjointEdgePairs G,(selectedFourSetEvent (pairVertices B)).card :=
    (Finset.card_le_of_subset (twoEdgesEvent_subset_union G)).trans Finset.card_biUnion_le
  calc
    (twoEdgesEvent G).card*N.descFactorial 4 ≤
        (∑ B in disjointEdgePairs G,(selectedFourSetEvent (pairVertices B)).card)*
          N.descFactorial 4 := Nat.mul_le_mul_right _ hc
    _ = ∑ B in disjointEdgePairs G,
        (selectedFourSetEvent (pairVertices B)).card*N.descFactorial 4 := Finset.sum_mul
    _ = ∑ _B in disjointEdgePairs G,120*Fintype.card (Equiv.Perm (Fin N)) := by
      apply Finset.sum_congr rfl
      intro B hB
      exact selectedFourSetEvent_card_mul hN (pairVertices B) (pairVertices_card G B hB)
    _ = (disjointEdgePairs G).card*(120*Fintype.card (Equiv.Perm (Fin N))) := by simp
    _ ≤ G.edgeFinset.card.choose 2 * (120*Fintype.card (Equiv.Perm (Fin N))) :=
      Nat.mul_le_mul_right _ (disjointEdgePairs_card_le G)

theorem descFactorial_four_pos (hN : 5≤N) : 0<(N.descFactorial 4 : ℝ) := by
  have hn : N.descFactorial 4≠0 := by
    intro hz
    have hh := Nat.descFactorial_eq_zero_iff_lt.mp hz
    linarith only [hN,hh]
  exact_mod_cast Nat.pos_of_ne_zero hn

/-- The stronger ordinary-edge-pair bound retains the exact binomial count. -/
theorem twoEdgesEvent_fraction_le_choose (hN : 5≤N) :
    ((twoEdgesEvent G).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≤
      120*(G.edgeFinset.card.choose 2 : ℝ)/(N.descFactorial 4 : ℝ) := by
  have hp : 0<(Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨Equiv.refl (Fin N)⟩)
  have hc : ((twoEdgesEvent G).card : ℝ)*(N.descFactorial 4 : ℝ) ≤
      (G.edgeFinset.card.choose 2 : ℝ)*
        (120*(Fintype.card (Equiv.Perm (Fin N)) : ℝ)) := by
    exact_mod_cast twoEdgesEvent_card_mul_le G hN
  apply (div_le_div_iff hp (descFactorial_four_pos hN)).mpr
  nlinarith only [hc]

/-- If eta is the number of ordinary graph edges, the probability that the
five selected labels contain two disjoint ordinary edges is at most
`60 eta^2/(N)_4`. The event and probability space are literal finite objects. -/
theorem twoEdgesEvent_fraction_le (hN : 5≤N) :
    ((twoEdgesEvent G).card : ℝ)/(Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/(N.descFactorial 4 : ℝ) := by
  have hchoose : 120*(G.edgeFinset.card.choose 2 : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [(Nat.cast_nonneg G.edgeFinset.card :
      (0 : ℝ)≤(G.edgeFinset.card : ℝ))]
  exact (twoEdgesEvent_fraction_le_choose G hN).trans
    ((div_le_div_right (descFactorial_four_pos hN)).mpr hchoose)

#check @twoEdgesEvent_fraction_le
#print axioms twoEdgesEvent_subset_union
#print axioms twoEdgesEvent_card_mul_le
#print axioms descFactorial_four_pos
#print axioms twoEdgesEvent_fraction_le_choose
#print axioms twoEdgesEvent_fraction_le
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
