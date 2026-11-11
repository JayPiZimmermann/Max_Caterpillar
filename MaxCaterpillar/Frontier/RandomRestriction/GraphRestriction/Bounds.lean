import MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction.TwoEdges
import MaxCaterpillar.Frontier.RandomRestriction.GoodEventConstants

/-! # The two-edge event bound in the tail-arity normalization

All five selected labels come from the same original uniform permutation.
This corollary only weakens the exact falling-factorial denominator.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction

theorem twoEdgesEvent_fraction_le_tail {m : ℕ}
    (G : SimpleGraph (Fin (m+5))) [DecidableRel G.Adj] (hm : 0<m) :
    ((twoEdgesEvent G).card : ℝ)/
        (Fintype.card (Equiv.Perm (Fin (m+5))) : ℝ) ≤
      60*(G.edgeFinset.card : ℝ)^2/(m : ℝ)^4 := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  exact (twoEdgesEvent_fraction_le G (Nat.le_add_left 5 m)).trans
    (div_le_div_of_le_left (by positivity) (pow_pos hmR 4)
      (GoodEvent.fifth_prefix_descFactorial_four_ge m))

#print axioms twoEdgesEvent_fraction_le_tail
end MaxCaterpillar.Frontier.RandomRestriction.GraphRestriction
