import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.SetRestriction
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-! Exact component counts under the literal enumeration of a selected set. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo
open Frontier Frontier.RandomRestriction NormalizedNetwork

variable {N : ℕ}

/-- The coordinate enumeration is a graph isomorphism, not a graph contraction. -/
def selectedGraphIso (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    G.comap (selectedEmbedding S) ≃g G.induce (S : Set (Fin N)) :=
  { S.equivFin.symm with
    map_rel_iff' := by intro a b; rfl }

theorem selected_component_card (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) :
    Nat.card (G.comap (selectedEmbedding S)).ConnectedComponent =
      Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent :=
  Nat.card_congr (selectedGraphIso G S).connectedComponentEquiv

#check @selected_component_card
#print axioms selected_component_card
end MaxCaterpillar.ExponentialPush.DegreeTwo
