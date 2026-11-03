import research.sN.overnight_20261103.degree_two.ActualTie
import research.sN.overnight_20261103.degree_two.FourControl

/-! Concrete all-input controls for a proper selected set and an empty tail. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo.Check
open Frontier Frontier.RandomRestriction NormalizedNetwork
open MaxCaterpillar.Overnight.DegreeTwo.Check

def properThree : Finset (Fin 4) := {0,1,2}

theorem properThree_card : properThree.card=3 := by decide
theorem properThree_ne_univ : properThree≠Finset.univ := by decide

/-- The generic tie construction is exercised on a proper selected subset
of a concrete exact four-input network. -/
theorem fourNet_proper_tie :
    ∃ k : Fin 1,fourNet.d k≠0 ∧
      Nat.card ((braidInteractionGraph fourNet fourNet_normalized k).induce
        (properThree : Set (Fin 4))).ConnectedComponent≤2 :=
  exists_active_second_on_set fourNet fourNet_normalized fourNet_braid
    fourNet_max properThree (by rw [properThree_card])

/-- The same concrete network exercises localization with no tail labels. -/
theorem fourNet_full_tie :
    ∃ k : Fin 1,fourNet.d k≠0 ∧
      Nat.card ((braidInteractionGraph fourNet fourNet_normalized k).induce
        ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))).ConnectedComponent≤2 :=
  exists_active_second_on_set fourNet fourNet_normalized fourNet_braid
    fourNet_max Finset.univ (by decide)

#print axioms fourNet_proper_tie
#print axioms fourNet_full_tie
end MaxCaterpillar.ExponentialPush.DegreeTwo.Check
