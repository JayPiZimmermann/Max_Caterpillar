import research.sN.overnight_20261103.degree_two.GraphDefs
import Mathlib.Data.Finset.Powerset

/-! A finite cover by original neuron graphs counts distinct selected sets.
The actual-network theorem supplies the cover, and graph theory supplies
each graph's capacity. This file contains no network or graph hypotheses
disguised as an exponential estimate. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
open BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Count all selected sets using the capacities of their witnessing graphs.
Each selected set needs just one original index; overlap is harmless. -/
theorem choose_le_sum_capacity (G : J → SimpleGraph (Fin N)) (m : ℕ)
    (hcover : ∀ S : Finset (Fin N), S.card = m →
      ∃ j, Nat.card ((G j).induce (S : Set (Fin N))).ConnectedComponent ≤ 2) :
    N.choose m ≤ ∑ j, (twoComponentSets (G j) m).card := by
  classical
  have hsub : (Finset.univ : Finset (Fin N)).powersetCard m ⊆
      Finset.univ.biUnion (fun j => twoComponentSets (G j) m) := by
    intro S hS
    have hc : S.card = m := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨j,hj⟩ := hcover S hc
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,
      (mem_twoComponentSets (G j) m S).mpr ⟨hc,hj⟩⟩
  have he := (Finset.card_le_of_subset hsub).trans Finset.card_biUnion_le
  simpa only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using he

/-- A uniform capacity bound on the original graphs gives the width bound. -/
theorem choose_le_card_mul_capacity (G : J → SimpleGraph (Fin N)) (m C : ℕ)
    (hcover : ∀ S : Finset (Fin N), S.card = m →
      ∃ j, Nat.card ((G j).induce (S : Set (Fin N))).ConnectedComponent ≤ 2)
    (hcapacity : ∀ j, (twoComponentSets (G j) m).card ≤ C) :
    N.choose m ≤ Fintype.card J * C := by
  classical
  calc
    N.choose m ≤ ∑ j, (twoComponentSets (G j) m).card :=
      choose_le_sum_capacity G m hcover
    _ ≤ ∑ _j : J, C := Finset.sum_le_sum (fun j _ => hcapacity j)
    _ = Fintype.card J * C := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]

#check @choose_le_sum_capacity
#check @choose_le_card_mul_capacity
#print axioms choose_le_sum_capacity
#print axioms choose_le_card_mul_capacity
end MaxCaterpillar.Overnight.DegreeTwo
