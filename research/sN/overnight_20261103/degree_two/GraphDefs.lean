import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! Literal connected and two-component subsets of an ordinary finite graph. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

def connectedSets (G : SimpleGraph (Fin N)) (k : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter fun S => S.card = k ∧ (G.induce (S : Set (Fin N))).Connected

def twoComponentSets (G : SimpleGraph (Fin N)) (m : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter fun S => S.card = m ∧
    Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent ≤ 2

@[simp] theorem mem_connectedSets (G : SimpleGraph (Fin N)) (k : ℕ) (S : Finset (Fin N)) :
    S ∈ connectedSets G k ↔ S.card = k ∧ (G.induce (S : Set (Fin N))).Connected := by
  simp [connectedSets]

@[simp] theorem mem_twoComponentSets (G : SimpleGraph (Fin N)) (m : ℕ) (S : Finset (Fin N)) :
    S ∈ twoComponentSets G m ↔ S.card = m ∧
      Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent ≤ 2 := by
  simp [twoComponentSets]

/-- Equivalent size-filter presentation used by the actual tie-cover count. -/
theorem twoComponentSets_eq_powersetCard_filter (G : SimpleGraph (Fin N)) (m : ℕ) :
    twoComponentSets G m = (Finset.univ.powersetCard m).filter
      (fun S : Finset (Fin N) => Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent ≤ 2) := by
  ext S
  simp [twoComponentSets, Finset.mem_powersetCard]

end MaxCaterpillar.Overnight.DegreeTwo
