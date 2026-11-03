import research.sN.overnight_20261103.degree_two.GraphConnected
import research.sN.overnight_20261103.degree_two.GraphCapacity

/-! Capacity of actual induced subsets in an arbitrary finite graph of
maximum degree two. Components include all isolated selected vertices. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

/-- Every positive cardinality is allowed. There is no connectedness,
acyclicity, or fixed cycle ordering assumption on the ambient graph. -/
theorem twoComponentSets_card_le (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v ≤ 2) (m : ℕ) (hm : 0<m) :
    (twoComponentSets G m).card ≤ 2*N+2*(m-1)*N^2 := by
  exact twoComponentSets_card_le_of_connected G m hm
    (fun k hk => connectedSets_card_le G hdegree k hk)

#check @twoComponentSets_card_le
#print axioms twoComponentSets_card_le
end MaxCaterpillar.Overnight.DegreeTwo
