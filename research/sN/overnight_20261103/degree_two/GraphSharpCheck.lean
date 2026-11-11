import research.sN.overnight_20261103.degree_two.GraphSharp

/-! Exact sharp graph-capacity types and a boundary attaining the constant. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo.Check
attribute [local instance] Classical.propDecidable

/-- Exact primitive graph statement: arbitrary degree-two graphs. -/
theorem exact_sharp_connected_type {N : ℕ} (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (k : ℕ) (hk : 0<k) :
    (Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card=k ∧
      (G.induce (S : Set (Fin N))).Connected)).card≤N :=
  connectedSets_card_le_sharp G hdegree k hk

theorem exact_sharp_two_component_type {N : ℕ} (G : SimpleGraph (Fin N))
    (hdegree : ∀ v, G.degree v≤2) (m : ℕ) (hm : 0<m) :
    2*(Finset.univ.powerset.filter (fun S : Finset (Fin N) => S.card=m ∧
      Nat.card (G.induce (S : Set (Fin N))).ConnectedComponent≤2)).card
      ≤2*N+(m-1)*N^2 :=
  two_mul_twoComponentSets_card_le_sharp G hdegree m hm

/-- A concrete nonempty family attains the sharp connected-set constant. -/
theorem sharp_singleton_attains (G : SimpleGraph (Fin 1)) :
    (connectedSets G 1).card=1 := by
  apply Nat.le_antisymm
  · apply connectedSets_card_le_sharp G _ 1 (by decide)
    intro v
    have h := G.degree_lt_card_verts v
    have h' : G.degree v < 1 := by simpa using h
    exact (Nat.le_of_lt h').trans (by decide : 1≤2)
  · apply Finset.card_pos.mpr
    refine ⟨Finset.univ,(mem_connectedSets _ _ _).mpr ⟨by simp,?_⟩⟩
    let z : (Finset.univ : Finset (Fin 1)) := ⟨0,by simp⟩
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨z,?_⟩
    intro w
    have hw : z=w := Subsingleton.elim _ _
    subst w
    exact ⟨SimpleGraph.Walk.nil⟩

#check @exact_sharp_connected_type
#check @exact_sharp_two_component_type
#print axioms exact_sharp_connected_type
#print axioms exact_sharp_two_component_type
#print axioms sharp_singleton_attains
end MaxCaterpillar.Overnight.DegreeTwo.Check
