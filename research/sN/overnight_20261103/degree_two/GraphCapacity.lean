import research.sN.overnight_20261103.degree_two.GraphDefs
import research.sN.overnight_20261103.degree_two.GraphCounting
import research.sN.exponential_push_20261102.degree_two.Components

/-! Counting actual induced subsets having at most two connected components.
The only graph-count input is the separately proved connected-subset capacity. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

/-- Every actual subset with at most two induced components has a connected
one-piece or nonempty disjoint connected two-piece decomposition. -/
theorem twoComponentSets_decomposition (G : SimpleGraph (Fin N)) (m : ℕ)
    (hm : 0 < m) (S : Finset (Fin N)) (hS : S ∈ twoComponentSets G m) :
    S ∈ connectedSets G m ∨ ∃ A B : Finset (Fin N),
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      A ∈ connectedSets G A.card ∧ B ∈ connectedSets G B.card ∧
      S = A ∪ B ∧ S.card = m := by
  obtain ⟨hcard,hcomp⟩ := (mem_twoComponentSets G m S).mp hS
  have hne : S.Nonempty := Finset.card_pos.mp (hcard ▸ hm)
  rcases MaxCaterpillar.ExponentialPush.DegreeTwo.two_components_decomposition G S hne hcomp with
    hconn | ⟨A,B,hA,hB,hdisj,hunion,hAC,hBC⟩
  · exact Or.inl ((mem_connectedSets G m S).mpr ⟨hcard,hconn⟩)
  · exact Or.inr ⟨A,B,hA,hB,hdisj,
      (mem_connectedSets G A.card A).mpr ⟨rfl,hAC⟩,
      (mem_connectedSets G B.card B).mpr ⟨rfl,hBC⟩,hunion,hcard⟩

/-- Actual two-component capacity, conditional only on the connected-subset
bound. The graph-specific degree-two theorem supplies that bound. -/
theorem twoComponentSets_card_le_of_connected (G : SimpleGraph (Fin N)) (m : ℕ)
    (hm : 0 < m) (hconn : ∀ k, 0 < k → (connectedSets G k).card ≤ 2*N) :
    (twoComponentSets G m).card ≤ 2*N + 2*(m-1)*N^2 := by
  exact at_most_two_capacity (connectedSets G) (twoComponentSets G m) m N hm hconn
    (fun S hS => twoComponentSets_decomposition G m hm S hS)

#print axioms twoComponentSets_decomposition
#print axioms twoComponentSets_card_le_of_connected
end MaxCaterpillar.Overnight.DegreeTwo
