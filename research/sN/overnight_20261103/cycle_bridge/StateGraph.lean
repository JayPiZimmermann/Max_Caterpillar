import research.sN.exponential_push_20261102.dictionary_bridge.ActualUnits
import research.sN.exponential_push_20261102.structural.FiniteIndex

/-! The interaction graph of an actual indexed forest-state network is
a subgraph of its active-state graph. Signed cancellations can only remove
edges. No support or graph correspondence is assumed of the final network.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DictionaryBridge
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ActualBraid FiniteIndex ForestMatching
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {K : Type*} [Fintype K]

lemma endpoints_of_root_support (p : Pair N) (a b : Fin N)
    (hs : rowSupport (braidRoot (left p) (right p)) = {a,b}) :
    (left p = a ∧ right p = b) ∨ (left p = b ∧ right p = a) := by
  rw [root_support] at hs
  have hl : left p = a ∨ left p = b := by
    have hm : left p ∈ ({a,b} : Finset (Fin N)) := hs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hr : right p = a ∨ right p = b := by
    have hm : right p ∈ ({a,b} : Finset (Fin N)) := hs ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · exact False.elim (pair_distinct p (hl.trans hr.symm))
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact False.elim (pair_distinct p (hl.trans hr.symm))

/-- Each nonzero actual signed aggregate has an active original root row.
This uses the literal finite-index network constructor and retains all
parallel-row cancellations, with arbitrary finite outer index type. -/
theorem indexed_graph_le_active (U : K → Point N) (W : K → Pair N → ℝ)
    (L : Point N) (B : Pair N → ℝ) (d : K → ℝ)
    (s : K → Pair N → State)
    (hw : ∀ k p, s k p ≠ 2 → W k p = 0)
    (hn : (indexedNetwork (fun p : Pair N => braidRoot (left p) (right p))
      U W L B d).TranslationNormalized) (k : K) :
    braidInteractionGraph
      (indexedNetwork (fun p : Pair N => braidRoot (left p) (right p)) U W L B d)
      hn (Fintype.equivFin K k) ≤ indexedGraph (active (s k)) left right := by
  classical
  intro a b he
  have hwgt := he.2
  rw [braidEdgeWeight_indexed] at hwgt
  have hsum : (∑ p : Pair N,
      if rowSupport (braidRoot (left p) (right p)) = {a,b}
      then W k p * |braidRoot (left p) (right p) a| else 0) ≠ 0 := by
    exact fun hz => hwgt (by rw [hz,neg_zero])
  obtain ⟨p,_,hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hs : rowSupport (braidRoot (left p) (right p)) = {a,b} := by
    by_contra hs
    exact hp (if_neg hs)
  have hwp : W k p ≠ 0 := by
    intro hz
    exact hp (by rw [if_pos hs,hz,zero_mul])
  have hstate : s k p = 2 := by
    by_contra hstate
    exact hwp (hw k p hstate)
  refine ⟨he.1,p,?_,endpoints_of_root_support p a b hs⟩
  simp [active,hstate]

/-- The state-weight definition automatically supplies the support clause
of `indexed_graph_le_active`. -/
theorem indexed_graph_le_state {h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂)
    (original : K → Fin h₂) (s : K → Pair N → State)
    (L : Point N) (B : Pair N → ℝ) (d : K → ℝ)
    (hn : (indexedNetwork
      (fun p : Pair N => braidRoot (left p) (right p))
      (fun k => stateHead net (original k) (s k))
      (fun k => stateWeight net (original k) (s k)) L B d).TranslationNormalized)
    (k : K) :
    braidInteractionGraph
      (indexedNetwork (fun p : Pair N => braidRoot (left p) (right p))
        (fun k => stateHead net (original k) (s k))
        (fun k => stateWeight net (original k) (s k)) L B d)
      hn (Fintype.equivFin K k) ≤ indexedGraph (active (s k)) left right := by
  apply indexed_graph_le_active _ _ _ _ _ s _ hn k
  intro k p hp
  simp [stateWeight,hp]

#check @indexed_graph_le_active
#check @indexed_graph_le_state
#print axioms indexed_graph_le_active
#print axioms indexed_graph_le_state
end MaxCaterpillar.ExponentialPush.DictionaryBridge
