import research.sN.exponential_push_20261102.dictionary_bridge.ActualUnits
import research.sN.exponential_push_20261102.dictionary_bridge.CoverExpansion
import research.sN.exponential_push_20261102.structural.FiniteIndex

/-! Assemble the simultaneous forest expansions as an actual normalized
network. Both hidden layers are ordinary finite indexed arrays. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ActualBraid DictionaryBridge FiniteIndex
attribute [local instance] Classical.propDecidable

variable {N h₁ h₂ : ℕ}

abbrev ExpandedIndex (net : NormalizedNetwork N h₁ h₂) :=
  (k : Fin h₂) × UnitState net k

def expandedNetwork (net : NormalizedNetwork N h₁ h₂)
    (d : (k : Fin h₂) → UnitState net k → ℝ) :
    NormalizedNetwork N (Fintype.card (Pair N)) (Fintype.card (ExpandedIndex net)) :=
  indexedNetwork
    (fun p : Pair N => braidRoot (left p) (right p))
    (fun t : ExpandedIndex net => stateHead net t.1 t.2.val)
    (fun t p => stateWeight net t.1 t.2.val p)
    (head net.L net.A net.B)
    (coefficient net.A net.B)
    (fun t => net.d t.1 * d t.1 t.2)

theorem expanded_translationNormalized (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hc : ∀ j, (rowSupport (net.A j)).card ≤ 2)
    (d : (k : Fin h₂) → UnitState net k → ℝ) :
    (expandedNetwork net d).TranslationNormalized := by
  apply (translationNormalized_indexed _ _ _ _ _ _).mpr
  refine ⟨root_sum, ?_, ?_⟩
  · intro t
    exact stateHead_sum net hn hc t.1 t.2.val
  · rw [head_sum _ _ _ hn.1 hc]
    exact hn.2.2

theorem expanded_support_le_two (net : NormalizedNetwork N h₁ h₂)
    (d : (k : Fin h₂) → UnitState net k → ℝ) :
    ∀ j, (rowSupport ((expandedNetwork net d).A j)).card ≤ 2 := by
  apply (rowSupport_card_le_indexed _ _ _ _ _ _ 2).mpr
  intro p
  rw [root_support]
  simp [pair_distinct p]

theorem expanded_eval (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hc : ∀ j, (rowSupport (net.A j)).card ≤ 2)
    (d : (k : Fin h₂) → UnitState net k → ℝ)
    (hd : ∀ k x, relu (net.inner k x) =
      ∑ t : UnitState net k, d k t * relu (lin (stateHead net k t.val) x +
        ∑ p : Pair N, stateWeight net k t.val p *
          relu (lin (braidRoot (left p) (right p)) x))) :
    ∀ x, (expandedNetwork net d).eval x = net.eval x := by
  intro x
  rw [expandedNetwork, eval_indexed]
  have hout : lin (head net.L net.A net.B) x +
      (∑ p : Pair N, coefficient net.A net.B p *
        relu (lin (braidRoot (left p) (right p)) x)) =
      lin net.L x + ∑ j, net.B j * relu (lin (net.A j) x) := by
    simp_rw [lin_root]
    exact (linear_combination_canonical net.L net.A net.B hn.1 hc x).symm
  rw [hout]
  unfold NormalizedNetwork.eval
  congr 1
  rw [←Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [hd k x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The actual number of new second-hidden slots is bounded explicitly.
This is a finite-width replacement, not a width-preserving replacement. -/
theorem expanded_width_le (net : NormalizedNetwork N h₁ h₂) :
    Fintype.card (ExpandedIndex net) ≤ h₂ * 3 ^ Fintype.card (Pair N) := by
  rw [Fintype.card_sigma]
  calc
    (∑ k : Fin h₂, Fintype.card (UnitState net k)) ≤
        ∑ _k : Fin h₂, 3 ^ Fintype.card (Pair N) := by
      apply Finset.sum_le_sum
      intro k _
      exact forest_states_card_le (activeEdges net.A (net.W k)) left right
    _ = _ := by simp

/-- Every actual normalized braid network has a single finite forest-state
expansion valid simultaneously at every real input. -/
theorem exists_expansion (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized)
    (hc : ∀ j, (rowSupport (net.A j)).card ≤ 2) :
    ∃ d : (k : Fin h₂) → UnitState net k → ℝ,
      ∀ x, (expandedNetwork net d).eval x = net.eval x := by
  choose d hd using actual_neuron_forest_expansion net hn hc
  exact ⟨d, expanded_eval net hn hc d hd⟩

#check @exists_expansion
#print axioms expanded_translationNormalized
#print axioms expanded_support_le_two
#print axioms expanded_eval
#print axioms expanded_width_le
#print axioms exists_expansion
end MaxCaterpillar.ExponentialPush.CycleBridge
