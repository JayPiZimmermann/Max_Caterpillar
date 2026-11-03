import research.sN.overnight_20261103.cycle_bridge.FiveViaCover

/-! Expanded semantic checks for the star-only proof of H(5,2). -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.CycleBridge.FiveCheck
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open ForestMatching GrowingMatching
attribute [local instance] Classical.propDecidable

/-- No representability predicate hides the actual network or cover bound. -/
theorem actual_cover_one_counterinput {h₁ h₂ : ℕ}
    (net : NormalizedNetwork 5 h₁ h₂) (hn : net.TranslationNormalized)
    (hs : ∀ j, (rowSupport (net.A j)).card ≤ 2)
    (hc : ∀ k, ∃ C : Finset (Fin 5),
      (∀ a b, (braidInteractionGraph net hn k).Adj a b → a ∈ C ∨ b ∈ C) ∧
      C.card ≤ 1) :
    ∃ x : Fin 5 → ℝ, net.eval x ≠ Maximum 5 x := by
  apply not_forall.mp
  intro he
  exact no_cover_one_maximum_five ⟨h₁,h₂,net,hn,hs,he,hc⟩

/-- The conclusion is a pair of disjoint actual signed-interaction edges,
not a matching in a support overapproximation. -/
theorem actual_two_edge_witness {h₁ h₂ : ℕ}
    (net : NormalizedNetwork 5 h₁ h₂) (hn : net.TranslationNormalized)
    (hs : ∀ j, (rowSupport (net.A j)).card ≤ 2)
    (he : ∀ x, net.eval x = Maximum 5 x) :
    ∃ k : Fin h₂, ∃ B : Finset (Sym2 (Fin 5)),
      B ⊆ (braidInteractionGraph net hn k).edgeFinset ∧ B.card = 2 ∧
      ∀ e ∈ B, ∀ f ∈ B, e ≠ f →
        Disjoint (GraphRestriction.edgeVertices e) (GraphRestriction.edgeVertices f) := by
  obtain ⟨k,B,hB,_⟩ := localMatchingObstruction_five_two_via_cycle_deletion h₁ h₂ net hn hs he
  exact ⟨k,B,(mem_matchings _ B).mp hB⟩

/-- A nonempty one-edge graph satisfies the cover hypotheses. In particular
the cover premise is not inconsistent before the MAX_5 equality is added. -/
def oneEdge : SimpleGraph (Fin 5) where
  Adj a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
  symm := by intro a b h; rcases h with h|h <;> simp_all
  loopless := by
    intro a h
    rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> norm_num at h

theorem nonempty_cover_control :
    oneEdge.Adj 0 1 ∧ IsVertexCover oneEdge ({0} : Finset (Fin 5)) ∧
    ({0} : Finset (Fin 5)).card ≤ 1 := by
  refine ⟨Or.inl ⟨rfl,rfl⟩,?_,by simp⟩
  intro a b hab
  rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

/-- The empty-cover boundary has a centre too, with no hidden nonempty-edge
assumption in the star conversion. -/
theorem empty_cover_control :
    MaxCaterpillar.Frontier.StarCertificate.StarContained (⊥ : SimpleGraph (Fin 5)) := by
  apply starContained_of_cover_one _ ∅ _ (by simp)
  intro a b hab
  exact False.elim hab

#check @actual_cover_one_counterinput
#check @actual_two_edge_witness
#print axioms actual_cover_one_counterinput
#print axioms actual_two_edge_witness
#print axioms nonempty_cover_control
#print axioms empty_cover_control
end MaxCaterpillar.ExponentialPush.CycleBridge.FiveCheck
