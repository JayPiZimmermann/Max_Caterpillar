import research.sN.overnight_20261103.degree_two.Recession
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Outer
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph

/-! Preserve original signed interaction graphs during recession and outer
normalization. Arbitrary original biases never delete individual first rows.
Outer normalization either retains an entire second row or sets it to zero.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.ExponentialPush.DegreeTwo.Recession
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension NormalizedNetwork
variable {N h₁ h₂ : ℕ}
attribute [local instance] Classical.propDecidable

/-- The original signed aggregate over all parallel first rows, independently
of their biases. The zero-sum condition makes the edge coefficient symmetric. -/
def rawInteractionGraph (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i=0) (k : Fin h₂) : SimpleGraph (Fin N) where
  Adj a b := a≠b ∧ braidEdgeWeight net.A (net.W k) a b≠0
  symm a b h := ⟨h.1.symm,by
    rw [←braidEdgeWeight_symm net.A (net.W k) hA a b]
    exact h.2⟩
  loopless a h := h.1 rfl

/-- Recession preserves all first rows. Only whole outer rows are normalized. -/
def normalized (net : AffineSkipNetwork N h₁ h₂) : NormalizedNetwork N h₁ h₂ :=
  normalizeOuter (model net)

@[simp] theorem normalized_A (net : AffineSkipNetwork N h₁ h₂) (j : Fin h₁) :
    (normalized net).A j=net.A j := rfl

theorem normalized_computes_max [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i=0)
    (hnet : ∀ x, AffineSkipExtension.eval net x=Maximum N x) :
    ∀ x, (normalized net).eval x=Maximum N x :=
  normalizeOuter_computes_max (model net) hA (model_computes_max net hnet)

theorem normalized_translation [NeZero N] (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i=0)
    (hnet : ∀ x, AffineSkipExtension.eval net x=Maximum N x) :
    (normalized net).TranslationNormalized :=
  normalizeOuter_translation_normalized (model net) hA (model_computes_max net hnet)

/-- A normalized edge is an original edge; exact signed parallel cancellation
is preserved because no individual first row is removed. -/
theorem normalized_graph_le_raw (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i=0)
    (hn : (normalized net).TranslationNormalized) (k : Fin h₂) :
    braidInteractionGraph (normalized net) hn k ≤ rawInteractionGraph net hA k := by
  intro a b hab
  change a≠b ∧ braidEdgeWeight net.A (net.W k) a b≠0
  change a≠b ∧ braidEdgeWeight (normalized net).A ((normalized net).W k) a b≠0 at hab
  by_cases hk : (∑ i,net.U k i)=0
  · simpa only [normalized,normalizeOuter,freezeOuter,model,hk,if_pos] using hab
  · have hz : braidEdgeWeight (normalized net).A ((normalized net).W k) a b=0 := by
      simp [normalized,normalizeOuter,freezeOuter,model,hk,braidEdgeWeight]
    exact False.elim (hab.2 hz)

/-- Degree bounds on original interaction graphs survive both exact model
reductions. This applies to any degree cap, not only degree two. -/
theorem normalized_degree_le_raw (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i, net.A j i=0)
    (hn : (normalized net).TranslationNormalized) (k : Fin h₂) (a : Fin N) :
    (braidInteractionGraph (normalized net) hn k).degree a ≤
      (rawInteractionGraph net hA k).degree a := by
  classical
  rw [←SimpleGraph.card_neighborFinset_eq_degree,
    ←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_of_subset
  intro b hb
  exact (SimpleGraph.mem_neighborFinset _ _ _).mpr
    (normalized_graph_le_raw net hA hn k ((SimpleGraph.mem_neighborFinset _ _ _).mp hb))

#check @normalized_graph_le_raw
#check @normalized_degree_le_raw
#print axioms normalized_computes_max
#print axioms normalized_translation
#print axioms normalized_graph_le_raw
#print axioms normalized_degree_le_raw
end MaxCaterpillar.ExponentialPush.DegreeTwo.Recession
