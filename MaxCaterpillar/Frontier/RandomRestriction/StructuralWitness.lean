import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.AtPoint
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.FiveModel
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.EmbeddedLocalizedModel

/-! # Actual original-neuron witnesses at structured dominant-gap points

The sole certificate premise is the displayed closed-star real coefficient
identity. The model is the original indexed normalized network; localization
is literal at its actual complementary-tail gap point. No genericity, local
model normal form, interaction-graph equality, or survival law is assumed in
the threshold conclusions.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
open BigOperators NormalizedNetwork DominantGap Cartesian
variable {N m h₁ h₂ : ℕ} [NeZero N]

/-- Model-to-obstruction bridge at the exact point supplied by the counting
experiment. Its generic-point proof is consumed, never replaced by a different
canonical complement ordering or a separately chosen local network. -/
theorem structural_witness_of_generic_embedding
    (hcoeff : ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin 5 ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) :=
  exists_original_outer_at_localization hcoeff net hn (actualGapPoint e p T) f
    (embedded_first_zero_iff_support net f e p T hcomp h)
    (embeddedLocalizedModel_translation_normalized net hn hnet f e p T hcomp h)
    (embeddedLocalizedModel_computes_max net hnet f e p T hcomp h) hno

/-- One actual gap threshold works for every raw tail configuration. No local
model or point-genericity assumption remains in this conclusion. -/
theorem exists_structural_witness_threshold
    (hcoeff : ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin 5 ↪ Fin N) (e : Fin m ↪ Fin N)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,
      (∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) →
      ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
        HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) (Finset.univ.image f) := by
  obtain ⟨B,hB,hgeneric⟩ := exists_network_gap_threshold net e
  exact ⟨B,hB,fun T hT p hno =>
    structural_witness_of_generic_embedding hcoeff net hn hnet f e p T hcomp (hgeneric T hT p) hno⟩

/-- Literal selected-set version, preserving the caller's actual tail embedding
and actual gap point. The five-input enumeration changes no physical point. -/
theorem structural_witness_on_five_set_of_generic
    (hcoeff : ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : S.card=5)
    (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ S)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆S) :
    ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
      HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) S := by
  have hc : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image (fiveEmbedding S hS) := by
    rw [fiveEmbedding_image]
    exact hcomp
  have hn' : ∀ j,3≤(rowSupport (net.A j)).card →
      ¬rowSupport (net.A j)⊆Finset.univ.image (fiveEmbedding S hS) := by
    simpa only [fiveEmbedding_image] using hno
  simpa only [fiveEmbedding_image] using structural_witness_of_generic_embedding
    hcoeff net hn hnet (fiveEmbedding S hS) e p T hc h hn'

/-- Actual selected-set threshold statement. Apart from the independent
closed-star coefficient identity, all hypotheses refer only to the original
normalized network, the selected five-set and the actual complementary tail. -/
theorem exists_structural_witness_threshold_on_five_set
    (hcoeff : ClosedStarCoefficientIdentity)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (S : Finset (Fin N)) (hS : S.card=5) (e : Fin m ↪ Fin N)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ S) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,
      (∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆S) →
      ∃ k : Fin h₂,net.inner k (actualGapPoint e p T)=0 ∧
        HasTwoDisjointEdgesOn (braidInteractionGraph net hn k) S := by
  obtain ⟨B,hB,hgeneric⟩ := exists_network_gap_threshold net e
  exact ⟨B,hB,fun T hT p hno => structural_witness_on_five_set_of_generic
    hcoeff net hn hnet S hS e p T hcomp (hgeneric T hT p) hno⟩

#print axioms structural_witness_of_generic_embedding
#print axioms exists_structural_witness_threshold
#print axioms structural_witness_on_five_set_of_generic
#print axioms exists_structural_witness_threshold_on_five_set
end MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness
