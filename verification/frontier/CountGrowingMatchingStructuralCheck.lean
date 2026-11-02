import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural
import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance

set_option autoImplicit false
noncomputable section
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.RandomRestriction
open MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open MaxCaterpillar.Frontier.RandomRestriction.DominantGap
open MaxCaterpillar.Frontier.RandomRestriction.Cartesian
open BigOperators
attribute [local instance] Classical.propDecidable

/-- H is a structural statement solely about actual local MAX networks.
There is no count, event, probability or random-configuration premise. -/
example (k q : ℕ) [NeZero k] : LocalMatchingObstruction k q ↔
    ∀ (h₁ h₂ : ℕ) (model : NormalizedNetwork k h₁ h₂)
      (hn : model.TranslationNormalized),
      (∀ j,(NormalizedNetwork.rowSupport (model.A j)).card≤2) →
      (∀ x,model.eval x=Maximum k x) →
      ∃ r : Fin h₂,∃ B∈matchings (braidInteractionGraph model hn r) q,
        matchingVertices B⊆(Finset.univ : Finset (Fin k)) := Iff.rfl

/-- Positive calibration: the independently proved actual five-variable
obstruction supplies H(5,2), with no new coefficient or counting premise. -/
example : LocalMatchingObstruction 5 2 := localMatchingObstruction_five_two

/-- The matching conclusion uses ordinary original unordered graph edges. -/
example {N q : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (S : Finset (Fin N)) :
    HasMatchingOn G q S ↔
      ∃ B : Finset (Sym2 (Fin N)),B⊆G.edgeFinset ∧ B.card=q ∧
        (∀ a∈B,∀ b∈B,a≠b→
          Disjoint (GraphRestriction.edgeVertices a) (GraphRestriction.edgeVertices b)) ∧
        matchingVertices B⊆S := by
  constructor
  · rintro ⟨B,hB,hS⟩
    obtain ⟨hsub,hcard,hdisj⟩ := (mem_matchings G B).mp hB
    exact ⟨B,hsub,hcard,hdisj,hS⟩
  · rintro ⟨B,hsub,hcard,hdisj,hS⟩
    exact ⟨B,(mem_matchings G B).mpr ⟨hsub,hcard,hdisj⟩,hS⟩

example {N k q m h₁ h₂ : ℕ} [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
      ∃ B∈matchings (braidInteractionGraph net hn r) q,
        matchingVertices B⊆Finset.univ.image f :=
  structural_witness_of_generic_embedding H hq net hn hnet f e p T hcomp h hno

/-- Standalone transfer has only H as its new structural premise. All point
realization, actual model localization and exact graph transport are proved. -/
example {N k q m h₁ h₂ : ℕ} [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,
      (∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
        ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f) →
      ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
        ∃ C∈matchings (braidInteractionGraph net hn r) q,
          matchingVertices C⊆Finset.univ.image f :=
  exists_structural_witness_threshold H hq net hn hnet f e hcomp

example {N k q m h₁ h₂ : ℕ} [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (σ : Equiv.Perm (Fin N))
    (hselected : Finset.univ.image f=GoodEvent.smallRankGaps σ k)
    (hno : ∀ j,3≤(NormalizedNetwork.rowSupport (net.A j)).card →
      ¬NormalizedNetwork.rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
      hasSelectedMatching (braidInteractionGraph net hn r) k q σ :=
  selected_event_witness_of_generic_embedding H hq net hn hnet f e p T hcomp h σ hselected hno

namespace GrowingMatchingChecks
/-- A genuine normalized MAX1 skip model with no hidden neurons. -/
noncomputable def linearOne : NormalizedNetwork 1 0 0 where
  A := 0
  U := 0
  W := 0
  L := fun _ => 1
  B := 0
  d := 0

lemma linearOne_normalized : linearOne.TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · simp [linearOne,Fin.sum_univ_succ]

lemma linearOne_max : ∀ x,linearOne.eval x=Maximum 1 x := by
  intro x
  have hm : Maximum 1 x=x 0 := by
    apply le_antisymm
    · apply (Maximum_le_iff _ _).mpr
      intro i
      have hi : i=0 := Subsingleton.elim _ _
      rw [hi]
    · exact le_Maximum x 0
  rw [hm]
  simp [NormalizedNetwork.eval,NormalizedNetwork.inner,linearOne,lin,Fin.sum_univ_succ]

/-- Control: H is not automatic, even for a nonempty actual MAX model. -/
lemma not_obstruction_one_one : ¬LocalMatchingObstruction 1 1 := by
  intro H
  obtain ⟨r,_⟩ := H 0 0 linearOne linearOne_normalized
    (by intro j; exact Fin.elim0 j) linearOne_max
  exact Fin.elim0 r
end GrowingMatchingChecks

#print axioms localized_support_le_two
#print axioms localized_dead_weights
#print axioms original_outer_zero_of_local_matching
#print axioms localized_braidGraph_eq_comap
#print axioms structural_witness_of_generic_embedding
#print axioms exists_structural_witness_threshold
#print axioms selected_event_witness_of_generic_embedding
#print axioms GrowingMatchingChecks.linearOne_normalized
#print axioms GrowingMatchingChecks.linearOne_max
#print axioms GrowingMatchingChecks.not_obstruction_one_one
#print axioms localMatchingObstruction_five_two
