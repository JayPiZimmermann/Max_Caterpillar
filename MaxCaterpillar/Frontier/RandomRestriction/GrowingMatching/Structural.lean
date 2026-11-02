import MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Transport
import MaxCaterpillar.Frontier.RandomRestriction.StructuralWitness.Graph
import MaxCaterpillar.Frontier.RandomRestriction.BraidModelLocalized
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.EmbeddedLocalizedModel

/-! # Actual-model growing-arity structural transfer

The sole structural hypothesis is a statement about actual normalized
homogeneous MAX_k networks with braid first rows and braid output skips.
It contains no counting, probability, or random-restriction premise. The
transfer retains original first/outer indices at the actual embedded point.
-/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
open BigOperators NormalizedNetwork DominantGap Cartesian
attribute [local instance] Classical.propDecidable

/-- A literal q-edge matching whose original vertices all lie in S. -/
def HasMatchingOn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ B∈matchings G q,matchingVertices B⊆S

/-- The actual local structural theorem required for the growing-arity route.
All weights and skips are arbitrary real numbers. Translation normalization
implies the support-at-most-two first rows are braid rows or zero. The
one-layer output uses exactly that same actual braid dictionary. -/
def LocalMatchingObstruction (k q : ℕ) [NeZero k] : Prop :=
  ∀ (h₁ h₂ : ℕ) (model : NormalizedNetwork k h₁ h₂)
    (hn : model.TranslationNormalized),
    (∀ j,(rowSupport (model.A j)).card≤2) →
    (∀ x,model.eval x=Maximum k x) →
    ∃ r : Fin h₂,HasMatchingOn (braidInteractionGraph model hn r) q Finset.univ

variable {N k q m h₁ h₂ : ℕ}

lemma localized_support_le_two (net : NormalizedNetwork N h₁ h₂)
    (point : Point N) (f : Fin k ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) point=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∀ j,(rowSupport ((net.localize point f).A j)).card≤2 := by
  classical
  intro j
  rw [localize_first_row]
  by_cases hj : rowSupport (net.A j)⊆Finset.univ.image f
  · rw [if_pos ((hfirst j).mpr hj),card_rowSupport_restrict f (net.A j) hj]
    exact Nat.le_of_lt_succ (lt_of_not_ge (fun hlarge => hno j hlarge hj))
  · rw [if_neg (fun hz => hj ((hfirst j).mp hz)),rowSupport_zero,Finset.card_empty]
    exact Nat.zero_le _

lemma localized_dead_weights (net : NormalizedNetwork N h₁ h₂)
    (point : Point N) (f : Fin k ↪ Fin N) (r : Fin h₂) (hr : net.inner r point≠0) :
    ∀ j,(net.localize point f).W r j=0 := by
  classical
  intro j
  change (if net.inner r point=0 then _ else 0)=0
  exact if_neg hr

/-- A positive matching forces survival of the same original outer slot. -/
lemma original_outer_zero_of_local_matching (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (point : Point N) (f : Fin k ↪ Fin N)
    (hloc : (net.localize point f).TranslationNormalized) (r : Fin h₂)
    (B : Finset (Sym2 (Fin k)))
    (hB : B∈matchings (braidInteractionGraph (net.localize point f) hloc r) q) :
    net.inner r point=0 := by
  classical
  obtain ⟨hsub,hcard,_⟩ := (mem_matchings _ B).mp hB
  have hpos : 0<B.card := by rw [hcard]; exact hq
  obtain ⟨edge,he⟩ := Finset.card_pos.mp hpos
  have hge := hsub he
  by_contra hr
  have hw := localized_dead_weights net point f r hr
  induction edge using Sym2.ind with
  | h a b =>
    have hab : (braidInteractionGraph (net.localize point f) hloc r).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hge)
    apply hab.2
    unfold braidEdgeWeight
    simp only [hw,zero_mul,Finset.sum_const_zero,neg_zero]

/-- Equality is derived from actual masks, including every original signed
parallel-row cancellation. No graph correspondence is assumed. -/
lemma localized_braidGraph_eq_comap (net : NormalizedNetwork N h₁ h₂)
    (hn : net.TranslationNormalized) (point : Point N) (f : Fin k ↪ Fin N)
    (hfirst : ∀ j,lin (net.A j) point=0 ↔ rowSupport (net.A j)⊆Finset.univ.image f)
    (hloc : (net.localize point f).TranslationNormalized)
    (r : Fin h₂) (hr : net.inner r point=0) :
    braidInteractionGraph (net.localize point f) hloc r=(braidInteractionGraph net hn r).comap f := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (a≠b ∧ braidEdgeWeight (net.localize point f).A ((net.localize point f).W r) a b≠0) ↔
    (f a≠f b ∧ braidEdgeWeight net.A (net.W r) (f a) (f b)≠0)
  rw [BraidModel.localize_braidEdgeWeight_eq_ambient net point f hfirst r hr a b]
  constructor
  · rintro ⟨hab,hw⟩
    exact ⟨f.injective.ne hab,hw⟩
  · rintro ⟨hab,hw⟩
    exact ⟨fun he => hab (congrArg f he),hw⟩

/-- Actual local-to-original transfer of a growing matching obstruction. -/
theorem structural_witness_of_generic_embedding [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
      HasMatchingOn (braidInteractionGraph net hn r) q (Finset.univ.image f) := by
  classical
  let point := actualGapPoint e p T
  have hfirst := embedded_first_zero_iff_support net f e p T hcomp h
  have hloc := embeddedLocalizedModel_translation_normalized net hn hnet f e p T hcomp h
  have hmax := embeddedLocalizedModel_computes_max net hnet f e p T hcomp h
  have hs := localized_support_le_two net point f hfirst hno
  obtain ⟨r,B,hB,_⟩ := H h₁ h₂ (net.localize point f) hloc hs hmax
  have hr := original_outer_zero_of_local_matching hq net point f hloc r B hB
  refine ⟨r,hr,?_⟩
  have hgraph := localized_braidGraph_eq_comap net hn point f hfirst hloc r hr
  rw [hgraph] at hB
  exact transport_matching (braidInteractionGraph net hn r) f B hB

/-- No generic-point assumption remains in the standalone actual threshold
statement. H(k,q) is the only new structural assumption. -/
theorem exists_structural_witness_threshold [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f) :
    ∃ B : ℝ,2≤B ∧ ∀ T : ℝ,B≤T→∀ p : RawConfig m,
      (∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) →
      ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
        HasMatchingOn (braidInteractionGraph net hn r) q (Finset.univ.image f) := by
  obtain ⟨B,hB,hgeneric⟩ := exists_network_gap_threshold net e
  exact ⟨B,hB,fun T hT p hno => structural_witness_of_generic_embedding
    H hq net hn hnet f e p T hcomp (hgeneric T hT p) hno⟩

/-- The witness belongs to the literal selected matching event of the original
ambient graph; selection is tested on the actual full permutation. -/
theorem selected_event_witness_of_generic_embedding [NeZero N] [NeZero k]
    (H : LocalMatchingObstruction k q) (hq : 0<q)
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x,net.eval x=Maximum N x)
    (f : Fin k ↪ Fin N) (e : Fin m ↪ Fin N) (p : RawConfig m) (T : ℝ)
    (hcomp : Finset.univ.image e=(Finset.univ : Finset (Fin N)) \ Finset.univ.image f)
    (h : GenericNetworkPoint net e p T) (σ : Equiv.Perm (Fin N))
    (hselected : Finset.univ.image f=GoodEvent.smallRankGaps σ k)
    (hno : ∀ j,3≤(rowSupport (net.A j)).card → ¬rowSupport (net.A j)⊆Finset.univ.image f) :
    ∃ r : Fin h₂,net.inner r (actualGapPoint e p T)=0 ∧
      hasSelectedMatching (braidInteractionGraph net hn r) k q σ := by
  obtain ⟨r,hr,B,hB,hv⟩ := structural_witness_of_generic_embedding
    H hq net hn hnet f e p T hcomp h hno
  refine ⟨r,hr,B,hB,?_⟩
  rwa [hselected] at hv

#print axioms original_outer_zero_of_local_matching
#print axioms localized_braidGraph_eq_comap
#print axioms structural_witness_of_generic_embedding
#print axioms exists_structural_witness_threshold
#print axioms selected_event_witness_of_generic_embedding
end MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching
