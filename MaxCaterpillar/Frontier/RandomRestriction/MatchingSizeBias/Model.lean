import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.Forcing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Perm

/-! # The actual partial-matching edge count

The model starts from an ordinary permutation of all vertices. The selected
position pairs are disjoint when `P` is injective. Oriented edges are mathlib's
ordinary simple-graph darts, not an assumed probability model.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
open BigOperators

abbrev OrientedEdge {m : ℕ} (G : SimpleGraph (Fin m)) := G.Dart

abbrev CouplingSample {m : ℕ} (G : SimpleGraph (Fin m)) (K : ℕ) :=
  Equiv.Perm (Fin m) × (Fin K × OrientedEdge G)

variable {m K : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

def matchingCount (P : Fin K × Fin 2 → Fin m) (τ : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter fun i => G.Adj (τ (P (i,0))) (τ (P (i,1)))).card

def forcedPermutation (P : Fin K × Fin 2 → Fin m) (ω : CouplingSample G K) :
    Equiv.Perm (Fin m) :=
  forcePair ω.1 (P (ω.2.1,0)) (P (ω.2.1,1)) ω.2.2.fst ω.2.2.snd

def sampleCount (P : Fin K × Fin 2 → Fin m) (ω : CouplingSample G K) : ℝ :=
  (matchingCount G P ω.1 : ℝ)

def sampleCoupledCount (P : Fin K × Fin 2 → Fin m) (ω : CouplingSample G K) : ℝ :=
  (matchingCount G P (forcedPermutation G P ω) : ℝ)

noncomputable def uniformWeight (_ω : CouplingSample G K) : ℝ :=
  (Fintype.card (CouplingSample G K) : ℝ)⁻¹

noncomputable def matchingMean (K : ℕ) : ℝ :=
  (K : ℝ) * (Fintype.card (OrientedEdge G) : ℝ) /
    ((m : ℝ) * ((m : ℝ)-1))

lemma oriented_edge_endpoints_ne (e : OrientedEdge G) : e.fst ≠ e.snd :=
  e.is_adj.ne

lemma oriented_edge_card : Fintype.card (OrientedEdge G) = 2*G.edgeFinset.card :=
  G.dart_card_eq_twice_card_edges

lemma matchingCount_le (P : Fin K × Fin 2 → Fin m) (τ : Equiv.Perm (Fin m)) :
    matchingCount G P τ ≤ K := by
  calc
    matchingCount G P τ ≤ (Finset.univ : Finset (Fin K)).card :=
      Finset.card_le_of_subset (Finset.filter_subset _ _)
    _ = K := by simp

lemma uniformWeight_nonneg (ω : CouplingSample G K) : 0 ≤ uniformWeight G ω := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

lemma pair_positions_ne (P : Fin K × Fin 2 → Fin m) (hP : Function.Injective P)
    (i : Fin K) : P (i,0) ≠ P (i,1) := by
  intro he
  have h := congrArg Prod.snd (hP he)
  norm_num at h

lemma forcedPermutation_selected (P : Fin K × Fin 2 → Fin m)
    (hP : Function.Injective P) (ω : CouplingSample G K) :
    (forcedPermutation G P ω) (P (ω.2.1,0)) = ω.2.2.fst ∧
    (forcedPermutation G P ω) (P (ω.2.1,1)) = ω.2.2.snd := by
  exact forcePair_pins ω.1 _ _ _ _ (pair_positions_ne P hP ω.2.1)
    (oriented_edge_endpoints_ne G ω.2.2)

#check @matchingCount
#check @forcedPermutation
end MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias
