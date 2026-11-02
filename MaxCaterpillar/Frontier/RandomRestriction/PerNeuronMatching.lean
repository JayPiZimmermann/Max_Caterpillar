import MaxCaterpillar.Frontier.RandomRestriction.MatchingCoins
import MaxCaterpillar.Frontier.RandomRestriction.MatchingSizeBias.AllGraphs
import Mathlib.Logic.Equiv.Fin

/-! # Native Boolean-slot matching counts and actual matching moments

The local coin index is any finite type. Enumerating it and the two Boolean
endpoints only reindexes the actual matching; it changes neither the graph
event nor its uniform-permutation moment.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

noncomputable def nativeMatchingCount (H : SimpleGraph (Fin m))
    (slot : (ι × Bool) ↪ Fin m) (τ : Equiv.Perm (Fin m)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => H.Adj (τ (slot (i, false))) (τ (slot (i, true)))).card

private theorem adjacency_of_pair_eq (H : SimpleGraph (Fin m)) (a b c d : Fin m)
    (hab : a ≠ b) (hpair : ({a, b} : Finset (Fin m)) = {c, d}) :
    H.Adj a b ↔ H.Adj c d := by
  classical
  have ha : a = c ∨ a = d := by
    have hh : a ∈ ({c, d} : Finset (Fin m)) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hb : b = c ∨ b = d := by
    have hh : b ∈ ({c, d} : Finset (Fin m)) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · rw [ha, hb]
  · rw [ha, hb]
    exact H.adj_comm d c
  · exact (hab (ha.trans hb.symm)).elim

/-- The graph-edge count genuinely depends only on unordered matching data. -/
theorem nativeMatchingCount_recorded_eq (H : SimpleGraph (Fin m))
    (slot : (ι × Bool) ↪ Fin m) (τ υ : Equiv.Perm (Fin m))
    (h : Matching.recorded slot τ = Matching.recorded slot υ) :
    nativeMatchingCount H slot τ = nativeMatchingCount H slot υ := by
  classical
  unfold nativeMatchingCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hp := congrArg (fun u : Matching.Data ι m => u.1 i) h
  change ({τ (slot (i, false)), τ (slot (i, true))} : Finset (Fin m)) =
    {υ (slot (i, false)), υ (slot (i, true))} at hp
  exact adjacency_of_pair_eq H _ _ _ _
    (τ.injective.ne (Matching.slot_pair_ne slot i)) hp

noncomputable def enumeratedSlot (slot : (ι × Bool) ↪ Fin m) :
    (Fin (Fintype.card ι) × Fin 2) ↪ Fin m :=
  (((Fintype.equivFin ι).symm.prodCongr finTwoEquiv).toEmbedding).trans slot

@[simp] theorem enumeratedSlot_false (slot : (ι × Bool) ↪ Fin m)
    (i : Fin (Fintype.card ι)) :
    enumeratedSlot slot (i, 0) = slot ((Fintype.equivFin ι).symm i, false) := rfl

@[simp] theorem enumeratedSlot_true (slot : (ι × Bool) ↪ Fin m)
    (i : Fin (Fintype.card ι)) :
    enumeratedSlot slot (i, 1) = slot ((Fintype.equivFin ι).symm i, true) := rfl

theorem enumerated_matchingCount_eq (H : SimpleGraph (Fin m)) [instH : DecidableRel H.Adj]
    (slot : (ι × Bool) ↪ Fin m) (τ : Equiv.Perm (Fin m)) :
    MatchingSizeBias.matchingCount H (enumeratedSlot slot) τ =
      nativeMatchingCount H slot τ := by
  classical
  cases Subsingleton.elim instH (fun _ _ => Classical.propDecidable _)
  unfold MatchingSizeBias.matchingCount nativeMatchingCount
  apply Finset.card_congr (fun i _ => (Fintype.equivFin ι).symm i)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [enumeratedSlot_false, enumeratedSlot_true] using (Finset.mem_filter.mp hi).2
  · intro i j _ _ hij
    exact (Fintype.equivFin ι).symm.injective hij
  · intro j hj
    refine ⟨(Fintype.equivFin ι) j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [enumeratedSlot_false, enumeratedSlot_true, Equiv.symm_apply_apply] using
        (Finset.mem_filter.mp hj).2
    · exact Equiv.symm_apply_apply _ _

/-- The all-graph matching estimate in the local Boolean-slot indexing. -/
theorem native_matching_counting_le_four_hundred (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (slot : (ι × Bool) ↪ Fin m) (K η : ℝ)
    (hm : 400 ≤ (m : ℝ)) (hK : 0 < K) (hKcut : K ≤ (m : ℝ) / 100)
    (hη : 0 ≤ η) (hJ : K / 2 ≤ (Fintype.card ι : ℝ))
    (hE : η - 5 * ((m : ℝ) + 4) ≤ (H.edgeFinset.card : ℝ)) :
    60 * η^2 / (m : ℝ)^4 *
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ *
        ∑ τ : Equiv.Perm (Fin m), (1/2 : ℝ) ^ nativeMatchingCount H slot τ) ≤
      400 / K^2 := by
  have hh := MatchingSizeBias.actual_matching_counting_le_four_hundred_all_graphs H
    (enumeratedSlot slot) (enumeratedSlot slot).injective K η hm hK hKcut hη hJ hE
  simpa only [enumerated_matchingCount_eq] using hh

end MaxCaterpillar.Frontier.RandomRestriction.PerNeuron
