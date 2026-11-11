import MaxCaterpillar.Frontier.RandomRestriction.ActualMatchingRank

set_option autoImplicit false
namespace ActualMatchingRankCheck
open BigOperators
open MaxCaterpillar MaxCaterpillar.Frontier MaxCaterpillar.Frontier.RandomRestriction
open GoodEvent DominantGap NormalizedNetwork
variable {N h₁ h₂ m : ℕ}

example (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m)) (K : ℕ)
    (g : ↥(rankIsolatedGaps rho K)) (T : ℝ) (hT : 0 < T)
    (hg : GenericNetworkPoint net e (tau,rho) T)
    (hg' : GenericNetworkPoint net e (Matching.swapTau (rankIsolatedSlots rho K) g tau,rho) T)
    (hc : ActualClean net e k rho K tau) :
    actualMatchingRow net e k rho (Matching.swapTau (rankIsolatedSlots rho K) g tau) T -
      actualMatchingRow net e k rho tau T =
      braidEdgeWeight net.A (net.W k) (e (tau (isolatedGapPredecessor g.val))) (e (tau g.val)) •
        braidRoot (tau (isolatedGapPredecessor g.val)) (tau g.val) :=
  actualMatchingRow_swap net hn e k rho tau K g T hT hg hg' hc

/-- The conclusion mentions the literal actual preactivation and literal
original indexed real edge weights. No affine or independent-column premise. -/
example (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho : Equiv.Perm (Fin m)) (K : ℕ)
    (u : Matching.Data (↥(rankIsolatedGaps rho K)) m)
    (base : Matching.Fiber (rankIsolatedSlots rho K) u)
    (hc : ActualClean net e k rho K base.val) (T : ℝ) (hT : 0 < T)
    (hg : ∀ tau, GenericNetworkPoint net e (tau,rho) T) :
    ((Finset.univ.filter (fun p : Matching.Fiber (rankIsolatedSlots rho K) u =>
        net.inner k (actualGapPoint e (p.val,rho) T) = 0)).card : ℝ) /
      Fintype.card (Matching.Fiber (rankIsolatedSlots rho K) u) ≤
      (1/2:ℝ)^ (Finset.univ.filter (fun g : ↥(rankIsolatedGaps rho K) =>
        braidEdgeWeight net.A (net.W k) (e (base.val (isolatedGapPredecessor g.val)))
          (e (base.val g.val)) ≠ 0)).card :=
  actualClean_fiber_survival_fraction_le net hn e k rho K u base hc T hT hg

noncomputable def oneEdge : NormalizedNetwork 2 1 1 where
  A := fun _ => braidRoot 0 1
  U := fun _ => 0
  W := fun _ _ => 1
  L := unitVec 0
  B := fun _ => 0
  d := fun _ => 0

theorem oneEdge_normalized : oneEdge.TranslationNormalized := by
  refine ⟨?_,?_,?_⟩
  · intro j
    norm_num [oneEdge,braidRoot,unitVec,Fin.sum_univ_two]
  · intro k
    norm_num [oneEdge]
  · norm_num [oneEdge,unitVec,Fin.sum_univ_two]

theorem oneEdge_support : rowSupport (braidRoot (0:Fin 2) 1) = {0,1} := by
  classical
  ext i
  fin_cases i <;> norm_num [rowSupport,braidRoot,unitVec]

theorem oneEdge_weight : braidEdgeWeight oneEdge.A (oneEdge.W 0) 0 1 = -1 := by
  classical
  have hr : braidEdgeRows oneEdge.A 0 1 = Finset.univ := by
    ext j
    simp only [braidEdgeRows,Finset.mem_filter,Finset.mem_univ,true_and]
    exact iff_true_intro oneEdge_support
  rw [braidEdgeWeight,hr]
  norm_num [oneEdge,Fin.sum_univ_one,braidRoot,unitVec]

/-- Proper real-weight network witness: the actual adjacent pair swap changes
survival, and its original signed edge weight is nonzero. -/
example (rho : Equiv.Perm (Fin 2)) (T : ℝ) (hT : 0 < T) :
    0 < oneEdge.inner 0 (actualGapPoint (Function.Embedding.refl (Fin 2)) (Equiv.refl _,rho) T) ∧
      oneEdge.inner 0 (actualGapPoint (Function.Embedding.refl (Fin 2))
        (swapAdjacentConfig (Equiv.refl _,rho) 0 1) T) = 0 ∧
      braidEdgeWeight oneEdge.A (oneEdge.W 0) 0 1 ≠ 0 := by
  have hp := actualGapPoint_pair_activation (Function.Embedding.refl (Fin 2))
    (Equiv.refl _,rho) T hT 0 1 (by decide) (braidRoot 0 1)
    (oneEdge_normalized.1 0) (by simpa only [Function.Embedding.refl_apply,Equiv.refl_apply] using oneEdge_support.le)
  have hx : 0 < lin (braidRoot (0:Fin 2) 1)
      (actualGapPoint (Function.Embedding.refl (Fin 2)) (Equiv.refl _,rho) T) := by
    apply hp.1.mpr
    norm_num [braidRoot,unitVec]
  have hy : lin (braidRoot (0:Fin 2) 1)
      (actualGapPoint (Function.Embedding.refl (Fin 2)) (swapAdjacentConfig (Equiv.refl _,rho) 0 1) T) ≤ 0 := by
    apply not_lt.mp
    intro h
    have hh := hp.2.mp h
    norm_num [braidRoot,unitVec] at hh
  refine ⟨?_,?_,?_⟩
  · simpa [NormalizedNetwork.inner,oneEdge,Fin.sum_univ_one,lin_zero_left,relu_of_nonneg hx.le] using hx
  · simp [NormalizedNetwork.inner,oneEdge,Fin.sum_univ_one,lin_zero_left,relu_of_nonpos hy]
  · rw [oneEdge_weight]
    norm_num

#print axioms actualMatchingRow_zero_iff
#print axioms actualMatchingRow_swap
#print axioms actualMatchingRow_fiber_flip
#print axioms actualClean_fiber_survival_fraction_le
#print axioms oneEdge_normalized
#print axioms oneEdge_weight
end ActualMatchingRankCheck
