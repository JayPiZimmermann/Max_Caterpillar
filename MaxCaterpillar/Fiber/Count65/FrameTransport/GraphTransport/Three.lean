import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.Basic
import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.CanonicalLabels
import MaxCaterpillar.Fiber.Count65.FrameTransport.ThreeRootBranches

/-! # Canonical finite graphs give explicit real-row frame normalizations

The root-frame cover is converted to rows by checked pointwise equalities.
The arbitrary nonroot rows and every positive real scale remain exposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots RootFrames SmallRootFrames
open ThreeRoots

private lemma root01 : row (0,1) = (![1,-1,0,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root10 : row (1,0) = (![-1,1,0,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root12 : row (1,2) = (![0,1,-1,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root21 : row (2,1) = (![0,-1,1,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root02 : row (0,2) = (![1,0,-1,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root20 : row (2,0) = (![-1,0,1,0] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff]
private lemma root23 : row (2,3) = (![0,0,1,-1] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff,show (3 : Fin 4).val=3 from rfl]
private lemma root32 : row (3,2) = (![0,0,-1,1] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff,show (3 : Fin 4).val=3 from rfl]
private lemma root03 : row (0,3) = (![1,0,0,-1] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff,show (3 : Fin 4).val=3 from rfl]
private lemma root30 : row (3,0) = (![-1,0,0,1] : Point 4) := by
  funext i; fin_cases i <;> norm_num [row,Fin.ext_iff,show (3 : Fin 4).val=3 from rfl]

private lemma path_orient_rows (n : ℕ) (t : Point 4) :
    threeGraphRows ![orient n 0 0 1,orient n 1 1 2,orient n 2 2 3] t =
      pathWithFourth (Nat.testBit n 0) (Nat.testBit n 1) (Nat.testBit n 2) t := by
  cases h₀ : Nat.testBit n 0 <;> cases h₁ : Nat.testBit n 1 <;>
    cases h₂ : Nat.testBit n 2 <;>
    simp [threeGraphRows,orient,h₀,h₁,h₂,pathWithFourth,
      root01,root10,root12,root21,root23,root32]

private lemma star_orient_rows (n : ℕ) (t : Point 4) :
    threeGraphRows ![orient n 0 0 1,orient n 1 0 2,orient n 2 0 3] t =
      starRows (Nat.testBit n 0) (Nat.testBit n 1) (Nat.testBit n 2) t := by
  cases h₀ : Nat.testBit n 0 <;> cases h₁ : Nat.testBit n 1 <;>
    cases h₂ : Nat.testBit n 2 <;>
    simp [threeGraphRows,orient,h₀,h₁,h₂,starRows,orientation,
      root01,root10,root02,root20,root03,root30]

theorem threeGraphRows_canonical (k : Fin 21) (t : Point 4) :
    threeGraphRows (threeCanonicalLabels k) t = threeRootRows k t := by
  fin_cases k
  · norm_num [threeGraphRows,threeCanonicalLabels,threeRootRows,transitiveTriangleRows,
      root01,root12,root02]
  · norm_num [threeGraphRows,threeCanonicalLabels,threeRootRows,cyclicTriangleRows,
      root01,root12,root20]
  · norm_num [threeGraphRows,threeCanonicalLabels,threeRootRows,oppositeAdjacentRows,
      root01,root10,root12]
  · norm_num [threeGraphRows,threeCanonicalLabels,threeRootRows,oppositeAdjacentRows,
      root01,root10,root21]
  · norm_num [threeGraphRows,threeCanonicalLabels,threeRootRows,oppositeDisjointRows,
      root01,root10,root23]
  · exact path_orient_rows 0 t
  · exact path_orient_rows 1 t
  · exact path_orient_rows 2 t
  · exact path_orient_rows 3 t
  · exact path_orient_rows 4 t
  · exact path_orient_rows 5 t
  · exact path_orient_rows 6 t
  · exact path_orient_rows 7 t
  · exact star_orient_rows 0 t
  · exact star_orient_rows 1 t
  · exact star_orient_rows 2 t
  · exact star_orient_rows 3 t
  · exact star_orient_rows 4 t
  · exact star_orient_rows 5 t
  · exact star_orient_rows 6 t
  · exact star_orient_rows 7 t

/-- The unique nonroot observation is selected from the original frame,
without a support bound or coefficient alphabet. -/
theorem normalize_three_canonical_graph {A : Fin 4 → Point 4}
    (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=3) (k : Fin 21) (q : Equiv.Perm (Fin 4))
    (hframe : (rootIndices A).image nf.roots = relabel q (threeCanonical k)) :
    ∃ t : Point 4,(∑ i,t i=0) ∧ Nonroot t ∧
      ∃ p : Equiv.Perm (Fin 4),∃ c : Fin 4→ℝ,(∀ j,0<c j) ∧
        ∀ j,A j=c j • (fun i => threeRootRows k t (p j) (q.symm i)) := by
  rw [threeCanonical_eq_image] at hframe
  obtain ⟨t,ht,hnt,p,c,hcpos,hrows⟩ :=
    normalize_three_graph nf hprop hc (threeCanonicalLabels k) q hframe
  refine ⟨t,ht,hnt,p,c,hcpos,?_⟩
  simpa only [threeGraphRows_canonical] using hrows

/-- The three-root graph cover is independent of fourth-row coefficients.
The transported fourth row is proved nonroot and zero-sum. -/
theorem three_root_frame_transport {A : Fin 4 → Point 4}
    (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=3) :
    ∃ k : Fin 21,∃ q : Equiv.Perm (Fin 4),
      ∃ t : Point 4,(∑ i,t i=0) ∧ Nonroot t ∧
        ∃ p : Equiv.Perm (Fin 4),∃ c : Fin 4→ℝ,(∀ j,0<c j) ∧
          ∀ j,A j=c j • (fun i => threeRootRows k t (p j) (q.symm i)) := by
  obtain ⟨q,k,hframe⟩ := three_roots_permutation ((rootIndices A).image nf.roots)
    (nf.root_frame_card.trans hc) nf.root_frame_noLoops
  exact ⟨k,q,normalize_three_canonical_graph nf hprop hc k q hframe⟩

#print axioms threeGraphRows_canonical
#print axioms three_root_frame_transport
end MaxCaterpillar.Fiber.Count65.FrameTransport
