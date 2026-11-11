import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.Basic
import MaxCaterpillar.Fiber.Count65.FrameTransport.GraphTransport.CanonicalLabels
import MaxCaterpillar.Fiber.Count65.FrameTransport.TwoRootBranches

/-! # Canonical finite graphs give explicit real-row frame normalizations

The root-frame cover is converted to rows by checked pointwise equalities.
The arbitrary nonroot rows and every positive real scale remain exposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots RootFrames SmallRootFrames

theorem twoGraphRows_canonical (k : Fin 5) (s t : Point 4) :
    twoGraphRows (twoCanonicalLabels k) s t = twoRootRows k s t := by
  funext j i
  fin_cases k <;> fin_cases j <;> fin_cases i <;>
    norm_num [twoGraphRows,twoCanonicalLabels,twoRootRows,inwardPairRows,row,
      Fin.ext_iff,show (3 : Fin 4).val=3 from rfl] <;> rfl

/-- The actual two nonroot observations and all positive scales are selected
from the original frame; the graph equality supplies only finite labels. -/
theorem normalize_two_canonical_graph {A : Fin 4 → Point 4}
    (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=2) (k : Fin 5) (q : Equiv.Perm (Fin 4))
    (hframe : (rootIndices A).image nf.roots = relabel q (twoCanonical k)) :
    ∃ s t : Point 4,(∑ i,s i=0) ∧ (∑ i,t i=0) ∧ Nonroot s ∧ Nonroot t ∧
      ∃ p : Equiv.Perm (Fin 4),∃ c : Fin 4→ℝ,(∀ j,0<c j) ∧
        ∀ j,A j=c j • (fun i => twoRootRows k s t (p j) (q.symm i)) := by
  rw [twoCanonical_eq_image] at hframe
  obtain ⟨s,t,hs,ht,hns,hnt,p,c,hcpos,hrows⟩ :=
    normalize_two_graph nf hprop hc (twoCanonicalLabels k) q hframe
  refine ⟨s,t,hs,ht,hns,hnt,p,c,hcpos,?_⟩
  simpa only [twoGraphRows_canonical] using hrows

/-- The checked graph cover is applied only to the actual selected roots.
Every real row scale and every complementary observation is retained. -/
theorem two_root_frame_transport {A : Fin 4 → Point 4}
    (nf : NormalizedFeatureFrame A)
    (hprop : ∀ j k,j≠k → ∀ c : ℝ,0<c → A j≠c • A k)
    (hc : (rootIndices A).card=2) :
    ∃ k : Fin 5,∃ q : Equiv.Perm (Fin 4),
      ∃ s t : Point 4,(∑ i,s i=0) ∧ (∑ i,t i=0) ∧ Nonroot s ∧ Nonroot t ∧
        ∃ p : Equiv.Perm (Fin 4),∃ c : Fin 4→ℝ,(∀ j,0<c j) ∧
          ∀ j,A j=c j • (fun i => twoRootRows k s t (p j) (q.symm i)) := by
  obtain ⟨q,k,hframe⟩ := two_roots_permutation ((rootIndices A).image nf.roots)
    (nf.root_frame_card.trans hc) nf.root_frame_noLoops
  exact ⟨k,q,normalize_two_canonical_graph nf hprop hc k q hframe⟩

#print axioms twoGraphRows_canonical
#print axioms two_root_frame_transport
end MaxCaterpillar.Fiber.Count65.FrameTransport
