import MaxCaterpillar.Fiber.Count65.FrameTransport.CarrierAssembly
import MaxCaterpillar.Fiber.Count65.FrameTransport.TwoRootBranches
import MaxCaterpillar.Fiber.Count65.FrameTransport.EnumeratedRepresentation
import MaxCaterpillar.Fiber.Count65.FrameTransport.FeatureNormalization
import MaxCaterpillar.Fiber.Count65.ForkExclusion.Scaling

/-! # The inward-fork obstruction from four actual invariant rows

The full six-row first matrix is derived by the inactive-frame carrier
completion theorem. It is not a hypothesis. Original biases and every
second-layer and output coefficient remain arbitrary.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots

/-- The fork's root center is coordinate1. Exchanging coordinates1 and2
gives the physical relative-coordinate convention used by the obstruction. -/
theorem completed_fork_anchor_swap (α β κ : ℝ) (j : Fin 6) (i : Fin 4) :
    completedRows (forkRows α β κ) 1 j (Equiv.swap 1 2 i) =
      PhysicalExtraction.carrierRows (ForkExclusion.invariantRows α β κ) j i := by
  refine Fin.addCases (m := 4) (n := 2)
    (motive := fun j : Fin 6 =>
      completedRows (forkRows α β κ) 1 j (Equiv.swap 1 2 i) =
        PhysicalExtraction.carrierRows (ForkExclusion.invariantRows α β κ) j i)
    (fun j => ?_) (fun j => ?_) j
  · change Fin.append (forkRows α β κ) ![unitVec 1,-unitVec 1]
      (Fin.castAdd 2 j) (Equiv.swap 1 2 i) =
        PhysicalExtraction.carrierRows (ForkExclusion.invariantRows α β κ) (Fin.castAdd 2 j) i
    rw [Fin.append_left,PhysicalExtraction.carrierRows_first]
    fin_cases j <;> fin_cases i <;>
      norm_num [forkRows,ForkExclusion.invariantRows,PhysicalExtraction.liftRow,
        Equiv.swap_apply_def,Fin.ext_iff,show (3 : Fin 4).val=3 from rfl] <;> rfl
  · change Fin.append (forkRows α β κ) ![unitVec 1,-unitVec 1]
      (Fin.natAdd 4 j) (Equiv.swap 1 2 i) =
        PhysicalExtraction.carrierRows (ForkExclusion.invariantRows α β κ) (Fin.natAdd 4 j) i
    rw [Fin.append_right]
    fin_cases j <;> fin_cases i <;>
      norm_num [PhysicalExtraction.carrierRows,unitVec,Equiv.swap_apply_def,
        Fin.ext_iff,show (3 : Fin 4).val=3 from rfl] <;> rfl

/-- Four actual invariant fork rows force the signed coordinate carriers;
the resulting full first matrix is excluded by the physical width-five
obstruction. No carrier or complete first-matrix form is assumed. -/
theorem network_fork_frame_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (α β κ : ℝ)
    (hα : 0<α) (hβ : 0<β) (hsum : α+β=1)
    (hbound : max α β≤κ) (hκne : κ≠1)
    (ρ : Fin 4→ℝ) (q : Equiv.Perm (Fin 4)) (hρ : ∀ j,0<ρ j)
    (hrows : ∀ j,net.W₁ (e j).val=ρ j • (fun i => forkRows α β κ j (q i))) : False := by
  have hακ : α≤κ := le_trans (le_max_left _ _) hbound
  have hβκ : β≤κ := le_trans (le_max_right _ _) hbound
  have hκ : 0<κ := lt_of_lt_of_le hα hακ
  obtain ⟨P,scale,hscale,hcomplete⟩ := completed_rows_of_inactive_frame net hnet
    (forkRows α β κ) e ρ q hρ hrows 1 (forkInactivePoint κ)
    (fork_inactive_winner κ hκ) (fork_all_strictly_inactive α β κ hsum hκ)
  let Q : Equiv.Perm (Fin 4) := (Equiv.swap 1 2).trans q.symm
  have hphysical : ∀ j i,net.W₁ (P j) (Q i)=
      scale j*PhysicalExtraction.carrierRows (ForkExclusion.invariantRows α β κ) j i := by
    intro j i
    have he := congrFun (hcomplete j) (Q i)
    change net.W₁ (P j) (Q i)=scale j*
      completedRows (forkRows α β κ) 1 j (q (Q i)) at he
    simpa only [Q,Equiv.trans_apply,q.apply_symm_apply,completed_fork_anchor_swap] using he
  exact ForkExclusion.not_exact_network_of_scaled_permuted_rows net
    hα hβ hsum hακ hβκ hκne P Q scale hscale hphysical hnet

private lemma twoRootRows_two (k : Fin 5) (s t : Point 4) :
    twoRootRows k s t 2=s := by
  unfold twoRootRows
  split_ifs <;> rfl

private lemma twoRootRows_three (k : Fin 5) (s t : Point 4) :
    twoRootRows k s t 3=t := by
  unfold twoRootRows
  split_ifs <;> rfl

/-- Every canonical two-root frame is excluded for an actual width-(6,5)
network. Sum-zero, C3, and the decoder factorization are derived from the
actual invariant-row enumeration before applying the normalization theorem. -/
theorem network_two_root_frame_excluded (net : Network 4 6 5)
    (hnet : ∀ x,net.eval x=Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (k : Fin 5) (s t : Point 4)
    (hs : Nonroot s) (ht : Nonroot t)
    (ρ : Fin 4→ℝ) (q : Equiv.Perm (Fin 4)) (hρ : ∀ j,0<ρ j)
    (hrows : ∀ j,net.W₁ (e j).val=ρ j • (fun i => twoRootRows k s t j (q i))) : False := by
  let A : Fin 4→Point 4 := enumeratedRows net e
  let B : Fin 4→Point 4 := twoRootRows k s t
  have hfactor : ∀ j,A j=ρ j • (fun i => B j (q i)) := hrows
  have hrep : Represents B := represents_of_normalized_frame A B
    (enumerated_represents net hnet e) (fun j => j) ρ q hρ hfactor
  have hcover : ∀ i,∃ j,B j i=0 := cover_of_normalized_frame A B
    (fun j => j) ρ q (fun j => ne_of_gt (hρ j)) hfactor
      (enumerated_rows_cover net hnet e)
  have hsum (j : Fin 4) : ∑ i,B j i=0 :=
    (sum_zero_of_normalized_row (A j) (B j) (ρ j) q (ne_of_gt (hρ j)) (hfactor j)).mp
      (enumerated_rows_zero_sum net e j)
  have hssum : ∑ i,s i=0 := by simpa only [B,twoRootRows_two] using hsum 2
  have htsum : ∑ i,t i=0 := by simpa only [B,twoRootRows_three] using hsum 3
  obtain ⟨α,β,κ,p,scale,hα,hβ,hab,hscale,hcanonical,hbound,_hκ,hκne,_hrep⟩ :=
    canonical_two_root_normalizes k s t hssum htsum hs ht hcover hrep
  let e' : Fin 4 ≃ invariantRows net := p.trans e
  let ρ' : Fin 4→ℝ := fun j => ρ (p j)*scale j
  have hρ' : ∀ j,0<ρ' j := fun j => mul_pos (hρ (p j)) (hscale j)
  have hrows' : ∀ j,net.W₁ (e' j).val=ρ' j • (fun i => forkRows α β κ j (q i)) := by
    intro j
    funext i
    have he := congrFun (hrows (p j)) i
    change net.W₁ (e (p j)).val i=ρ (p j)*twoRootRows k s t (p j) (q i) at he
    rw [congrFun (hcanonical j) (q i)] at he
    change net.W₁ (e (p j)).val i=(ρ (p j)*scale j)*forkRows α β κ j (q i)
    change net.W₁ (e (p j)).val i=ρ (p j)*(scale j*forkRows α β κ j (q i)) at he
    rw [he]
    ring
  exact network_fork_frame_excluded net hnet e' α β κ hα hβ hab hbound hκne ρ' q hρ' hrows'

#check @completed_fork_anchor_swap
#check @network_fork_frame_excluded
#check @network_two_root_frame_excluded
#print axioms completed_fork_anchor_swap
#print axioms network_fork_frame_excluded
#print axioms network_two_root_frame_excluded
end MaxCaterpillar.Fiber.Count65.FrameTransport
