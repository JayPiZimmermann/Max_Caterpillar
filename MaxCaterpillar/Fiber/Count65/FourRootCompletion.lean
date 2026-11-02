import MaxCaterpillar.Fiber.Count65.RootNetworkBridge
import MaxCaterpillar.Fiber.Count65.FrameTransport.CarrierCompletion
import MaxCaterpillar.Fiber.Count65.FirstRayCover
import MaxCaterpillar.Fiber.Count65.MatrixForms

/-! # Physical completion of the four-root star endpoint

The finite directed frame is only a hypothesis about invariant first rows.
The signed coordinate carriers and the entire six-row first-matrix normal
form are consequences of actual all-input exactness.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65
open BigOperators MaxCaterpillar.Frontier RootFrames

/-- All four-root star dictionaries complete to the endpoint r=1. -/
theorem star_first_matrix_of_root_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (invariantRows net).card = 4) (q : Equiv.Perm (Fin 4))
    (hroots : ∀ j, (∑ i, net.W₁ j i) = 0 →
      ∃ a ∈ starFrame q, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • row a) :
    StarFirstMatrixForm net := by
  classical
  have hf3 : (3 : Fin 4).val = 3 := rfl
  let x : Point 4 := fun i => if i=q 2 then 0 else if i=q 0 then -2 else -1
  have htop : x (q 2) = Maximum 4 x := by
    have hx : x (q 2) = 0 := by simp [x]
    have hm : Maximum 4 x = 0 := Maximum_eq_of x 0 (q 2) hx (by
      intro i
      dsimp [x]
      split_ifs <;> norm_num)
    rw [hx,hm]
  have hinactive : ∀ j, (∑ i, net.W₁ j i) = 0 → lin (net.W₁ j) x < 0 := by
    intro j hj
    obtain ⟨a,ha,c,hc,he⟩ := hroots j hj
    rw [he,lin_smul_left]
    apply mul_neg_of_pos_of_neg hc
    simp only [starFrame,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      rw [lin_row] <;>
      simp only [x,q.injective.eq_iff] <;>
      norm_num [Fin.ext_iff,hf3]
  obtain ⟨p,n,cp,cm,hpn,hcp,hcm,hp,hn,hother⟩ :=
    FrameTransport.coordinate_carrier_completion net hnet hcard (q 2) x htop hinactive
  let A : Fin 6 → Point 4 := fun j i => Star65.firstRows 1 j (q.symm i)
  have hA0 : A 0 = row (q 0,q 1) := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [A,Star65.firstRows,row,q.injective.eq_iff,Fin.ext_iff,hf3] <;> rfl
  have hA1 : A 1 = row (q 1,q 2) := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [A,Star65.firstRows,row,q.injective.eq_iff,Fin.ext_iff,hf3] <;> rfl
  have hA2 : A 2 = row (q 3,q 2) := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [A,Star65.firstRows,row,q.injective.eq_iff,Fin.ext_iff,hf3] <;> rfl
  have hA3 : A 3 = row (q 0,q 2) := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [A,Star65.firstRows,row,q.injective.eq_iff,Fin.ext_iff,hf3] <;> rfl
  have hF4 : Star65.firstRows 1 4 = ![0,0,1,0] := rfl
  have hF5 : Star65.firstRows 1 5 = ![0,0,-1,0] := rfl
  have hA4 : A 4 = unitVec (q 2) := by
    funext i
    change Star65.firstRows 1 4 (q.symm i) = _
    rw [hF4]
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [unitVec,q.injective.eq_iff,Fin.ext_iff,hf3]
  have hA5 : A 5 = -unitVec (q 2) := by
    funext i
    change Star65.firstRows 1 5 (q.symm i) = _
    rw [hF5]
    obtain ⟨k,rfl⟩ := q.surjective i
    fin_cases k <;> norm_num [unitVec,q.injective.eq_iff,Fin.ext_iff,hf3]
  have hcover : ∀ j, ∃ k, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • A k := by
    intro j
    by_cases hj : (∑ i, net.W₁ j i) = 0
    · obtain ⟨a,ha,c,hc,he⟩ := hroots j hj
      simp only [starFrame,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨0,c,hc,he.trans (congrArg (fun v => c • v) hA0.symm)⟩
      · exact ⟨1,c,hc,he.trans (congrArg (fun v => c • v) hA1.symm)⟩
      · exact ⟨2,c,hc,he.trans (congrArg (fun v => c • v) hA2.symm)⟩
      · exact ⟨3,c,hc,he.trans (congrArg (fun v => c • v) hA3.symm)⟩
    · by_cases hjp : j=p
      · subst j
        exact ⟨4,cp,hcp,hp.trans (congrArg (fun v => cp • v) hA4.symm)⟩
      · have hjn : j=n := by
          by_contra hne
          exact hj ((hother j).mpr ⟨hjp,hne⟩)
        subst j
        exact ⟨5,cm,hcm,hn.trans (congrArg (fun v => cm • v) hA5.symm)⟩
  obtain ⟨s,hs,P,hrows⟩ := first_matrix_of_positive_ray_cover net hnet A hcover
  refine ⟨1,by norm_num,by norm_num,s,hs,P,q.symm,?_⟩
  intro j i
  exact congrFun (hrows j) i

#print axioms star_first_matrix_of_root_frame
end MaxCaterpillar.Fiber.Count65
