import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.PairedWall
import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Count65.FirstRayCover

/-! # The paired first-matrix form on the four-invariant-row wall

A positive carrier supplies one code vector; the invariant anchor difference
supplies the other. Their determinant is the negative carrier row sum.
Actual first-row irredundancy turns the six-ray cover into a permutation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65
open BigOperators Frontier

theorem pairedFirstMatrixForm_of_four_invariant_paired_frame
    (net : Network 4 6 5) (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (q : Equiv.Perm (Fin 4))
    (hroots : ∀ j, (∑ i, net.W₁ j i) = 0 →
      ∃ r ∈ RootFrames.pairedFrame (q : Fin 4 → Fin 4),
        ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • RootFrames.row r) :
    PairedFirstMatrixForm net := by
  classical
  obtain ⟨p,n,t,hpn,ht,hp,hn,hnp,hother⟩ :=
    max4_four_invariant_rows_have_opposite_carriers net hnet hcard
  have hplane := paired_wall_actual_carrier_plane net hnet hcard q hroots
  let A : ℝ := net.W₁ p (q 1)
  let B : ℝ := net.W₁ p (q 3)
  let M : Fin 6 → Point 4 := fun j i => pairedRows A B 1 (-1) j (q.symm i)
  have hf3 : (3 : Fin 4).val = 3 := rfl
  have pullback (r : Fin 6) (a b : Fin 4)
      (hr : pairedRows A B 1 (-1) r = RootFrames.row (a,b)) :
      M r = RootFrames.row (q a,q b) := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    simp only [M,Equiv.symm_apply_apply,hr,RootFrames.row,q.injective.eq_iff]
  have hmodel₀ : M 0 = RootFrames.row (q 0,q 1) := by
    apply pullback
    change ![(1:ℝ),-1,0,0] = RootFrames.row (0,1)
    funext i
    fin_cases i <;> norm_num [RootFrames.row,Fin.ext_iff,hf3,Fin.coe_ofNat_eq_mod,
      Fin.ofNat,Fin.ofNat',Fin.ofNat'']
  have hmodel₁ : M 1 = RootFrames.row (q 2,q 3) := by
    apply pullback
    change ![(0:ℝ),0,1,-1] = RootFrames.row (2,3)
    funext i
    fin_cases i <;> norm_num [RootFrames.row,Fin.ext_iff,hf3,Fin.coe_ofNat_eq_mod,
      Fin.ofNat,Fin.ofNat',Fin.ofNat'']
  have hmodel₄ : M 4 = RootFrames.row (q 1,q 3) := by
    apply pullback
    change ![(0:ℝ),1,0,-1] = RootFrames.row (1,3)
    funext i
    fin_cases i <;> norm_num [RootFrames.row,Fin.ext_iff,hf3,Fin.coe_ofNat_eq_mod,
      Fin.ofNat,Fin.ofNat',Fin.ofNat'']
  have hmodel₅ : M 5 = RootFrames.row (q 3,q 1) := by
    apply pullback
    change ![(0:ℝ),-1,0,-(-1)] = RootFrames.row (3,1)
    funext i
    fin_cases i <;> norm_num [RootFrames.row,Fin.ext_iff,hf3,Fin.coe_ofNat_eq_mod,
      Fin.ofNat,Fin.ofNat',Fin.ofNat'']
  have hrow₂ : pairedRows A B 1 (-1) 2 = ![0,A,0,B] := rfl
  have hrow₃ : pairedRows A B 1 (-1) 3 = ![0,-A,0,-B] := rfl
  have hcarrier : net.W₁ p = M 2 := by
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    simp only [M,Equiv.symm_apply_apply,hrow₂]
    fin_cases k
    · change net.W₁ p (q 0) = 0
      exact hplane p (ne_of_gt hp) (q 0)
        (q.injective.ne (by decide)) (q.injective.ne (by decide))
    · rfl
    · change net.W₁ p (q 2) = 0
      exact hplane p (ne_of_gt hp) (q 2)
        (q.injective.ne (by decide)) (q.injective.ne (by decide))
    · rfl
  have hnegative : net.W₁ n = t • M 3 := by
    rw [hnp,hcarrier]
    funext i
    obtain ⟨k,rfl⟩ := q.surjective i
    simp only [Pi.smul_apply,smul_eq_mul,M,Equiv.symm_apply_apply,hrow₂,hrow₃]
    fin_cases k
    · change (-t) * 0 = t * 0
      ring
    · change (-t) * A = t * (-A)
      ring
    · change (-t) * 0 = t * 0
      ring
    · change (-t) * B = t * (-B)
      ring
  have hsum : (∑ i, net.W₁ p i) = A + B := by
    rw [← Fintype.sum_equiv q (fun i => net.W₁ p (q i)) (net.W₁ p) (fun _ => rfl)]
    have hp₀ := hplane p (ne_of_gt hp) (q 0)
      (q.injective.ne (by decide)) (q.injective.ne (by decide))
    have hp₂ := hplane p (ne_of_gt hp) (q 2)
      (q.injective.ne (by decide)) (q.injective.ne (by decide))
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change net.W₁ p (q 0) + (net.W₁ p (q 1) + (net.W₁ p (q 2) + net.W₁ p (q 3))) = A + B
    simp [hp₀,hp₂,A,B]
  have hdet : A * (-1) - B * 1 ≠ 0 := by
    rw [hsum] at hp
    nlinarith only [hp]
  have hcover : ∀ j, ∃ k, ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • M k := by
    intro j
    by_cases hj : (∑ i, net.W₁ j i) = 0
    · obtain ⟨r,hr,c,hc,he⟩ := hroots j hj
      simp only [RootFrames.pairedFrame,Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0,c,hc,by rw [hmodel₀]; exact he⟩
      · exact ⟨1,c,hc,by rw [hmodel₁]; exact he⟩
      · exact ⟨4,c,hc,by rw [hmodel₄]; exact he⟩
      · exact ⟨5,c,hc,by rw [hmodel₅]; exact he⟩
    · by_cases hjp : j = p
      · subst j
        exact ⟨2,1,one_pos,by simpa using hcarrier⟩
      · have hjn : j = n := by
          by_contra hjn
          exact hj (hother j hjp hjn)
        subst j
        exact ⟨3,t,ht,hnegative⟩
  obtain ⟨s,hs,e,he⟩ := first_matrix_of_positive_ray_cover net hnet M hcover
  refine ⟨A,B,1,-1,hdet,s,hs,e,q.symm,?_⟩
  intro j i
  exact congrFun (he j) i

#check @pairedFirstMatrixForm_of_four_invariant_paired_frame
#print axioms pairedFirstMatrixForm_of_four_invariant_paired_frame
end MaxCaterpillar.Fiber.Count65
