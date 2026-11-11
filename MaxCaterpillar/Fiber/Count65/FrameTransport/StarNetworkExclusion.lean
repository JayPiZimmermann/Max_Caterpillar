import MaxCaterpillar.Fiber.Count65.FrameTransport.CarrierAssembly
import MaxCaterpillar.Fiber.Count65.FrameTransport.FeatureNormalization
import MaxCaterpillar.Fiber.Count65.FrameTransport.RootSelection
import MaxCaterpillar.Fiber.Count65.ThreeRoots.Star
import MaxCaterpillar.Fiber.Count65.StarNonroot

/-! # Exclude the actual three-root star from its four invariant rows

The two carrier rows and the full first-matrix form are derived from an actual
network. Only its four invariant rows are normalized in the hypotheses.
All original biases and second-hidden-layer parameters are unrestricted.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots ThreeRoots

/-- A genuine zero-sum leaf nonroot admits a strict inactive point for the
whole outward star. No generic-point or limiting argument is needed. -/
theorem outward_star_strictly_inactive (t : Point 4)
    (hsum : ∑ i, t i = 0) (h0 : t 0 = 0) (ht : Nonroot t) :
    ∃ z : Point 4, z 0 = Maximum 4 z ∧
      ∀ j, lin (starRows false false false t j) z < 0 := by
  have hs : t 0+t 1+t 2+t 3=0 := by
    simpa [Fin.sum_univ_succ,add_assoc,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] using hsum
  have hp : 0 < t 1 ∨ 0 < t 2 ∨ 0 < t 3 := by
    by_contra hh
    push_neg at hh
    exact (star_nonroot_leaf_nonzero t hsum ht h0).1
      (by linarith only [hs,h0,hh.1,hh.2.1,hh.2.2])
  rcases hp with h1 | h2 | h3
  · refine ⟨![0,-2,-1,-1],by norm_num [Maximum_four],?_⟩
    intro j
    fin_cases j
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · change lin t (![0,-2,-1,-1] : Point 4) < 0
      rw [lin_four]
      change t 0*0+t 1*(-2)+t 2*(-1)+t 3*(-1)<0
      linarith only [hs,h0,h1]
  · refine ⟨![0,-1,-2,-1],by norm_num [Maximum_four],?_⟩
    intro j
    fin_cases j
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · change lin t (![0,-1,-2,-1] : Point 4) < 0
      rw [lin_four]
      change t 0*0+t 1*(-1)+t 2*(-2)+t 3*(-1)<0
      linarith only [hs,h0,h2]
  · refine ⟨![0,-1,-1,-2],by norm_num [Maximum_four],?_⟩
    intro j
    fin_cases j
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · norm_num [lin_four,starRows,orientation]
    · change lin t (![0,-1,-1,-2] : Point 4) < 0
      rw [lin_four]
      change t 0*0+t 1*(-1)+t 2*(-1)+t 3*(-2)<0
      linarith only [hs,h0,h3]

private def starInputPermutation : Equiv.Perm (Fin 4) where
  toFun := ![1,2,0,3]
  invFun := ![2,0,1,3]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem completed_star_rows (t : Point 4) :
    completedRows (starRows false false false t) 0 =
      ![![-1,1,0,0],![-1,0,1,0],![-1,0,0,1],t,
        ![1,0,0,0],![-1,0,0,0]] := by
  let V : Fin 6 → Point 4 :=
    ![![-1,1,0,0],![-1,0,1,0],![-1,0,0,1],t,
      ![1,0,0,0],![-1,0,0,0]]
  change completedRows (starRows false false false t) 0 = V
  funext j
  refine Fin.addCases (m := 4) (n := 2)
    (motive := fun k => completedRows (starRows false false false t) 0 k = V k)
    (fun j => ?_) (fun j => ?_) j
  · simp only [completedRows,Fin.append_left]
    fin_cases j <;> funext i <;> fin_cases i <;>
      norm_num [V,starRows,orientation,Fin.ext_iff] <;> rfl
  · simp only [completedRows,Fin.append_right]
    fin_cases j <;> funext i <;> fin_cases i <;>
      norm_num [V,unitVec,Fin.ext_iff] <;> rfl

private theorem star_nonroot_rows (a b c : ℝ) :
    StarNonroot.firstRows a b c =
      ![![1,0,-1,0],![0,1,-1,0],![0,0,-1,1],![a,b,-a-b-c,c],
        ![0,0,1,0],![0,0,-1,0]] := by
  funext j
  fin_cases j
  · change ![(1 : ℝ),0,-1-0-0,0] = ![1,0,-1,0]
    norm_num
  · change ![(0 : ℝ),1,-0-1-0,0] = ![0,1,-1,0]
    norm_num
  · change ![(0 : ℝ),0,-0-0-1,1] = ![0,0,-1,1]
    norm_num
  · change ![a,b,-a-b-c,c] = ![a,b,-a-b-c,c]
    rfl
  · rfl
  · rfl

private theorem completed_star_rows_permute (t : Point 4)
    (h0 : t 0 = 0) (hsum : ∑ i, t i = 0) (j : Fin 6) (i : Fin 4) :
    completedRows (starRows false false false t) 0 j (starInputPermutation i) =
      StarNonroot.firstRows (t 1) (t 2) (t 3) j i := by
  have hs : t 0+t 1+t 2+t 3=0 := by
    simpa [Fin.sum_univ_succ,add_assoc,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] using hsum
  rw [completed_star_rows,star_nonroot_rows]
  fin_cases j <;> fin_cases i <;>
    norm_num [starInputPermutation,Fin.ext_iff,h0]
  all_goals first | linarith only [hs,h0] | rfl

/-- Actual C3 and carrier completion produce the forbidden full first matrix
as a conclusion, starting from only the four enumerated invariant rows. -/
theorem star_first_matrix_form_from_invariant_rows (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (t : Point 4) (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => starRows false false false t j (q i))) :
    t 0 = 0 ∧ StarNonroot.FirstMatrixForm net (t 1) (t 2) (t 3) := by
  have hcover : ∀ i, ∃ j, starRows false false false t j i = 0 :=
    cover_of_normalized_frame (enumeratedRows net e) (starRows false false false t)
      id ρ q (fun j => ne_of_gt (hρ j)) hrows (enumerated_rows_cover net hnet e)
  have h0 := star_cover_omits_center false false false t hcover
  obtain ⟨z,hz,hinactive⟩ := outward_star_strictly_inactive t hsum h0 ht
  obtain ⟨P,s,hs,hW⟩ := completed_rows_of_inactive_frame net hnet
    (starRows false false false t) e ρ q hρ hrows 0 z hz hinactive
  refine ⟨h0,fun j => s (P.symm j),fun j => hs (P.symm j),
    P.symm,q.trans starInputPermutation.symm,?_⟩
  intro j i
  have hh := congrFun (hW (P.symm j)) i
  simp only [P.apply_symm_apply,Pi.smul_apply,smul_eq_mul] at hh
  have he := completed_star_rows_permute t h0 hsum (P.symm j)
    (starInputPermutation.symm (q i))
  rw [starInputPermutation.apply_symm_apply] at he
  change net.W₁ j i = s (P.symm j)*
    StarNonroot.firstRows (t 1) (t 2) (t 3) (P.symm j)
      (starInputPermutation.symm (q i))
  rw [← he]
  exact hh

/-- An actual arbitrary-bias width-(6,5) Max4 network cannot have three
outward-star invariant roots and one genuine nonroot invariant row.
The other two physical first rows are unrestricted in the hypotheses. -/
theorem network_outward_star_nonroot_excluded (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (t : Point 4) (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => starRows false false false t j (q i))) : False := by
  obtain ⟨h0,hform⟩ := star_first_matrix_form_from_invariant_rows net hnet
    e ρ q hρ t hsum ht hrows
  obtain ⟨h1,h2,h3⟩ := star_nonroot_leaf_nonzero t hsum ht h0
  exact StarNonroot.network_excluded_firstMatrixForm net (t 1) (t 2) (t 3)
    h1 h2 h3 hform hnet

#print axioms outward_star_strictly_inactive
#print axioms star_first_matrix_form_from_invariant_rows
#print axioms network_outward_star_nonroot_excluded
end MaxCaterpillar.Fiber.Count65.FrameTransport
