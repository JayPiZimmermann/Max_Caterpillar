import MaxCaterpillar.Fiber.Count65.FrameTransport.EnumeratedRepresentation
import MaxCaterpillar.Fiber.Count65.FrameTransport.FeatureNormalization
import MaxCaterpillar.Fiber.Count65.FrameTransport.CarrierAssembly
import MaxCaterpillar.Fiber.Count65.FrameTransport.ThreeRootBranches
import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! # Actual path invariant rows force a full mixed or star first matrix

The coordinate carriers and the six-row permutation are derived from
exactness. No equation for the two noninvariant first rows is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open Frontier TwoRoots ThreeRoots

/-- Only the fourth invariant direction changes its positive normalization. -/
noncomputable def fourthScale (c : ℝ) (j : Fin 6) : ℝ := if j.val = 3 then c else 1

lemma fourthScale_pos (c : ℝ) (hc : 0 < c) (j : Fin 6) : 0 < fourthScale c j := by
  by_cases hj : j.val = 3 <;> simp [fourthScale,hj,hc]

lemma completed_path_rows (a b : ℝ) :
    completedRows (ThreeRoots.pathRows true true false a b 0) 2 =
      ![![1,-1,0,0],![0,1,-1,0],![0,0,-1,1],![a,b-a,-b,0],
        ![0,0,1,0],![0,0,-1,0]] := by
  let T : Fin 6 → Point 4 :=
    ![![1,-1,0,0],![0,1,-1,0],![0,0,-1,1],![a,b-a,-b,0],
      ![0,0,1,0],![0,0,-1,0]]
  change completedRows (ThreeRoots.pathRows true true false a b 0) 2 = T
  funext j
  refine Fin.addCases (m := 4) (n := 2)
    (motive := fun j : Fin 6 =>
      completedRows (ThreeRoots.pathRows true true false a b 0) 2 j = T j)
    (fun j => ?_) (fun j => ?_) j
  · simp only [completedRows,Fin.append_left]
    fin_cases j <;> funext i <;> fin_cases i <;>
      norm_num [ThreeRoots.pathRows,pathFourth,T,Fin.castAdd,Fin.castLE,Fin.ext_iff]
  · simp only [completedRows,Fin.append_right]
    fin_cases j <;> funext i <;> fin_cases i <;>
      norm_num [unitVec,T,Fin.natAdd,Fin.ext_iff]

lemma completed_path_mixed_identity (a b : ℝ) (hb : b < 0)
    (j : Fin 6) (i : Fin 4) :
    completedRows (ThreeRoots.pathRows true true false a b 0) 2 j i =
      fourthScale (-b) j * Mixed65.firstRows (a/(-b)) j i := by
  rw [completed_path_rows]
  have hnb : -b ≠ 0 := ne_of_gt (neg_pos.mpr hb)
  fin_cases j <;> fin_cases i <;>
    norm_num [fourthScale,Mixed65.firstRows,Fin.ext_iff]
  all_goals field_simp [hnb,hb.ne] <;> ring

lemma completed_path_star_identity (a b : ℝ) (ha : 0 < a)
    (j : Fin 6) (i : Fin 4) :
    completedRows (ThreeRoots.pathRows true true false a b 0) 2 j i =
      fourthScale a j * Star65.firstRows (b/a) j i := by
  rw [completed_path_rows]
  fin_cases j <;> fin_cases i <;>
    norm_num [fourthScale,Star65.firstRows,Fin.ext_iff]
  all_goals field_simp [ha.ne'] <;> ring

/-- The mixed full matrix follows from only the invariant-row equations.
The remaining rows are forced to be the signed coordinate carriers. -/
theorem path_mixed_matrix_form (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (a b : ℝ) (ha : 0 < a) (hb : b < 0)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true true false a b 0 j (q i))) :
    Mixed65.FirstMatrixForm net := by
  obtain ⟨z,hz,hneg⟩ := canonical_path_strict_inactive a b ha
  obtain ⟨P,s,hs,hW⟩ := completed_rows_of_inactive_frame net hnet
    (ThreeRoots.pathRows true true false a b 0) e ρ q hρ hrows 2 z hz hneg
  refine ⟨a/(-b),div_pos ha (neg_pos.mpr hb),
    (fun j => s (P.symm j) * fourthScale (-b) (P.symm j)),
    (fun j => mul_pos (hs _) (fourthScale_pos _ (neg_pos.mpr hb) _)),P.symm,q,?_⟩
  intro j i
  calc
    net.W₁ j i = s (P.symm j) *
        completedRows (ThreeRoots.pathRows true true false a b 0) 2 (P.symm j) (q i) := by
      have hh := congrFun (hW (P.symm j)) i
      simpa only [P.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hh
    _ = (s (P.symm j) * fourthScale (-b) (P.symm j)) *
        Mixed65.firstRows (a/(-b)) (P.symm j) (q i) := by
      rw [completed_path_mixed_identity a b hb]
      ring

/-- Positive path coefficients, including the endpoint b=a, give the star
full first matrix. All biases and second-layer parameters stay arbitrary. -/
theorem path_star_matrix_form (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true true false a b 0 j (q i))) :
    StarFirstMatrixForm net := by
  obtain ⟨z,hz,hneg⟩ := canonical_path_strict_inactive a b ha
  obtain ⟨P,s,hs,hW⟩ := completed_rows_of_inactive_frame net hnet
    (ThreeRoots.pathRows true true false a b 0) e ρ q hρ hrows 2 z hz hneg
  refine ⟨b/a,div_pos hb ha,(div_le_one ha).mpr hba,
    (fun j => s (P.symm j) * fourthScale a (P.symm j)),
    (fun j => mul_pos (hs _) (fourthScale_pos _ ha _)),P.symm,q,?_⟩
  intro j i
  calc
    net.W₁ j i = s (P.symm j) *
        completedRows (ThreeRoots.pathRows true true false a b 0) 2 (P.symm j) (q i) := by
      have hh := congrFun (hW (P.symm j)) i
      simpa only [P.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hh
    _ = (s (P.symm j) * fourthScale a (P.symm j)) *
        Star65.firstRows (b/a) (P.symm j) (q i) := by
      rw [completed_path_star_identity a b ha]
      ring

/-- The strict mixed/star alternatives are a conclusion of the actual
maximum equation and four invariant rows. No full first-matrix hypothesis. -/
theorem path_matrix_form_of_nonroot_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (a b : ℝ)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true true false a b 0 j (q i)))
    (ht : Nonroot (pathFourth a b 0)) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  have hrep : Represents (ThreeRoots.pathRows true true false a b 0) :=
    represents_of_normalized_frame (enumeratedRows net e) _
      (enumerated_represents net hnet e) (fun j => j) ρ q hρ hrows
  obtain ⟨ha,hbne,hba⟩ := path_ppm_nonroot_coefficient_bounds a b hrep ht
  rcases lt_or_gt_of_ne hbne with hb | hb
  · exact Or.inl (path_mixed_matrix_form net hnet e ρ q hρ a b ha hb hrows)
  · exact Or.inr (path_star_matrix_form net hnet e ρ q hρ a b ha hb hba.le hrows)

/-- The all-root star endpoint needs no nonroot hypothesis. -/
theorem path_endpoint_star_matrix_form (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true true false 1 1 0 j (q i))) :
    StarFirstMatrixForm net :=
  path_star_matrix_form net hnet e ρ q hρ 1 1 (by norm_num) (by norm_num) le_rfl hrows

#print axioms path_matrix_form_of_nonroot_frame
#print axioms path_endpoint_star_matrix_form
end MaxCaterpillar.Fiber.Count65.FrameTransport
