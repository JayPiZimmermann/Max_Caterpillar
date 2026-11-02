import MaxCaterpillar.Fiber.Count65.FrameTransport.ThreeRootBranches
import MaxCaterpillar.Fiber.Count65.FrameTransport.PathMatrixForm
import MaxCaterpillar.Fiber.Count65.FrameTransport.StarNetworkExclusion

/-! # Actual-network classification for a normalized three-root invariant frame

Only the four actual invariant rows are normalized in the hypotheses. Their
geometry, both physical carriers, and the entire first-matrix alternative are
derived from exactness. The reversed path is transported explicitly.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open MaxCaterpillar.Frontier BigOperators TwoRoots ThreeRoots

private def reversePathInputs : Equiv.Perm (Fin 4) where
  toFun := ![3,2,1,0]
  invFun := ![3,2,1,0]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private def swapPathEnds : Equiv.Perm (Fin 4) where
  toFun := ![2,1,0,3]
  invFun := ![2,1,0,3]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem reverse_path_rows (b c : ℝ) (j i : Fin 4) :
    ThreeRoots.pathRows true false false 0 b c (swapPathEnds j) (reversePathInputs i) =
      ThreeRoots.pathRows true true false (-c) (-b) 0 j i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [ThreeRoots.pathRows,pathFourth,swapPathEnds,reversePathInputs,Fin.ext_iff] <;>
    ring
  all_goals rfl

private theorem reverse_path_fourth (b c : ℝ) :
    (fun i => pathFourth 0 b c (reversePathInputs i)) = pathFourth (-c) (-b) 0 := by
  funext i
  fin_cases i <;> norm_num [pathFourth,reversePathInputs,Fin.ext_iff] <;> ring

private theorem ppm_matrix_form (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (a b c : ℝ)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true true false a b c j (q i)))
    (ht : Nonroot (pathFourth a b c)) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  have hrep : Represents (ThreeRoots.pathRows true true false a b c) :=
    represents_of_normalized_frame (enumeratedRows net e) _
      (enumerated_represents net hnet e) id ρ q hρ hrows
  have hc := path_ppm_last_zero a b c hrep
  subst c
  exact path_matrix_form_of_nonroot_frame net hnet e ρ q hρ a b hrows ht

private theorem pmm_matrix_form (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (a b c : ℝ)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => ThreeRoots.pathRows true false false a b c j (q i)))
    (ht : Nonroot (pathFourth a b c)) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  have hrep : Represents (ThreeRoots.pathRows true false false a b c) :=
    represents_of_normalized_frame (enumeratedRows net e) _
      (enumerated_represents net hnet e) id ρ q hρ hrows
  have ha := path_pmm_first_zero a b c hrep
  subst a
  let e' : Fin 4 ≃ invariantRows net := swapPathEnds.trans e
  let ρ' : Fin 4 → ℝ := fun j => ρ (swapPathEnds j)
  let q' : Equiv.Perm (Fin 4) := q.trans reversePathInputs.symm
  have hrows' : ∀ j, net.W₁ (e' j).val =
      ρ' j • (fun i => ThreeRoots.pathRows true true false (-c) (-b) 0 j (q' i)) := by
    intro j
    change net.W₁ (e (swapPathEnds j)).val = ρ (swapPathEnds j) •
      (fun i => ThreeRoots.pathRows true true false (-c) (-b) 0 j
        (reversePathInputs.symm (q i)))
    rw [hrows (swapPathEnds j)]
    funext i
    change ρ (swapPathEnds j) *
        ThreeRoots.pathRows true false false 0 b c (swapPathEnds j) (q i) =
      ρ (swapPathEnds j) * ThreeRoots.pathRows true true false (-c) (-b) 0 j
        (reversePathInputs.symm (q i))
    have he := reverse_path_rows b c j (reversePathInputs.symm (q i))
    rw [reversePathInputs.apply_symm_apply] at he
    exact congrArg (fun r : ℝ => ρ (swapPathEnds j) * r) he
  have ht' : Nonroot (pathFourth (-c) (-b) 0) := by
    rw [← reverse_path_fourth b c]
    exact nonroot_permute _ reversePathInputs ht
  exact path_matrix_form_of_nonroot_frame net hnet e' ρ' q'
    (fun j => hρ (swapPathEnds j)) (-c) (-b) hrows' ht'

private theorem threeRootRows_six (t : Point 4) :
    threeRootRows 6 t = pathWithFourth true false false t := by rfl

private theorem threeRootRows_eight (t : Point 4) :
    threeRootRows 8 t = pathWithFourth true true false t := by rfl

private theorem threeRootRows_thirteen (t : Point 4) :
    threeRootRows 13 t = starRows false false false t := by rfl

/-- Every actual normalized three-root invariant frame yields the full mixed
or star first-matrix form. The two noninvariant first rows, all biases and all
second-layer coefficients are unrestricted in the hypotheses. -/
theorem three_root_matrix_form_of_frame (net : Network 4 6 5)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (e : Fin 4 ≃ invariantRows net) (ρ : Fin 4 → ℝ)
    (q : Equiv.Perm (Fin 4)) (hρ : ∀ j, 0 < ρ j)
    (k : Fin 21) (t : Point 4) (hsum : ∑ i, t i = 0) (ht : Nonroot t)
    (hrows : ∀ j, net.W₁ (e j).val =
      ρ j • (fun i => threeRootRows k t j (q i))) :
    Mixed65.FirstMatrixForm net ∨ StarFirstMatrixForm net := by
  have hrep : Represents (threeRootRows k t) :=
    represents_of_normalized_frame (enumeratedRows net e) _
      (enumerated_represents net hnet e) id ρ q hρ hrows
  have hcover : ∀ i, ∃ j, threeRootRows k t j i = 0 :=
    cover_of_normalized_frame (enumeratedRows net e) _ id ρ q
      (fun j => ne_of_gt (hρ j)) hrows (enumerated_rows_cover net hnet e)
  have htpath : Nonroot (pathFourth (t 0) (t 0+t 1) (-t 3)) := by
    rw [← zero_sum_eq_pathFourth t hsum]
    exact ht
  rcases canonical_three_root_branch k t hsum ht hcover hrep with hk | hk | hk
  · subst k
    have hrows' : ∀ j, net.W₁ (e j).val = ρ j •
        (fun i => ThreeRoots.pathRows true false false (t 0) (t 0+t 1) (-t 3) j (q i)) := by
      simpa only [threeRootRows_six,pathWithFourth_eq true false false t hsum] using hrows
    exact pmm_matrix_form net hnet e ρ q hρ _ _ _ hrows' htpath
  · subst k
    have hrows' : ∀ j, net.W₁ (e j).val = ρ j •
        (fun i => ThreeRoots.pathRows true true false (t 0) (t 0+t 1) (-t 3) j (q i)) := by
      simpa only [threeRootRows_eight,pathWithFourth_eq true true false t hsum] using hrows
    exact ppm_matrix_form net hnet e ρ q hρ _ _ _ hrows' htpath
  · subst k
    apply False.elim
    apply network_outward_star_nonroot_excluded net hnet e ρ q hρ t hsum ht
    simpa only [threeRootRows_thirteen] using hrows

#print axioms three_root_matrix_form_of_frame
end MaxCaterpillar.Fiber.Count65.FrameTransport
