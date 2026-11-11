import MaxCaterpillar.Frontier.Basic
import Mathlib.Analysis.Convex.Jensen

/-! Every input lies in a simplex of points with all but one input tied
at the maximum. Convexity therefore propagates nonpositivity on those
contacts to the whole input space. -/

set_option autoImplicit false

namespace MaxCaterpillar.Max5Optimal.ConvexCores
open BigOperators Frontier

variable {N : ℕ}

def contactVertex (M s : ℝ) (i : Fin N) : Point N :=
  fun j => M - if j = i then s else 0

@[simp] theorem contactVertex_self (M s : ℝ) (i : Fin N) :
    contactVertex M s i i = M - s := by simp [contactVertex]

@[simp] theorem contactVertex_other (M s : ℝ) (i j : Fin N) (h : j ≠ i) :
    contactVertex M s i j = M := by simp [contactVertex, h]

/-- The barycentric weights are strictly positive, not merely nonnegative. -/
theorem exists_contact_barycentric [NeZero N] (x : Point N) :
    ∃ M s : ℝ, ∃ w : Fin N → ℝ,
      0 < s ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
        (∑ i, w i • contactVertex M s i) = x := by
  classical
  let M : ℝ := Maximum N x + 1
  let gap : Fin N → ℝ := fun i => M - x i
  have hgap : ∀ i, 0 < gap i := by
    intro i
    dsimp [gap, M]
    linarith [le_Maximum x i]
  let s : ℝ := ∑ i, gap i
  have hs : 0 < s :=
    Finset.sum_pos (fun i _ => hgap i) Finset.univ_nonempty
  let w : Fin N → ℝ := fun i => gap i / s
  have hw : ∀ i, 0 < w i := fun i => div_pos (hgap i) hs
  have hw_sum : (∑ i, w i) = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hs.ne'
  refine ⟨M, s, w, hs, hw, hw_sum, ?_⟩
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, contactVertex, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul]
  have hdelta : (∑ i, w i * (if j = i then s else 0)) = w j * s := by
    simp [mul_ite]
  rw [hdelta]
  dsimp [w, gap]
  rw [div_mul_cancel _ hs.ne']
  ring

/-- A convex function bounded by zero at every translated contact vertex
is bounded by zero everywhere. No homogeneity is assumed. -/
theorem convex_nonpos_of_contact_nonpos [NeZero N] {f : Point N → ℝ}
    (hf : ConvexOn ℝ Set.univ f)
    (hz : ∀ M s : ℝ, 0 < s → ∀ i : Fin N, f (contactVertex M s i) ≤ 0) :
    ∀ x, f x ≤ 0 := by
  classical
  intro x
  obtain ⟨M, s, w, hs, hw, hw_sum, hsum⟩ := exists_contact_barycentric x
  have hj := hf.map_sum_le (t := Finset.univ) (w := w)
    (p := fun i => contactVertex M s i)
    (fun i _ => (hw i).le) hw_sum (fun _ _ => Set.mem_univ _)
  rw [hsum] at hj
  apply hj.trans
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (hz M s hs i)

theorem convex_nonpos_of_contact_zeros [NeZero N] {f : Point N → ℝ}
    (hf : ConvexOn ℝ Set.univ f)
    (hz : ∀ M s : ℝ, 0 < s → ∀ i : Fin N, f (contactVertex M s i) = 0) :
    ∀ x, f x ≤ 0 :=
  convex_nonpos_of_contact_nonpos hf (fun M s hs i => (hz M s hs i).le)

#check @exists_contact_barycentric
#check @convex_nonpos_of_contact_zeros
#print axioms exists_contact_barycentric
#print axioms convex_nonpos_of_contact_nonpos
#print axioms convex_nonpos_of_contact_zeros

end MaxCaterpillar.Max5Optimal.ConvexCores
