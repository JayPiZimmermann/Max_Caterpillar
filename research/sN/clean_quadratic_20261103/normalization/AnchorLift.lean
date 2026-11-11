import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.TiedMaximum
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Support

/-! Coordinate localization with a lift preserving the diagonal. -/
set_option autoImplicit false
namespace MaxCaterpillar.CleanQuadratic.Normalization
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N m : ℕ}

/-- Selected coordinates carry the requested direction; every outside
coordinate carries one selected anchor value. -/
def anchorLift (e : Fin m ↪ Fin N) (a : Fin m) (x : Point m) : Point N :=
  lift e (x - diag (x a)) + diag (x a)

@[simp] theorem anchorLift_selected (e : Fin m ↪ Fin N) (a i : Fin m)
    (x : Point m) : anchorLift e a x (e i) = x i := by
  simp only [anchorLift,Pi.add_apply,lift_selected,Pi.sub_apply,diag]
  ring

theorem anchorLift_outside (e : Fin m ↪ Fin N) (a : Fin m) (x : Point m)
    (i : Fin N) (hi : i ∉ Finset.univ.image e) : anchorLift e a x i = x a := by
  simp only [anchorLift,Pi.add_apply,lift_outside e _ i hi,diag,zero_add]

@[simp] theorem anchorLift_diag (e : Fin m ↪ Fin N) (a : Fin m) (t : ℝ) :
    anchorLift e a (diag t) = diag t := by
  classical
  ext i
  by_cases hi : i ∈ Finset.univ.image e
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact anchorLift_selected e a j _
  · exact anchorLift_outside e a _ i hi

/-- Exact for every positive step, rather than merely sufficiently small ones. -/
theorem maximum_anchorLift [NeZero N] [NeZero m]
    (e : Fin m ↪ Fin N) (a : Fin m) (q : Point N)
    (hq : ∀ i, q (e i) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0)
    (x : Point m) (ε : ℝ) (hε : 0 < ε) :
    Maximum N (q + ε • anchorLift e a x) = ε * Maximum m x := by
  classical
  obtain ⟨i,hi⟩ := exists_eq_Maximum x
  apply Maximum_eq_of _ _ (e i)
  · rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hq i,anchorLift_selected,zero_add,←hi]
  · intro j
    by_cases hj : j ∈ Finset.univ.image e
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
      rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hq b,anchorLift_selected,zero_add]
      exact mul_le_mul_of_nonneg_left (le_Maximum x b) hε.le
    · rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,anchorLift_outside e a x j hj]
      have hm := mul_le_mul_of_nonneg_left (le_Maximum x a) hε.le
      linarith only [hneg j hj,hm]

/-- Pullback of a linear form along the anchor lift. -/
def anchorRestrict (e : Fin m ↪ Fin N) (a : Fin m) (v : Point N) : Point m :=
  restrict e v + ((∑ i,v i) - ∑ i,restrict e v i) • unitVec a

theorem lin_anchorLift (e : Fin m ↪ Fin N) (a : Fin m)
    (v : Point N) (x : Point m) :
    lin v (anchorLift e a x) = lin (anchorRestrict e a v) x := by
  rw [anchorLift,lin_add_right,lin_lift,lin_sub_right,lin_diag,lin_diag,
    anchorRestrict,lin_add_left,lin_smul_left]
  have hunit : lin (unitVec a) x = x a := by
    classical
    simp [lin,unitVec]
  rw [hunit]
  ring

/-- Pullback preserves the coordinate sum, including for arbitrary linear heads. -/
theorem sum_anchorRestrict (e : Fin m ↪ Fin N) (a : Fin m) (v : Point N) :
    (∑ i,anchorRestrict e a v i) = ∑ i,v i := by
  have hh := lin_anchorLift e a v (diag 1)
  rw [anchorLift_diag,lin_diag,lin_diag] at hh
  simpa only [one_mul] using hh.symm

theorem anchorRestrict_of_support (e : Fin m ↪ Fin N) (a : Fin m) (v : Point N)
    (hv : rowSupport v ⊆ Finset.univ.image e) :
    anchorRestrict e a v = restrict e v := by
  rw [anchorRestrict,sum_restrict_of_subset e v hv,sub_self,zero_smul,add_zero]

@[simp] theorem anchorRestrict_zero (e : Fin m ↪ Fin N) (a : Fin m) :
    anchorRestrict e a (0 : Point N) = 0 := by
  ext i
  simp [anchorRestrict,restrict]

#check @maximum_anchorLift
#check @sum_anchorRestrict
#print axioms anchorLift_diag
#print axioms maximum_anchorLift
#print axioms lin_anchorLift
#print axioms sum_anchorRestrict
end MaxCaterpillar.CleanQuadratic.Normalization
