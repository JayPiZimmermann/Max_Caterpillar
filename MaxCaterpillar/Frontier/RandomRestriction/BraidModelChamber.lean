import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model
import MaxCaterpillar.Frontier.StarCertificate.MobiusQuadratic
import MaxCaterpillar.Frontier.StarCertificate.StarPermutations

/-! # Actual Boolean-prefix chamber inputs and braid-hinge reconstruction -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open BigOperators MaxCaterpillar.Frontier.StarCertificate

noncomputable def booleanPoint (B : Finset (Fin 5)) : Point 5 :=
  fun i => booleanCoordinate i B

noncomputable def chamberPoint (p : Fin 120) (d : Point 4) : Point 5 :=
  ∑ r : Fin 4, d r • booleanPoint (chamberPrefix p r)

theorem chamberPoint_apply (p : Fin 120) (d : Point 4) (i : Fin 5) :
    chamberPoint p d i=∑ r : Fin 4, d r*booleanCoordinate i (chamberPrefix p r) := by
  simp only [chamberPoint,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,booleanPoint]

theorem lin_chamberPoint (a : Point 5) (p : Fin 120) (d : Point 4) :
    lin a (chamberPoint p d)=
      ∑ r : Fin 4, d r*lin a (booleanPoint (chamberPrefix p r)) := by
  rw [chamberPoint,lin_sum_right]
  simp only [lin_smul_right]

theorem mem_permutationPrefix_iff (pi : Equiv.Perm (Fin 5)) (a : Fin 5) (r : Fin 4) :
    a∈permutationPrefix pi r ↔ (pi.symm a).val≤r.val := by
  simp only [permutationPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,hk,hka⟩
    rw [←hka,pi.symm_apply_apply]
    exact hk
  · intro h
    exact ⟨pi.symm a,h,pi.apply_symm_apply a⟩

theorem mem_chamberPrefix_iff (p : Fin 120) (a : Fin 5) (r : Fin 4) :
    a∈chamberPrefix p r ↔ ((permutationEquiv p).symm a).val≤r.val :=
  mem_permutationPrefix_iff (permutationEquiv p) a r

theorem prefix_coordinate_order (p : Fin 120) (a b : Fin 5)
    (hab : ((permutationEquiv p).symm a).val≤((permutationEquiv p).symm b).val)
    (r : Fin 4) :
    booleanCoordinate b (chamberPrefix p r)≤booleanCoordinate a (chamberPrefix p r) := by
  classical
  by_cases hb : b∈chamberPrefix p r
  · have ha : a∈chamberPrefix p r := (mem_chamberPrefix_iff p a r).mpr
      (hab.trans ((mem_chamberPrefix_iff p b r).mp hb))
    simp [booleanCoordinate,ha,hb]
  · by_cases ha : a∈chamberPrefix p r <;> simp [booleanCoordinate,ha,hb]

theorem pair_prefix_one_sign (p : Fin 120) (a b : Fin 5) (t : ℝ) :
    (∀ r : Fin 4, 0≤t*(booleanCoordinate a (chamberPrefix p r)-
      booleanCoordinate b (chamberPrefix p r))) ∨
    (∀ r : Fin 4, t*(booleanCoordinate a (chamberPrefix p r)-
      booleanCoordinate b (chamberPrefix p r))≤0) := by
  rcases le_total ((permutationEquiv p).symm a).val
      ((permutationEquiv p).symm b).val with hab | hba
  · by_cases ht : 0≤t
    · left
      intro r
      exact mul_nonneg ht (sub_nonneg.mpr (prefix_coordinate_order p a b hab r))
    · right
      intro r
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht)
        (sub_nonneg.mpr (prefix_coordinate_order p a b hab r))
  · by_cases ht : 0≤t
    · right
      intro r
      exact mul_nonpos_of_nonneg_of_nonpos ht
        (sub_nonpos.mpr (prefix_coordinate_order p b a hba r))
    · left
      intro r
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ht)
        (sub_nonpos.mpr (prefix_coordinate_order p b a hba r))

theorem relu_weighted_sum_of_one_sign {ι : Type*} [Fintype ι]
    (c f : ι→ℝ) (hc : ∀ i, 0≤c i)
    (hf : (∀ i, 0≤f i) ∨ (∀ i, f i≤0)) :
    relu (∑ i, c i*f i)=∑ i, c i*relu (f i) := by
  rcases hf with hf | hf
  · rw [relu_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (hf i)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [relu_of_nonneg (hf i)]
  · rw [relu_of_nonpos (Finset.sum_nonpos
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hc i) (hf i)))]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [relu_of_nonpos (hf i),mul_zero]

theorem relu_pair_chamber (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r)
    (a b : Fin 5) (t : ℝ) :
    relu (t*(chamberPoint p d a-chamberPoint p d b))=
      ∑ r : Fin 4, d r*relu (t*(booleanCoordinate a (chamberPrefix p r)-
        booleanCoordinate b (chamberPrefix p r))) := by
  have he : t*(chamberPoint p d a-chamberPoint p d b)=
      ∑ r : Fin 4, d r*(t*(booleanCoordinate a (chamberPrefix p r)-
        booleanCoordinate b (chamberPrefix p r))) := by
    rw [chamberPoint_apply,chamberPoint_apply,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he]
  exact relu_weighted_sum_of_one_sign d _ hd (pair_prefix_one_sign p a b t)

theorem chamber_linear_combination {ι : Type*} [Fintype ι]
    (f : ι→Point 5→ℝ) (c : ι→ℝ) (p : Fin 120) (d : Point 4)
    (hf : ∀ j, f j (chamberPoint p d)=
      ∑ r : Fin 4, d r*f j (booleanPoint (chamberPrefix p r))) :
    (∑ j, c j*f j (chamberPoint p d))=
      ∑ r : Fin 4, d r*(∑ j, c j*f j (booleanPoint (chamberPrefix p r))) := by
  simp_rw [hf,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A positive-gap chamber input really has maximum equal to the sum of
its four gaps. The lowest coordinate is anchored at zero. -/
theorem maximum_chamberPoint (p : Fin 120) (d : Point 4) (hd : ∀ r, 0≤d r) :
    Maximum 5 (chamberPoint p d)=∑ r : Fin 4, d r := by
  classical
  apply Maximum_eq_of _ _ (permutationTable p 0)
  · rw [chamberPoint_apply]
    apply Finset.sum_congr rfl
    intro r _
    have hi : permutationTable p 0∈chamberPrefix p r := by
      simp only [chamberPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨0,Nat.zero_le _,rfl⟩
    simp [booleanCoordinate,hi]
  · intro i
    rw [chamberPoint_apply]
    apply Finset.sum_le_sum
    intro r _
    by_cases hi : i∈chamberPrefix p r <;> simp [booleanCoordinate,hi,hd r]

#print axioms relu_pair_chamber
#print axioms maximum_chamberPoint
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
