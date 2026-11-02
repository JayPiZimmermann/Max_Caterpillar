import MaxCaterpillar.Frontier.StarCertificate.StarRelabel
import MaxCaterpillar.Frontier.StarCertificate.StarLeafOrderTable

/-! # Actual leaf-permutation equivariance of the chamber-group function

Relabeling the four leaves permutes the 120 chambers while preserving the
four chain values. Consequently the Xi dictionary itself needs no leaf
symmetry hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- Extend a leaf permutation by fixing the actual star centre, coordinate 4. -/
def leafLift (e : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 5) where
  toFun := Fin.lastCases 4 (fun i => (e i).castSucc)
  invFun := Fin.lastCases 4 (fun i => (e.symm i).castSucc)
  left_inv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem leafLift_castSucc (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    leafLift e i.castSucc=(e i).castSucc := by simp [leafLift]

@[simp] theorem leafLift_last (e : Equiv.Perm (Fin 4)) : leafLift e 4=4 := by
  rfl

@[simp] theorem leafLift_symm (e : Equiv.Perm (Fin 4)) :
    (leafLift e).symm=leafLift e.symm := by
  ext i
  rfl

@[simp] theorem leafLift_symm_castSucc (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (leafLift e).symm i.castSucc=(e.symm i).castSucc := by
  change leafLift e.symm i.castSucc=(e.symm i).castSucc
  exact leafLift_castSucc e.symm i

/-- The leaves preceding the centre, defined directly from ordering positions.
This version is computable for the displayed chamber table. -/
def leavesBeforeCenter (pi : Equiv.Perm (Fin 5)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => ∃ a b : Fin 5,
    a.val<b.val ∧ pi a=i.castSucc ∧ pi b=4)

theorem leavesBeforeCenter_table (p : Fin 120) :
    leavesBeforeCenter (permutationEquiv p)=maskSet (centerBeforeMask p) := by
  ext i
  simp only [leavesBeforeCenter,maskSet,Finset.mem_filter,Finset.mem_univ,true_and,
    permutationEquiv_apply]
  exact (table_leavesBeforeCenter p i).symm

theorem leavesBeforeCenter_lift (e : Equiv.Perm (Fin 4)) (pi : Equiv.Perm (Fin 5)) :
    leavesBeforeCenter (leafLift e*pi)=(leavesBeforeCenter pi).map e.toEmbedding := by
  ext i
  simp only [Finset.mem_map_equiv,leavesBeforeCenter,Finset.mem_filter,
    Finset.mem_univ,true_and]
  change (∃ a b : Fin 5, a.val<b.val ∧ leafLift e (pi a)=i.castSucc ∧
    leafLift e (pi b)=4) ↔
    ∃ a b : Fin 5, a.val<b.val ∧ pi a=(e.symm i).castSucc ∧ pi b=4
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    refine ⟨a,b,hab,?_,?_⟩
    · apply (leafLift e).injective
      simpa using ha
    · apply (leafLift e).injective
      simpa using hb
  · rintro ⟨a,b,hab,ha,hb⟩
    refine ⟨a,b,hab,?_,?_⟩ <;> simp [ha,hb]

theorem starSetFunction_leaf_permute (e : Equiv.Perm (Fin 4))
    (v v' : Fin 4→ℝ) (B : Finset (Fin 5)) :
    starSetFunction (fun i => v (e i)) (fun i => v' (e i)) B=
      starSetFunction v v' (B.map (leafLift e).toEmbedding) := by
  unfold starSetFunction
  have hc : (4 : Fin 5)∈B.map (leafLift e).toEmbedding ↔ (4 : Fin 5)∈B := by simp
  by_cases hB : (4 : Fin 5)∈B
  · simp only [if_pos hB,if_pos (hc.mpr hB)]
    congr 1
    apply Fintype.sum_equiv e
    intro i
    have hi : (leafLift e).symm ((e i).castSucc)=i.castSucc := by
      rw [←leafLift_castSucc e i]
      exact (leafLift e).symm_apply_apply _
    simp only [Finset.mem_map_equiv]
    rw [hi]
  · simp only [if_neg hB,if_neg (fun h => hB (hc.mp h))]
    apply Fintype.sum_equiv e
    intro i
    have hi : (leafLift e).symm ((e i).castSucc)=i.castSucc := by
      rw [←leafLift_castSucc e i]
      exact (leafLift e).symm_apply_apply _
    simp only [Finset.mem_map_equiv]
    rw [hi]

theorem star_chain_leaf_permute (e : Equiv.Perm (Fin 4))
    (z : Fin 4→ℝ) (pi : Equiv.Perm (Fin 5)) :
    permutationFunctionChain (starSetFunction (fun i => z (e i)) (fun i => z (e i))) pi=
      permutationFunctionChain (starSetFunction z z) (leafLift e*pi) := by
  funext r
  unfold permutationFunctionChain
  rw [starSetFunction_leaf_permute]
  have hp := permutationPrefix_map (leafLift e).symm pi r
  simpa only [Equiv.symm_symm] using congrArg (starSetFunction z z) hp

theorem maskedGamma_eq_starChain (p : Fin 120) (z : Fin 4→ℝ) :
    maskedGamma 15 p z=starChain z z p := by
  have hm : mixed (maskSet (centerBeforeMask p)) z z=z := by
    funext i
    simp [mixed]
  rw [starChain_eq_maskedGamma,hm]

noncomputable def permutationPsi (P : Finset (Fin 4)) (z : Fin 4→ℝ) : ℝ :=
  ∑ pi : Equiv.Perm (Fin 5), if leavesBeforeCenter pi=P then
    starXi (permutationFunctionChain (starSetFunction z z) pi) else 0

theorem starPsi_eq_permutationPsi (P : Finset (Fin 4)) (z : Fin 4→ℝ) :
    starPsi P z=permutationPsi P z := by
  unfold starPsi permutationPsi
  rw [←sum_permutationTable]
  apply Finset.sum_congr rfl
  intro p _
  have hc : centerBeforeMask p=setMask P ↔
      leavesBeforeCenter (permutationEquiv p)=P := by
    rw [leavesBeforeCenter_table]
    constructor
    · intro h
      rw [h,maskSet_setMask]
    · intro h
      have he := congrArg setMask h
      simpa only [setMask_maskSet] using he
  simp only [hc,permutationFunctionChain_star_table,maskedGamma_eq_starChain]

/-- Exact S4 equivariance of the actual Xi chamber sum, for all real inputs. -/
theorem starPsi_leaf_permute (e : Equiv.Perm (Fin 4))
    (P : Finset (Fin 4)) (z : Fin 4→ℝ) :
    starPsi P (fun i => z (e i))=starPsi (P.map e.toEmbedding) z := by
  rw [starPsi_eq_permutationPsi,starPsi_eq_permutationPsi]
  unfold permutationPsi
  apply Fintype.sum_equiv (Equiv.mulLeft (leafLift e))
  intro pi
  change _ = if leavesBeforeCenter (leafLift e*pi)=P.map e.toEmbedding then
    starXi (permutationFunctionChain (starSetFunction z z) (leafLift e*pi)) else 0
  rw [leavesBeforeCenter_lift,star_chain_leaf_permute]
  have hc : (leavesBeforeCenter pi).map e.toEmbedding=P.map e.toEmbedding ↔
      leavesBeforeCenter pi=P := (e.finsetCongr).injective.eq_iff
  simp only [hc]

#print axioms starPsi_leaf_permute
end MaxCaterpillar.Frontier.StarCertificate
