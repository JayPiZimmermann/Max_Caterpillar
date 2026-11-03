import research.sN.max5_optimal_20261103.lower.triple_contact.TripleContact
import MaxCaterpillar.Frontier.Constructions

/-! Unit scale of a comparator in a specific exact Max4 decomposition.
The second outer fold is retained; it is only its core that is locally
affine at the chosen three-way top tie. No global shallow claim is made. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.UnitScale
open BigOperators Frontier TripleContact

/-- A nonzero scalar multiple of a maximum cannot have a locally linear
odd part at a three-way top tie. -/
theorem scalar_eq_zero_of_locOddLin_max {N : ℕ} [NeZero N]
    (s : ℝ) (q : Point N) (I : Finset (Fin N)) (hI : 3≤I.card)
    (hq0 : ∀ i ∈ I, q i=0) (hq1 : ∀ i ∉ I, q i≤-1)
    (hf : LocOddLin (fun x => s*Maximum N x) q) : s=0 := by
  by_contra hs
  apply not_locOddLin_max q I hI hq0 hq1
  apply (hf.const_mul s⁻¹).congr
  intro x
  rw [←mul_assoc,inv_mul_cancel hs,one_mul]

lemma locAff_coordinate {N : ℕ} (i : Fin N) (q : Point N) :
    LocAff (fun x => x i) q :=
  (locAff_lin (unitVec i) q).congr fun x => by simp [lin,unitVec]

lemma locAff_coordinate_difference {N : ℕ} (i j : Fin N) (q : Point N) :
    LocAff (fun x => x i-x j) q := by
  apply ((locAff_coordinate i q).add ((locAff_coordinate j q).const_mul (-1))).congr
  intro x
  ring

lemma locOddLin_pair_max {N : ℕ} (i j : Fin N) (q : Point N) :
    LocOddLin (fun x => max (x i) (x j)) q := by
  apply (((locAff_coordinate_difference i j q).relu_locOddLin).add
    (locAff_coordinate j q).locOddLin).congr
  intro x
  rw [relu_sub_add,max_comm]

/-- Exact pair-comparator identity, valid also at scale zero. -/
lemma scaled_pair_comparator (scale : ℝ) (hscale : 0≤scale) (x : Point 4) :
    relu (scale*(max (x 0) (x 1)-max (x 2) (x 3)))=
      scale*(Maximum 4 x-max (x 2) (x 3)) := by
  have hm : relu (scale*(max (x 0) (x 1)-max (x 2) (x 3)))=
      scale*relu (max (x 0) (x 1)-max (x 2) (x 3)) := by
    unfold relu
    rw [mul_max_of_nonneg _ _ hscale,mul_zero]
  rw [hm]
  congr 1
  have h := relu_sub_add (max (x 2) (x 3)) (max (x 0) (x 1))
  rw [max_comm (max (x 2) (x 3)) (max (x 0) (x 1)),←Maximum_four] at h
  linarith only [h]

/-- In the specified exact Max4 representation, a nonnegative scaled
pair-comparator fold has scale one. The other core has an arbitrary affine
head and one first-layer comparison hinge on coordinates 0,1. -/
theorem unit_comparator_scale {mR : ℕ}
    (aR : Point 4) (bR : ℝ) (AR : Fin mR → Point 4) (βR cR : Fin mR → ℝ)
    (aH : Point 4) (bH cH scale : ℝ) (hscale : 0≤scale)
    (heq : ∀ x : Point 4,
      shallow aR bR AR βR cR x+
      relu (scale*(max (x 0) (x 1)-max (x 2) (x 3)))+
      relu (lin aH x+bH+cH*relu (x 0-x 1))=Maximum 4 x) : scale=1 := by
  let q : Point 4 := -unitVec 1
  have h01 : (q 0-q 1)≠0 := by norm_num [q,unitVec]
  have hH : LocAff (fun x => lin aH x+bH+cH*relu (x 0-x 1)) q :=
    ((locAff_lin aH q).add (locAff_const bH q)).add
      (((locAff_coordinate_difference 0 1 q).reluComp h01).const_mul cH)
  have hR := (shallow_locOddLin aR bR AR βR cR q).add
    ((locOddLin_pair_max 2 3 q).const_mul (-scale))
  have hs : LocOddLin (fun x => (1-scale)*Maximum 4 x) q := by
    apply (hR.add hH.relu_locOddLin).congr
    intro x
    have h := heq x
    rw [scaled_pair_comparator scale hscale x] at h
    linear_combination h
  have hz : 1-scale=0 := by
    apply scalar_eq_zero_of_locOddLin_max (1-scale) q (Finset.univ.erase 1)
      (by simp) (fun i hi => ?_) (fun i hi => ?_) hs
    · simp [q,unitVec,Finset.ne_of_mem_erase hi]
    · have hi1 : i=1 := by simpa using hi
      subst i
      norm_num [q,unitVec]
  linarith only [hz]

#check @scalar_eq_zero_of_locOddLin_max
#print axioms scalar_eq_zero_of_locOddLin_max
#check @unit_comparator_scale
#print axioms unit_comparator_scale
end MaxCaterpillar.Max5Optimal.UnitScale
