import MaxCaterpillar.Frontier.StarCertificate.StarRelabel

/-! # Primitive stars with arbitrary centres and real slopes

The first definition is the native erased-centre formula. Its identification
with the centre-4 model is proved below, rather than assumed as a model class.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

/-- The primitive star set function, with no restriction on the centre or slopes. -/
noncomputable def starAtSetFunction (c : Fin 5) (v v' : Fin 5 → ℝ)
    (B : Finset (Fin 5)) : ℝ :=
  if c ∈ B then
    -(∑ i in (Finset.univ : Finset (Fin 5)).erase c,if i ∉ B then v' i else 0)
  else ∑ i in (Finset.univ : Finset (Fin 5)).erase c,if i ∈ B then v i else 0

/-- Pulling a finite set through an inverse permutation transports membership. -/
theorem mem_map_symm_iff (e : Equiv.Perm (Fin 5)) (B : Finset (Fin 5)) (i : Fin 5) :
    i ∈ B.map e.symm.toEmbedding ↔ e i ∈ B := by
  constructor
  · intro hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hi
    change e.symm j=i at hji
    have hje : j=e i := by
      calc j=e (e.symm j) := (e.apply_symm_apply j).symm
           _=e i := by rw [hji]
    exact hje ▸ hj
  · intro hi
    exact Finset.mem_map.mpr ⟨e i,hi,e.symm_apply_apply i⟩

/-- Any permutation taking coordinate 4 to the centre enumerates the four
remaining coordinates by its castSucc images. -/
theorem sum_erase_center (e : Equiv.Perm (Fin 5)) (c : Fin 5)
    (he : e 4=c) (f : Fin 5 → ℝ) :
    (∑ i in (Finset.univ : Finset (Fin 5)).erase c,f i) =
      ∑ i : Fin 4,f (e i.castSucc) := by
  have hsum :
      (∑ i in (Finset.univ : Finset (Fin 5)).erase c,f i)+f c =
        (∑ i : Fin 4,f (e i.castSucc))+f c := by
    calc
      _ = ∑ i : Fin 5,f i := Finset.sum_erase_add _ f (Finset.mem_univ c)
      _ = ∑ i : Fin 5,f (e i) :=
        (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
      _ = _ := by
        rw [Fin.sum_univ_castSucc,show (Fin.last 4 : Fin 5)=4 by decide,he]
  exact add_right_cancel hsum

/-- A permutation taking coordinate 4 to c transports the native formula. -/
theorem starAtSetFunction_eq_relabel_of_center (e : Equiv.Perm (Fin 5))
    (c : Fin 5) (he : e 4=c) (v v' : Fin 5 → ℝ) :
    starAtSetFunction c v v' =
      relabelSetFunction
        (starSetFunction
          (fun i : Fin 4 => v (e i.castSucc))
          (fun i : Fin 4 => v' (e i.castSucc))) e := by
  funext B
  have hc : ((4 : Fin 5) ∈ B.map e.symm.toEmbedding) ↔ c ∈ B := by
    rw [mem_map_symm_iff,he]
  change (if c ∈ B then
      -(∑ i in (Finset.univ : Finset (Fin 5)).erase c,if i ∉ B then v' i else 0)
    else ∑ i in (Finset.univ : Finset (Fin 5)).erase c,if i ∈ B then v i else 0) =
    (if (4 : Fin 5) ∈ B.map e.symm.toEmbedding then
      -(∑ i : Fin 4,if i.castSucc ∉ B.map e.symm.toEmbedding then v' (e i.castSucc) else 0)
    else ∑ i : Fin 4,if i.castSucc ∈ B.map e.symm.toEmbedding then v (e i.castSucc) else 0)
  by_cases hcB : c ∈ B
  · rw [if_pos hcB,if_pos (hc.mpr hcB)]
    congr 1
    rw [sum_erase_center e c he]
    apply Finset.sum_congr rfl
    intro i _
    have hi := mem_map_symm_iff e B i.castSucc
    by_cases hm : e i.castSucc ∈ B
    · have hm' := hi.mpr hm
      rw [if_neg (not_not_intro hm),if_neg (not_not_intro hm')]
    · have hm' : i.castSucc ∉ B.map e.symm.toEmbedding := fun h => hm (hi.mp h)
      rw [if_pos hm,if_pos hm']
  · rw [if_neg hcB,if_neg (fun h => hcB (hc.mp h))]
    rw [sum_erase_center e c he]
    apply Finset.sum_congr rfl
    intro i _
    have hi := mem_map_symm_iff e B i.castSucc
    by_cases hm : e i.castSucc ∈ B
    · have hm' := hi.mpr hm
      rw [if_pos hm,if_pos hm']
    · have hm' : i.castSucc ∉ B.map e.symm.toEmbedding := fun h => hm (hi.mp h)
      rw [if_neg hm,if_neg hm']

/-- The primitive arbitrary-centre star is exactly the stated swap of the
centre-4 model. No relabeling hypothesis is imposed on the primitive star. -/
theorem starAtSetFunction_eq_relabel (c : Fin 5) (v v' : Fin 5 → ℝ) :
    starAtSetFunction c v v' =
      relabelSetFunction
        (starSetFunction
          (fun i : Fin 4 => v ((Equiv.swap (4 : Fin 5) c) i.castSucc))
          (fun i : Fin 4 => v' ((Equiv.swap (4 : Fin 5) c) i.castSucc)))
        (Equiv.swap (4 : Fin 5) c) :=
  starAtSetFunction_eq_relabel_of_center (Equiv.swap 4 c) c
    (Equiv.swap_apply_left _ _) v v'

/-- A universal coefficient certificate implies the Xi identity for every
primitive star centre and every real slope vector, including all degeneracies. -/
theorem starAt_permutation_sum_of_coefficients
    (hcoeff : ∀ (z : Fin 4 → ℝ) (t : Fin 80),
      evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z=0)
    (c : Fin 5) (v v' : Fin 5 → ℝ) :
    (∑ pi : Equiv.Perm (Fin 5),starXi
      (permutationFunctionChain (starAtSetFunction c v v') pi))=0 := by
  rw [starAtSetFunction_eq_relabel]
  exact star_permutation_relabel_sum_of_coefficients hcoeff _ _ _

#print axioms sum_erase_center
#print axioms starAtSetFunction_eq_relabel
#print axioms starAt_permutation_sum_of_coefficients
end MaxCaterpillar.Frontier.StarCertificate
