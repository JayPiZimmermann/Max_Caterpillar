import MaxCaterpillar.Fiber.Count65.SectorQuotient.FirstNormalization
import MaxCaterpillar.Fiber.Count65.SectorSeparation.StarClosed
import MaxCaterpillar.Fiber.Count65.Star.ActualLabelsNormalization

/-! Explicit continuous first-frame normalization on the actual positively
scaled star sector, including the endpoint parameter one. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

open SectorSeparation

@[simp] private theorem star_vec6_three {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (3 : Fin 6) = d := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (0 : Fin 3)))) = d
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem star_vec6_four {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (4 : Fin 6) = e := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))) = e
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem star_vec6_five {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := by
  change ![a,b,c,d,e,f] (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))) = f
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]

@[simp] private theorem star_vec4_three {α : Type*} (a b c d : α) :
    ![a,b,c,d] (3 : Fin 4) = d := by
  change ![a,b,c,d] (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) = d
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]


abbrev StarDomain := {net : ExactFiber 4 6 5 // net ∈ StarClosed.labeled}

noncomputable def starParameter (n : StarDomain) : ℝ :=
  StarClosed.branch n.val.val / StarClosed.rowScale n.val.val 3

noncomputable def starScales (n : StarDomain) : Fin 6 → ℝ :=
  StarClosed.rowScale n.val.val

lemma star_scale_pos (n : StarDomain) (j : Fin 6) : 0 < starScales n j := by
  obtain ⟨r,_hr,_hr1,s,hs,hw⟩ := n.property
  have hscale : StarClosed.rowScale n.val.val = s := by
    funext k
    fin_cases k <;>
      simp only [StarClosed.rowScale,hw,Star65.firstRows,
        star_vec6_three,star_vec6_four,star_vec6_five,star_vec4_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
        Matrix.head_cons,Matrix.tail_cons,mul_one,mul_neg,neg_neg]
    all_goals rfl
  change 0 < StarClosed.rowScale n.val.val j
  rw [hscale]
  exact hs j

lemma star_first_data (n : StarDomain) :
    0 < starParameter n ∧ starParameter n ≤ 1 ∧ (∀ j, 0 < starScales n j) ∧
    n.val.val.W₁ = fun j i => starScales n j * Star65.firstRows (starParameter n) j i := by
  have hn := StarClosed.labeled_closedRows n.val n.property
  have hs := star_scale_pos n
  have hv := StarClosed.branch_pos n.val.val n.val.property hn
  have hz : n.val.val.W₁ 3 0 ≠ 0 := (hs 3).ne'
  refine ⟨div_pos hv (hs 3),(div_le_one (hs 3)).mpr hn.2.2.1,hs,?_⟩
  rw [hn.2.2.2]
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp only [starParameter,starScales,StarClosed.template,Star65.firstRows,
      star_vec6_three,star_vec6_four,star_vec6_five,star_vec4_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.head_cons,Matrix.tail_cons,mul_one,mul_neg,mul_zero,neg_zero,neg_neg]
  all_goals first | rfl | skip
  all_goals simp only [StarClosed.rowScale,StarClosed.branch,
    star_vec6_three,star_vec6_four,star_vec6_five,star_vec4_three,
    Matrix.cons_val_zero, Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.head_cons,Matrix.tail_cons]
  all_goals (field_simp [hz]; ring)

noncomputable def starFirst (n : StarDomain) : ActualStarLabels.RawSlice :=
  ⟨(starParameter n,scaleFirst n.val.val (fun j => (starScales n j)⁻¹)),
    (star_first_data n).1,(star_first_data n).2.1,
    reciprocal_first_weights n.val.val (starScales n) _
      (fun j => (star_scale_pos n j).ne') (star_first_data n).2.2.2,
    fun x => (scaleFirst_eval n.val.val _
      (fun j => inv_pos.mpr (star_scale_pos n j)) x).trans (n.val.property x)⟩

private lemma continuous_star_network : Continuous (fun n : StarDomain => n.val.val) :=
  continuous_subtype_val.comp continuous_subtype_val

lemma continuous_starScales : Continuous starScales :=
  StarClosed.continuous_rowScale.comp continuous_star_network

lemma continuous_starParameter : Continuous starParameter := by
  apply (StarClosed.continuous_branch.comp continuous_star_network).div
    ((continuous_apply 3).comp (StarClosed.continuous_rowScale.comp continuous_star_network))
  intro n
  exact (star_scale_pos n 3).ne'

lemma continuous_starFirst : Continuous starFirst := by
  have hi : Continuous (fun n : StarDomain => fun j => (starScales n j)⁻¹) := by
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp continuous_starScales).inv₀
      (fun n => (star_scale_pos n j).ne')
  have hn := continuous_variable_scaleFirst (fun n : StarDomain => n.val.val)
    (fun n j => (starScales n j)⁻¹) continuous_star_network hi
    (fun n j => inv_ne_zero (star_scale_pos n j).ne')
  exact (continuous_starParameter.prod_mk hn).subtype_mk _

noncomputable def starFirstExact (n : StarDomain) : ExactFiber 4 6 5 :=
  ⟨(starFirst n).val.2,(starFirst n).property.2.2.2⟩

lemma continuous_starFirstExact : Continuous starFirstExact :=
  (continuous_snd.comp (continuous_subtype_val.comp continuous_starFirst)).subtype_mk _

lemma starFirst_sameQuotient (n : StarDomain) :
    quotientMk (starFirstExact n) = quotientMk n.val := by
  exact (quotientMk_eq_of_step (SymmetryStep.first n.val
    (fun j => (starScales n j)⁻¹) (fun j => inv_pos.mpr (star_scale_pos n j)))).symm

end MaxCaterpillar.Fiber.Count65.SectorQuotient
