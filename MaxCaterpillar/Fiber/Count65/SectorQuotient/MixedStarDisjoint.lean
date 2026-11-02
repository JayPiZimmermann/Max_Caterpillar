import MaxCaterpillar.Fiber.Count65.SectorQuotient.RootGraphs
import MaxCaterpillar.Fiber.Count65.MatrixForms
import MaxCaterpillar.Fiber.Mixed65.SectorNormalForm

/-! The actual mixed and star first-matrix sectors are disjoint before any
suffix classification. The statement allows every bias and output weight. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.Fiber.Count65.SectorQuotient

private lemma vec6_three {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) (3 : Fin 6)=d := rfl

lemma mixed_moving_row_not_star_ray (t u s : ℝ) (ht : 0<t) (hu : 0<u)
    (hs : 0<s) (k : Fin 6)
    (h : ∀ i,Mixed65.firstRows t 3 i=s*Star65.firstRows u k i) : False := by
  have h0 := h 0
  have h2 := h 2
  have hsu := mul_pos hs hu
  fin_cases k <;>
    simp only [Mixed65.firstRows,Star65.firstRows,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,vec6_three,
      mul_zero,mul_one,mul_neg,zero_mul,neg_zero] at h0 h2 <;>
    nlinarith only [ht,hsu,h0,h2]

theorem mixed_star_frames_not_relabel (t u : ℝ) (ht : 0<t) (hu : 0<u) (hu1 : u≤1)
    (s : Fin 6 → ℝ) (hs : ∀ j,0<s j)
    (p : Equiv.Perm (Fin 6)) (q : Equiv.Perm (Fin 4))
    (h : ∀ j i,Mixed65.firstRows t j i=s j*Star65.firstRows u (p j) (q i)) : False := by
  have hq := (mixed_star_input_perm_trivial t u ht hu hu1 p q s hs h).2
  subst q
  exact mixed_moving_row_not_star_ray t u (s 3) ht hu (hs 3) (p 3) (h 3)

/-- No physical first matrix has both complete normal forms. -/
theorem not_star_of_mixedFirstMatrixForm (net : Network 4 6 5)
    (hm : Mixed65.FirstMatrixForm net) : ¬StarFirstMatrixForm net := by
  intro hs
  obtain ⟨t,ht,a,ha,p,q,hm⟩ := hm
  obtain ⟨u,hu,hu1,b,hb,p',q',hs⟩ := hs
  apply mixed_star_frames_not_relabel t u ht hu hu1
    (fun j => b (p.symm j)/a (p.symm j))
    (fun j => div_pos (hb (p.symm j)) (ha (p.symm j)))
    (p.symm.trans p') (q.symm.trans q')
  intro j i
  have he := (hm (p.symm j) (q.symm i)).symm.trans (hs (p.symm j) (q.symm i))
  simp only [Equiv.apply_symm_apply] at he
  simp only [Equiv.trans_apply]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ha (p.symm j)).ne').mpr
  nlinarith only [he]

#print axioms not_star_of_mixedFirstMatrixForm
end MaxCaterpillar.Fiber.Count65.SectorQuotient
