import MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment.Prefix

set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
open BigOperators
variable {N m k l : ℕ}

theorem prefixSlots_suffix_not_mem {m r : ℕ} (j : Fin r) :
    Fin.natAdd m j∉prefixSlots m r := by
  intro h
  obtain ⟨i,hi⟩ := prefixSlots_onto _ h
  have hv := congrArg Fin.val hi
  change i.val=m+j.val at hv
  have hil := i.isLt
  linarith only [hil,hv]

theorem selected_prefix_iff (S : Finset (Fin k)) (i : Fin (S.card+(k-S.card))) :
    i∈prefixSlots S.card (k-S.card) ↔ selectedSecondEquiv S i∈S := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · exact iff_of_true (prefixSlots_mem j) (selectedSecondEquiv_prefix_mem S j)
  · exact iff_of_false (prefixSlots_suffix_not_mem j) (selectedSecondEquiv_suffix_not_mem S j)

theorem sum_selected_prefix (S : Finset (Fin k)) (f : Fin k → ℝ) :
    (∑ j : Fin S.card,f (selectedSecondEquiv S (Fin.castAdd (k-S.card) j)))=
      ∑ i in S,f i := by
  classical
  let g := fun j : Fin S.card=>selectedSecondEquiv S (Fin.castAdd (k-S.card) j)
  have hg : Finset.univ.image g=S := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j,_hj,rfl⟩
      exact selectedSecondEquiv_prefix_mem S j
    · intro hi
      obtain ⟨j,hj⟩ := selectedSecondEquiv_prefix_onto S i hi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
  have hinj : ∀ x∈(Finset.univ : Finset (Fin S.card)),∀ y∈Finset.univ,g x=g y → x=y := by
    intro x _hx y _hy hxy
    apply Fin.ext
    exact congrArg (fun z : Fin (S.card+(k-S.card))=>z.val)
      ((selectedSecondEquiv S).injective hxy)
  have hsum := Finset.sum_image (f:=f) hinj
  rw [hg] at hsum
  exact hsum.symm

theorem reindex_signedNet_mapBack (a : Network N m k) (e : Fin l≃Fin k)
    (S : Finset (Fin k)) (T : Finset (Fin l)) (hT : ∀ i,i∈T ↔ e i∈S)
    (p n : Fin l) (L : Fin m → ℝ) (η : ℝ) :
    reindexSecond (signedNet (reindexSecond a e) T p n L η) e.symm=
      signedNet a S (e p) (e n) L η := by
  apply physical_ext
  · rfl
  · rfl
  · funext i
    have hp : e.symm i=p ↔ i=e p := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hn : e.symm i=n ↔ i=e n := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hm : e.symm i∈T ↔ i∈S := by simpa only [Equiv.apply_symm_apply] using hT (e.symm i)
    simp only [reindexSecond,signedNet,QuadrantGroups.signedChordRows,hp,hn,hm,Equiv.apply_symm_apply]
  · funext i
    have hp : e.symm i=p ↔ i=e p := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hn : e.symm i=n ↔ i=e n := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hm : e.symm i∈T ↔ i∈S := by simpa only [Equiv.apply_symm_apply] using hT (e.symm i)
    simp only [reindexSecond,signedNet,QuadrantGroups.signedChordBiases,hp,hn,hm,Equiv.apply_symm_apply]
  · funext i
    have hp : e.symm i=p ↔ i=e p := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hn : e.symm i=n ↔ i=e n := by
      constructor
      · intro h; simpa only [Equiv.apply_symm_apply] using congrArg e h
      · intro h; rw [h,Equiv.symm_apply_apply]
    have hm : e.symm i∈T ↔ i∈S := by simpa only [Equiv.apply_symm_apply] using hT (e.symm i)
    simp only [reindexSecond,signedNet,readout,hp,hn,hm,Equiv.apply_symm_apply]
  · rfl

end MaxCaterpillar.Fiber.Count65.Paired.BaselineAttachment
